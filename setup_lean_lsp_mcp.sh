#!/usr/bin/env bash
# Install and register the lean-lsp-mcp server (https://github.com/oOo0oOo/lean-lsp-mcp)
# so Claude Code can query this repository's Lean proof state directly: goals at a
# `sorry`, diagnostics, hover types, mathlib search, and tactic trial runs.
#
# This complements setup_lean.sh, which installs the toolchain itself. Run that first.
#
# The MCP server is registered against an absolute --lean-project-path pointing at this
# repository, so it resolves DRSB regardless of where Claude Code is launched from.

set -Eeuo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export ELAN_HOME
export PATH="$ELAN_HOME/bin:$HOME/.local/bin:$PATH"

SERVER_NAME="${SERVER_NAME:-lean-lsp}"
SCOPE="local"
DO_REGISTER=1
DO_SMOKE_TEST=1
CLAUDE_DIRS=()

log() {
    printf '[setup_lean_lsp_mcp] %s\n' "$*"
}

warn() {
    printf '[setup_lean_lsp_mcp] warning: %s\n' "$*" >&2
}

fail() {
    printf '[setup_lean_lsp_mcp] error: %s\n' "$*" >&2
    exit 1
}

usage() {
    cat <<'EOF'
Usage: ./setup_lean_lsp_mcp.sh [options]

Options:
  --claude-dir DIR   Directory you launch Claude Code from. Repeatable.
                     `local` scope is keyed to this directory, so the server is only
                     visible in sessions started there. Defaults to this repo root.
  --scope SCOPE      local (default), project, or user.
                       local   - private to you, per --claude-dir, not committed
                       project - writes .mcp.json in --claude-dir, shared via git
                       user    - visible in every project on this machine
  --no-register      Install/verify prerequisites only; do not touch Claude config.
  --no-smoke-test    Skip the stdio handshake check.
  -h, --help         Show this help.

Examples:
  ./setup_lean_lsp_mcp.sh
  ./setup_lean_lsp_mcp.sh --claude-dir ../..          # superproject checkout
  ./setup_lean_lsp_mcp.sh --scope user
EOF
}

parse_args() {
    while [ $# -gt 0 ]; do
        case "$1" in
            --claude-dir)
                [ $# -ge 2 ] || fail "--claude-dir requires a directory argument"
                CLAUDE_DIRS+=("$2")
                shift 2
                ;;
            --scope)
                [ $# -ge 2 ] || fail "--scope requires an argument"
                SCOPE="$2"
                shift 2
                ;;
            --no-register)   DO_REGISTER=0; shift ;;
            --no-smoke-test) DO_SMOKE_TEST=0; shift ;;
            -h|--help)       usage; exit 0 ;;
            *)               fail "unknown argument: $1 (try --help)" ;;
        esac
    done

    case "$SCOPE" in
        local|project|user) ;;
        *) fail "invalid --scope '$SCOPE' (expected local, project, or user)" ;;
    esac

    if [ "${#CLAUDE_DIRS[@]}" -eq 0 ]; then
        CLAUDE_DIRS=("$REPO_ROOT")
    fi

    # Resolve to absolute paths up front: the launch directory is what `local` scope is
    # keyed on, so it must be reported accurately even when --no-register skips the
    # code path that would otherwise resolve it.
    local i dir
    for i in "${!CLAUDE_DIRS[@]}"; do
        dir="${CLAUDE_DIRS[$i]}"
        [ -d "$dir" ] || fail "--claude-dir does not exist: $dir"
        CLAUDE_DIRS[$i]="$(cd "$dir" && pwd)"
    done
}

install_uv_if_needed() {
    if command -v uvx >/dev/null 2>&1; then
        log "uv is already installed: $(command -v uvx)"
        return
    fi

    log "installing uv into $HOME/.local/bin"
    if command -v curl >/dev/null 2>&1; then
        curl -LsSf https://astral.sh/uv/install.sh | sh
    elif command -v wget >/dev/null 2>&1; then
        wget -qO- https://astral.sh/uv/install.sh | sh
    else
        fail "curl or wget is required to install uv"
    fi

    export PATH="$HOME/.local/bin:$PATH"
    command -v uvx >/dev/null 2>&1 || fail "uv install completed, but uvx is not on PATH"
}

verify_lean_tools() {
    command -v lake >/dev/null 2>&1 || fail "lake not found on PATH. Run ./setup_lean.sh first."
    command -v lean >/dev/null 2>&1 || fail "lean not found on PATH. Run ./setup_lean.sh first."
    log "lake: $(lake --version | head -1)"
}

check_ripgrep() {
    if command -v rg >/dev/null 2>&1; then
        log "ripgrep found; lean_local_search will be available"
    else
        warn "ripgrep (rg) not found. The lean_local_search tool will be degraded or unavailable."
    fi
}

# The server elaborates files on demand. Without prebuilt .olean artifacts the very first
# tool call has to compile Mathlib and will time out, which reads as a broken server.
check_build_artifacts() {
    if [ -d "$REPO_ROOT/.lake/build/lib" ]; then
        log "build artifacts present under .lake/build/lib"
        return
    fi

    warn "no .lake/build artifacts found. The first MCP tool call will time out while Lean"
    warn "compiles dependencies. Run 'lake build' in $REPO_ROOT before using the server."
}

# Populate the uv tool cache now, so the first tool call inside Claude Code is not
# competing with a package download against the MCP startup timeout.
prefetch_server() {
    log "prefetching lean-lsp-mcp via uvx"
    local version
    version="$(uvx lean-lsp-mcp --version 2>&1 | tail -1)" || fail "failed to run 'uvx lean-lsp-mcp'"
    log "server package: $version"
}

register_one() {
    # Already validated and made absolute by parse_args.
    local claude_dir="$1"

    log "registering '$SERVER_NAME' (scope=$SCOPE) for sessions launched from $claude_dir"

    # Re-registering is an error if the name is taken, so drop any prior entry first.
    # A missing entry is the normal case, hence the tolerated failure.
    ( cd "$claude_dir" && claude mcp remove "$SERVER_NAME" -s "$SCOPE" >/dev/null 2>&1 ) || true

    (
        cd "$claude_dir" &&
        claude mcp add "$SERVER_NAME" -s "$SCOPE" -- \
            uvx lean-lsp-mcp --lean-project-path "$REPO_ROOT"
    ) || fail "claude mcp add failed for $claude_dir"
}

register_server() {
    if [ "$DO_REGISTER" -eq 0 ]; then
        log "skipping registration (--no-register)"
        return
    fi

    if ! command -v claude >/dev/null 2>&1; then
        warn "the 'claude' CLI is not on PATH; skipping automatic registration."
        warn "Add this to your MCP config by hand:"
        cat >&2 <<EOF

  "mcpServers": {
    "$SERVER_NAME": {
      "command": "uvx",
      "args": ["lean-lsp-mcp", "--lean-project-path", "$REPO_ROOT"]
    }
  }

EOF
        return
    fi

    local dir
    for dir in "${CLAUDE_DIRS[@]}"; do
        register_one "$dir"
    done
}

# Drive the server over stdio and confirm it completes an MCP handshake and advertises
# tools. stdin is held open until the reply arrives; closing it early shuts the server
# down mid-request, which looks like a hang.
smoke_test() {
    if [ "$DO_SMOKE_TEST" -eq 0 ]; then
        log "skipping smoke test (--no-smoke-test)"
        return
    fi

    log "smoke test: MCP handshake + tools/list"

    LEAN_PROJECT_PATH="$REPO_ROOT" python3 - "$REPO_ROOT" <<'PY' || fail "smoke test failed"
import json, os, subprocess, sys

repo_root = sys.argv[1]
proc = subprocess.Popen(
    ["uvx", "lean-lsp-mcp", "--lean-project-path", repo_root],
    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
    text=True, bufsize=1,
)

def send(msg):
    proc.stdin.write(json.dumps(msg) + "\n")
    proc.stdin.flush()

try:
    send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "protocolVersion": "2024-11-05", "capabilities": {},
        "clientInfo": {"name": "setup_lean_lsp_mcp", "version": "1"}}})
    send({"jsonrpc": "2.0", "method": "notifications/initialized"})
    send({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})

    tools = None
    for line in proc.stdout:
        line = line.strip()
        if not line:
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            continue
        if msg.get("id") == 1 and "result" in msg:
            info = msg["result"].get("serverInfo", {})
            print(f"[setup_lean_lsp_mcp] connected to {info.get('name')} {info.get('version')}")
        if msg.get("id") == 2:
            tools = msg.get("result", {}).get("tools")
            break
finally:
    proc.terminate()
    try:
        proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        proc.kill()

if not tools:
    print("[setup_lean_lsp_mcp] error: server advertised no tools", file=sys.stderr)
    sys.exit(1)

names = sorted(t["name"] for t in tools)
print(f"[setup_lean_lsp_mcp] server advertises {len(names)} tools")
print("[setup_lean_lsp_mcp]   " + ", ".join(names[:6]) + ", ...")
for required in ("lean_goal", "lean_diagnostic_messages"):
    if required not in names:
        print(f"[setup_lean_lsp_mcp] error: missing tool {required}", file=sys.stderr)
        sys.exit(1)
PY
}

print_next_steps() {
    cat <<EOF

================================================================================
[setup_lean_lsp_mcp] MANUAL STEPS REQUIRED — the setup is not usable yet
================================================================================

Everything above is done. The following steps cannot be automated, because a
Claude Code session connects to its MCP servers once, at startup. The session you
ran this script from will never see '$SERVER_NAME', no matter what the config says.

  STEP 1 (required) — Start a NEW Claude Code session.

      Terminal CLI:      exit and run 'claude' again.
      VS Code extension: open a new Claude Code chat/session. A full restart of
                         VS Code is normally NOT needed. If the server still does
                         not appear, reload the window:
                           Ctrl/Cmd+Shift+P -> "Developer: Reload Window"

  STEP 2 (required) — Verify the server is connected.

      Run:   claude mcp list
      Want:  $SERVER_NAME: uvx lean-lsp-mcp ... - OK Connected

      If it is missing, you are launching Claude from a directory this script did
      not register. '$SCOPE' scope is keyed to the launch directory. Re-run with:
          ./setup_lean_lsp_mcp.sh --claude-dir /path/you/launch/claude
      or register everywhere at once:
          ./setup_lean_lsp_mcp.sh --scope user

  STEP 3 (recommended) — Confirm Lean itself responds, not just the server.

      'OK Connected' only means the process started. It does NOT mean Lean
      resolved this project. In the new session, ask Claude for the proof goal at
      a known sorry:

          "use lean_goal on ForMathlib/Analysis/ExpLogBounds.lean line 38"

      Expect a proof state. The FIRST call against a Mathlib-heavy file must
      elaborate it and can take several minutes. A reply with partial: true, or
      goal status 'still_elaborating', means Lean is still working: poll again.
      That is not an error and the server is not dead.

--------------------------------------------------------------------------------
Registered for sessions launched from:
$(printf '    %s\n' "${CLAUDE_DIRS[@]}")
Lean project resolved by the server (absolute, independent of launch dir):
    $REPO_ROOT
--------------------------------------------------------------------------------

Useful tools for this repo's remaining proof debt:
    lean_goal                 goal state at a sorry, e.g. ForMathlib/Analysis/ExpLogBounds.lean
    lean_diagnostic_messages  errors and warnings for a file
    lean_multi_attempt        try candidate tactics without editing the file
    lean_verify               axiom check for a theorem (catches sorryAx)
    lean_local_search         find an existing declaration before inventing a lemma name

EOF
}

main() {
    parse_args "$@"
    install_uv_if_needed
    verify_lean_tools
    check_ripgrep
    check_build_artifacts
    prefetch_server
    register_server
    smoke_test
    print_next_steps
    log "done"
}

main "$@"

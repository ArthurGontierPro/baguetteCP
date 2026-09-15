#!/usr/bin/env bash
# One-time setup of the OCaml toolchain for baguette.
# Safe to re-run: every step checks before acting.
set -euo pipefail

SWITCH_NAME="baguette"
OCAML_VERSION="5.1.1"

say() { printf '\033[1m==>\033[0m %s\n' "$*"; }

export PATH="${HOME}/.local/bin:${PATH}"

if ! command -v opam >/dev/null 2>&1; then
  say "opam not found — installing the release binary to ~/.local/bin"
  mkdir -p "${HOME}/.local/bin"
  VER="$(curl -fsSL -o /dev/null -w '%{url_effective}' \
        https://github.com/ocaml/opam/releases/latest | sed 's|.*/tag/||')"
  curl -fsSL -o "${HOME}/.local/bin/opam" \
    "https://github.com/ocaml/opam/releases/download/${VER}/opam-${VER}-x86_64-linux"
  chmod +x "${HOME}/.local/bin/opam"
  say "installed opam ${VER}"
else
  say "opam present: $(opam --version)"
fi

if [ ! -d "${HOME}/.opam" ]; then
  say "initialising opam (this takes a few minutes)"
  opam init --bare --disable-sandboxing --no-setup -y
fi

eval "$(opam env 2>/dev/null || true)"

if ! opam switch list --short | grep -qx "${SWITCH_NAME}"; then
  say "creating switch ${SWITCH_NAME} on OCaml ${OCAML_VERSION}"
  opam switch create "${SWITCH_NAME}" "ocaml-base-compiler.${OCAML_VERSION}" -y -j "$(nproc)"
fi

opam switch set "${SWITCH_NAME}"
eval "$(opam env --switch=${SWITCH_NAME})"

say "installing build and dev dependencies"
opam install -y dune menhir ocamlformat.0.26.1 ocaml-lsp-server

say "checking veripb"
# scripts/checker.sh is the single source of truth for which checker this project
# uses and in what order it looks; do not re-implement the search here.
# shellcheck source=checker.sh
. "$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/checker.sh"
if baguette_resolve_veripb; then
  say "veripb present at ${VERIPB}"
  "${VERIPB}" --version 2>&1 | grep -i version | head -1 | sed 's/^/  /'
else
  echo "WARNING: no veripb found. The proof tests will FAIL (they do not skip)." >&2
  baguette_veripb_diagnostic
fi

cat <<'MSG'

Done. Add this to your shell profile if it is not there already:

    eval "$(opam env)"

Then:

    make build
    make test
MSG

# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# Sourced by scripts/build.sh and repro.sh: prepares the flake-only directory
# and sets nix_shell, the command prefix that runs a command in the pinned
# development shell.
#
# Nix copies a path flake's whole directory, build outputs included, into
# /nix/store on every call, so the shell never comes from this tree. The
# flake files are copied into FLAKE_DIR (default
# ${XDG_CACHE_HOME:-~/.cache}/gordiehowe/flake), and the shell runs as
# `nix develop FLAKE_DIR --profile FLAKE_DIR/dev-profile`; the profile keeps
# the shell's closure from garbage collection. FLAKE_DIR may hold only the
# flake files and the profile links, and an existing FLAKE_DIR whose flake
# files differ from this tree's is refused, so a shared flake directory is
# never overwritten.
#
#   gh_prepare_flake REPO_DIR    sets flake_dir and nix_shell, or exits

gh_prepare_flake() {
  local repo="$1" f
  flake_dir="${FLAKE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/gordiehowe/flake}"
  mkdir -p "$flake_dir"
  flake_dir="$(cd -- "$flake_dir" && pwd -P)"
  case "$flake_dir/" in
    "$(cd -- "$repo" && pwd -P)/"*)
      echo "FLAKE_DIR $flake_dir is inside the source tree" >&2; exit 2 ;;
  esac
  for f in "$flake_dir"/* "$flake_dir"/.[!.]*; do
    [[ -e "$f" || -L "$f" ]] || continue
    case "$(basename -- "$f")" in
      flake.nix|flake.lock|dev-profile|dev-profile-*-link) ;;
      *) echo "FLAKE_DIR $flake_dir holds $(basename -- "$f"); it must hold only the flake" >&2
         exit 2 ;;
    esac
  done
  for f in flake.nix flake.lock; do
    if [[ -e "$flake_dir/$f" ]]; then
      if ! cmp -s "$repo/$f" "$flake_dir/$f"; then
        echo "$flake_dir/$f differs from $repo/$f; use another FLAKE_DIR" >&2
        exit 2
      fi
    else
      cp -- "$repo/$f" "$flake_dir/$f"
    fi
  done
  # The flake's shell hook sets CC, CXX and NIX_ENFORCE_NO_NATIVE=0 (without
  # the latter the cc-wrapper drops -march=native silently).
  nix_shell=(nix --extra-experimental-features "nix-command flakes"
    develop "$flake_dir" --profile "$flake_dir/dev-profile" -c)
}

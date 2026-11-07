#!/bin/sh
# Collect provenance before building a final compiler program.
set -eu
if [ "$#" -gt 1 ]; then
  echo "usage: $0 [HOLDIR]" >&2
  exit 1
fi
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cakeml_dir=$(CDPATH= cd -- "$script_dir/../../.." && pwd)
if [ "$#" -eq 1 ]; then
  hol_dir=$1
else
  context=$(holbuild --source-dir "$cakeml_dir" context)
  hol_dir=$(printf '%s\n' "$context" | sed -n 's/^package-source-root: hol //p')
  if [ -z "$hol_dir" ]; then
    echo "holbuild context did not report a HOL source root" >&2
    exit 1
  fi
fi
out="$script_dir/compiler_build_info.txt"
tmp=$(mktemp "$out.XXXXXX")
trap 'rm -f "$tmp"' EXIT HUP INT TERM
revision () {
  if commit=$(git -C "$2" rev-parse --verify HEAD 2>/dev/null); then
    diff=$(git -C "$2" diff --no-ext-diff --no-textconv --binary HEAD --)
    if [ -n "$diff" ]; then
      fingerprint=$(printf '%s\n' "$diff" | git hash-object --stdin)
      commit="$commit-dirty:$fingerprint"
    fi
    printf '%s %s\n' "$1" "$commit"
  else
    printf '%s unknown\n' "$1"
  fi
}
poly_version=$("${HOLBUILD_POLY:-poly}" -v)
identity=$(
  revision 'CakeML:' "$cakeml_dir"
  revision 'HOL4:  ' "$hol_dir"
  printf 'PolyML: %s\n' "$poly_version"
)
# Retain the producer's timestamp only while its source/tool identities match.
if [ -f "$out" ] && [ "$(tail -n +6 "$out")" = "$identity" ]; then
  case "$identity" in
    *unknown*) ;;
    *) exit 0 ;;
  esac
fi
{
  printf 'The CakeML compiler\n\nVersion details:\n'
  LC_ALL=C date -u '+%a %b %e %T %Y UTC'
  printf '\n%s\n' "$identity"
} > "$tmp"
if ! cmp -s "$tmp" "$out"; then mv "$tmp" "$out"; fi

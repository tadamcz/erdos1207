#!/usr/bin/env bash
set -euo pipefail

# Runs the checks this repository performs in place of Comparator, which cannot be built against
# the pinned Lean v4.27.0 (see the README section "Toolchain and verification").
#
#   1. Builds Audit.lean, which checks -- on the solution side -- that the proved theorem has the
#      intended statement, is a theorem, and depends on no axioms beyond propext, Quot.sound and
#      Classical.choice. Those checks are elaboration errors, so building them is running them.
#   2. Compares the two environments: Challenge.lean and the proof module declare
#      Erdos1207.erdos_1207 separately and are never imported together, so this prints the fully
#      explicit type of that constant from each environment and requires the two to be identical.
#      This is the statement comparison Comparator would otherwise perform.

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

lake build Challenge Solution Audit

work_dir=$(mktemp -d)
trap 'rm -rf "$work_dir"' EXIT

# `pp.all` prints universes, implicit arguments and instances explicitly, and `pp.fullNames` prints
# every constant fully qualified, so the printed type is insensitive to notation and to what each
# environment happens to have opened.
emit_type() {
  local module=$1 destination=$2
  cat >"$work_dir/Emit.lean" <<LEAN
import $module
open Lean Meta in
#eval show MetaM Unit from do
  let some ci := (← getEnv).find? \`Erdos1207.erdos_1207
    | throwError "Erdos1207.erdos_1207 is not in the $module environment"
  withOptions (fun o => ((o.setBool \`pp.all true).setBool \`pp.fullNames true)) do
    IO.println (toString (← ppExpr ci.type))
LEAN
  lake env lean "$work_dir/Emit.lean" >"$destination"
}

emit_type Challenge "$work_dir/challenge.txt"
emit_type Solution "$work_dir/solution.txt"

if ! diff -u --label "type in the Challenge environment" "$work_dir/challenge.txt" \
                --label "type in the Solution environment" "$work_dir/solution.txt"; then
  echo "audit: FAILED -- the challenge statement and the proved theorem have different types" >&2
  exit 1
fi

echo "audit: the challenge statement and the proved theorem have the same type:"
cat "$work_dir/challenge.txt"

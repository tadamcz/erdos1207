import Solution

/-!
# Audit (solution side)

Part of the checking that the Palomar template delegates to
[Comparator](https://github.com/leanprover/comparator), which cannot be built against this
repository's toolchain; see the README section "Toolchain and verification". `scripts/audit.sh`
builds this module and then performs the cross-environment comparison that this module cannot.

`Challenge.lean` and the proof module each declare `Erdos1207.erdos_1207`, along with their own
copies of the statement's definitions, in *separate* environments; that is what lets a reader audit
the small file while the proof lives in the large one, and it is why the two are never imported
together. This module therefore imports only `Solution`, and checks, of the theorem that is
actually proved:

1. **The statement is the intended one.** The `example` re-types the conjecture verbatim from the
   benchmark statement file and checks that the proved theorem inhabits it.
2. **No `sorry`, and only the permitted axioms:** `propext`, `Quot.sound` and `Classical.choice`.
   A `sorry` anywhere in the proof's dependencies would show up here as `sorryAx`.
3. **It is a theorem**, not an axiom or an opaque constant.

Each failure is an elaboration error, so a successful build is a passing audit. The remaining
check, that this statement coincides with the one in `Challenge.lean`, is done by
`scripts/audit.sh`, which prints the fully explicit type of `Erdos1207.erdos_1207` from each of the
two environments and requires them to be identical.
-/

open Filter

-- (1) The exact statement, retyped verbatim from the benchmark statement file.
example : (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (Erdos1207.P 2 n : ℝ) < (n : ℝ) ^ (1 - c)) :=
  Erdos1207.erdos_1207

-- (2) and (3).
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let target := `Erdos1207.erdos_1207
  let some ci := env.find? target | throwError "{target} is not in the environment"
  unless ci matches .thmInfo _ do throwError "{target} is not a theorem"
  unless ci.levelParams.isEmpty do
    throwError "{target} unexpectedly has universe parameters: {ci.levelParams}"
  let (_, s) := ((CollectAxioms.collect target).run env).run {}
  let permitted : List Name := [`propext, `Quot.sound, `Classical.choice]
  for a in s.axioms.toList do
    unless permitted.contains a do
      throwError "{target} depends on the unpermitted axiom {a}"
  IO.println s!"audit: {target} is a theorem depending only on {s.axioms.toList}"

#print axioms Erdos1207.erdos_1207

import Mathlib

/-!
# Erdős problem #1207 (isosceles-free subsets of planar point sets): proof

*Reference:* [erdosproblems.com/1207](https://www.erdosproblems.com/1207)

For a set of `n` points in `ℝ^d`, consider its largest subset containing no isosceles triangle
(no three distinct points with two equal distances among them; degenerate, collinear triangles
count). Let `P_d(n)` be the smallest such maximum over all `n`-point sets, so that every `n`
points in `ℝ^d` contain `P_d(n)` points with no isosceles triangle. Erdős [Er80, p. 110]
attributes the problem to Riddell and asks for estimates of `P_d(n)`; in particular, is it true
that `P_2(n) < n^{1-c}` for some constant `c > 0`? Taking a subset with all distances distinct
gives `P_d(n) ≥ n^{1/(3d-3) - o(1)}`, and Pach and Tardos [PaTa02] give `P_2(n) ≫ n^{0.432}`.
The case `d = 1` is the problem of large subsets without three-term arithmetic progressions, and
the vertices of a regular polygon show `P_2(n) ≪ r_3(n) = n^{1-o(1)}`, which is not a power
saving.

The answer is **yes**: there is `c > 0` such that `P_2(n) < n^{1-c}` for all sufficiently large
`n`. Formally, the theorem proved is `Erdos1207.erdos_1207`, the statement of the FrontierMath
Erdős benchmark: `∃ c > 0, ∀ᶠ n in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)`, where `P d n` is the
infimum over `n`-point finsets `S` of `EuclideanSpace ℝ (Fin d)` of the supremum of the
cardinalities of isosceles-free subsets of `S`. (In the literature, the same statement was
established in July 2026 by Lee, Pohoata and Zhu, arXiv:2607.05374, by a different route; see
the README.)

This file is the small statement surface a reader should audit: the theorem
`Erdos1207.erdos_1207` below is the compared declaration, and the conjecture is proved in
`Solution.lean` and the module it imports. Only the theorem's `sorry` is filled in there.

The definitions `IsIsoscelesFree` and `P` and the statement inside this file are copied verbatim
from the FrontierMath Erdős benchmark file
`apn/data/erdos_autoformalized/Isolated/Erdos1207.erdos_1207.lean` in [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) at commit
`8fa3b4c6ee5e6f0ee25d027b6f110f20787db977` (formalized by the benchmark authors' autoformalization pipeline; the problem had
no statement in Formal Conjectures). It is exactly the statement the AI system was given. That
file imported `FormalConjecturesUtil`, and its two auxiliary notions `Set.Triplewise` and
`IsIsosceles` are not in Mathlib: they are copied verbatim below from
`FormalConjecturesForMathlib/Data/Set/Triplewise.lean` and
`FormalConjecturesForMathlib/Geometry/2d.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind,
Apache-2.0) at commit `9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`, the pin the benchmark used.
-/
open Filter

namespace Set

variable {α : Type*}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

namespace Erdos1207

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z => ¬ IsIsosceles x y z

/--
`P d n` is the largest number such that every set of `n` points in Euclidean `d`-space has an
isosceles-free subset of at least that size.
-/
noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)),
      A ⊆ S ∧ IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}}

/--
**Erdős problem #1207.** Let $P_d(n)$ be such that in any set of $n$ points in $\mathbb{R}^d$
there exist at least $P_d(n)$ many points which do not contain an isosceles triangle. Estimate
$P_d(n)$ - in particular, is it true that $P_2(n)<n^{1-c}$ for some constant $c>0$? This is the
statement of the FrontierMath Erdős benchmark: the answer is yes, there is $c>0$ with
$P_2(n)<n^{1-c}$ for all sufficiently large $n$.
-/
theorem erdos_1207 :
    (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)) := by
  sorry

end Erdos1207

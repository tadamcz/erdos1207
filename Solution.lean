import Mathlib

/-!
# Erdős Problem 1207

*Reference:* [erdosproblems.com/1207](https://www.erdosproblems.com/1207)
-/

open Filter

/-! ### Definitions from Formal Conjectures

The benchmark statement reached the model through `import FormalConjecturesUtil`. Six of the
declarations it provides are not in Mathlib; they are copied verbatim here so that this module
imports only Mathlib. All six are from Google DeepMind's Formal Conjectures (Apache-2.0) at commit
`9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`: `Data/Set/Triplewise.lean`, `Geometry/2d.lean`,
`Data/Nat/Squarefree.lean`, `Algebra/QuadraticAlgebra/Basic.lean` and
`NumberTheory/NumberField/Quadratic.lean`. The first two are used by the conjecture statement
itself; the last four are used inside the proof. -/

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

namespace Nat

theorem Prime.squarefree {p : ℕ} (hp : p.Prime) : Squarefree p := Irreducible.squarefree hp

end Nat

namespace QuadraticAlgebra

variable {K : Type*} [Field K] {a b : K} [Fact (∀ r, r ^ 2 ≠ a + b * r)]

attribute [-instance] instField

@[simps] instance : NNRatCast (QuadraticAlgebra K a b) where nnratCast q := ⟨q, 0⟩
@[simps] instance : RatCast (QuadraticAlgebra K a b) where ratCast q := ⟨q, 0⟩

/-- If `K` is a field and there is no `r : K` such that `r ^ 2 = a + b * r`,
then `QuadraticAlgebra K a b` is a field. -/
instance instField' : Field (QuadraticAlgebra K a b) where
  inv z := (norm z)⁻¹ • star z
  mul_inv_cancel z hz := by
    rw [ne_eq, ← norm_eq_zero_iff_eq_zero] at hz
    simp only [Algebra.mul_smul_comm]
    rw [← C_mul_eq_smul, C_eq_algebraMap, ← algebraMap_norm_eq_mul_star, ← map_mul,
      inv_mul_cancel₀ hz, map_one]
  inv_zero := by simp
  nnratCast_def q :=
    show _ = _ * (norm (_ : QuadraticAlgebra K a b))⁻¹ • star (_ : QuadraticAlgebra K a b) by
      ext <;> simp [sq]; field_simp; simp [NNRat.cast_def]
  ratCast_def q :=
    show _ = _ * (norm (_ : QuadraticAlgebra K a b))⁻¹ • star (_ : QuadraticAlgebra K a b) by
      ext <;> simp [sq]; field_simp; simp [Rat.cast_def]
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnqsmul_def q x := by ext <;> simp [NNRat.smul_def]
  qsmul_def q x := by ext <;> simp [Rat.smul_def]

end QuadraticAlgebra

/-- Any `QuadraticAlgebra ℚ a b` that is a field is automatically a quadratic extension
of `ℚ`, i.e., a degree-2 extension. Combined with `IsQuadraticField.instNumberField`,
this gives `NumberField (QuadraticAlgebra ℚ a b)` for free. -/
instance QuadraticAlgebra.instIsQuadraticExtension (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

/-- A quadratic field is a number field: it has characteristic zero
and is finite-dimensional over `ℚ`. -/
instance Algebra.IsQuadraticExtension.to_numberField (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where
  to_finiteDimensional := .of_finrank_pos <| by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]; norm_num

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

end Erdos1207

set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000



/-! The conjecture follows from an unbounded-degree family of totally real
number fields containing a square root of five and having bounded root
discriminant. The existence of this family is not proved here. -/


/- A conditional arithmetic criterion for the original conjecture.
The required family of number fields is NOT constructed in this file. -/





/- A quantitative bounded-overlap version of Blichfeldt's principle. -/

open MeasureTheory
open scoped ENNReal
namespace BlichfeldtCounting

/-- If all differences of translates hitting a point lie in `U`, at most
`U.card` translates can hit that point. -/
theorem overlap_le_card {G E : Type*} [AddGroup G] [AddAction G E]
    (s : Set E) (U : Finset G)
    (hU : ∀ g h : G, ∀ x : E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) (x : E) :
    (∑' g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) ≤ U.card := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro T
  have hc : (T.filter (fun g => g +ᵥ x ∈ s)).card ≤ U.card := by
    let V := T.filter (fun g => g +ᵥ x ∈ s)
    by_cases hV : V.Nonempty
    · obtain ⟨g₀,hg₀⟩ := hV
      have hg₀' := (Finset.mem_filter.mp hg₀).2
      apply Finset.card_le_card_of_injOn (fun g => g-g₀)
      · intro g hg
        exact hU g g₀ x (Finset.mem_filter.mp hg).2 hg₀'
      · intro g _ h _ heq
        exact sub_left_injective heq
    · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (Nat.zero_le _)
  have hs : (∑ g ∈ T, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) =
      ((T.filter (fun g => g +ᵥ x ∈ s)).card : ℝ≥0∞) := by
    simp only [Set.indicator_apply,Finset.sum_boole]
  rw [hs]
  exact_mod_cast hc

/-- The measure of a set is at most the number of possible translate
differences times the measure of a fundamental domain. -/
theorem measure_le_card_mul {G E : Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ : Measure E) [VAddInvariantMeasure G E μ]
    (F s : Set E) (hF : IsAddFundamentalDomain G F μ) (hs : MeasurableSet s)
    (U : Finset G)
    (hU : ∀ g h : G, ∀ x : E, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U) :
    μ s ≤ (U.card : ℝ≥0∞) * μ F := by
  have hm (g : G) : Measurable (fun x : E => s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x)) :=
    (measurable_const.indicator hs).comp (measurable_const_vadd g)
  calc
    μ s = ∫⁻ x, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      (lintegral_indicator_one hs).symm
    _ = ∑' g : G, ∫⁻ x in F, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      hF.lintegral_eq_tsum'' _
    _ = ∫⁻ x in F, ∑' g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (g +ᵥ x) ∂μ :=
      (lintegral_tsum (fun g => (hm g).aemeasurable)).symm
    _ ≤ ∫⁻ _x in F, (U.card : ℝ≥0∞) ∂μ :=
      lintegral_mono (overlap_le_card s U hU)
    _ = (U.card : ℝ≥0∞) * μ F := by simp

/-- A full lattice has at least `t^r / covolume` points in the centered
coordinate cube of radius `t`. This lower bound is uniform in the lattice. -/
theorem cube_card_lower_bound {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (U : Finset L) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) :
    t^(Fintype.card ι) ≤ (U.card : ℝ) * ZLattice.covolume L := by
  classical
  letI : MeasurableVAdd L (ι → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  let s : Set (ι → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-t/2) (t/2))
  have hs : MeasurableSet s := MeasurableSet.pi (Set.to_countable _) (by intro i _; exact measurableSet_Icc)
  have hdiff : ∀ g h : L, ∀ x : ι → ℝ, g +ᵥ x ∈ s → h +ᵥ x ∈ s → g-h ∈ U := by
    intro g h x hg hh
    apply (hU _).mpr
    intro i
    have hg' := Set.mem_pi.mp hg i (Set.mem_univ i)
    have hh' := Set.mem_pi.mp hh i (Set.mem_univ i)
    change -t/2 ≤ (g : ι → ℝ) i + x i ∧ (g : ι → ℝ) i + x i ≤ t/2 at hg'
    change -t/2 ≤ (h : ι → ℝ) i + x i ∧ (h : ι → ℝ) i + x i ≤ t/2 at hh'
    change |(g : ι → ℝ) i - (h : ι → ℝ) i| ≤ t
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hm : volume s = (ENNReal.ofReal t)^(Fintype.card ι) := by
    rw [volume_pi,Measure.pi_pi]
    simp only [Real.volume_Icc]
    have he : t/2 - -t/2 = t := by ring
    simp only [he,Finset.prod_const,Finset.card_univ]
  have hfin : volume F ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  have h := measure_le_card_mul volume F s hF hs U hdiff
  have hreal := ENNReal.toReal_mono (by finiteness : (U.card : ℝ≥0∞)*volume F ≠ ⊤) h
  rw [hm,ENNReal.toReal_pow,ENNReal.toReal_ofReal ht,ENNReal.toReal_mul,ENNReal.toReal_natCast] at hreal
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hreal

end BlichfeldtCounting


/- A finite-index residue argument bounds the doubling of a complete
logarithmic cube. It includes torsion, provided the residue hypothesis holds. -/

open scoped Pointwise
namespace LogCubeDoubling

/-- A complete bounded logarithmic cube has small doubling whenever division
by five is available within each of a bounded number of residue classes. -/
theorem sub_card_le {G ι Q : Type*} [AddCommGroup G] [DecidableEq G] [Fintype Q]
    (U : Finset G) (f : G →+ (ι → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f x i| ≤ t)
    (q : G → Q) (hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y) :
    (U-U).card ≤ Fintype.card Q * U.card := by
  classical
  let V : Finset G := U-U
  have hV : ∀ x ∈ V, ∀ i, |f x i| ≤ 2*t := by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
    calc
      |f (a-b) i| = |f a i-f b i| := by simp
      _ ≤ |f a i|+|f b i| := abs_sub _ _
      _ ≤ t+t := add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t := by ring
  have hf : ∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card := by
    intro c hc
    let T : Finset G := V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩ := Finset.mem_image.mp hc
    have hex : ∀ x ∈ T, ∃ z ∈ U, (5 : ℕ) • z = x-x₀ := by
      intro x hx
      obtain ⟨hx,hqx⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩ := hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he : 5 * f z i = f x i - f x₀ i := by
        have hh := congrArg (fun w => f w i) hz
        simpa using hh
      have hb : |f x i - f x₀ i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g : T → U := fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x : T) : (5 : ℕ) • (g x : G) = (x : G)-x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hh := congrArg (fun z : U => (5 : ℕ) • (z : G)) hxy
      dsimp only at hh
      rw [hg,hg] at hh
      exact sub_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U-U).card ≤ U.card * (V.image q).card := Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card := Nat.mul_comm _ _

/-- In free integer coordinates there are exactly `5^r` residue classes. -/
theorem int_cube_sub_card_le {ι κ : Type*} [Fintype ι]
    (U : Finset (ι → ℤ)) (f : (ι → ℤ) →+ (κ → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f x i| ≤ t) :
    (U-U).card ≤ 5^(Fintype.card ι) * U.card := by
  classical
  let q : (ι → ℤ) → (ι → ZMod 5) := fun x i => x i
  have hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y := by
    intro x y hxy
    refine ⟨fun i => (x i-y i)/5,?_⟩
    ext i
    have hdiv : (5 : ℤ) ∣ x i-y i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by
      rw [Int.cast_sub,sub_eq_zero]
      exact congrFun hxy i)
    simpa using Int.mul_ediv_cancel' hdiv
  simpa [Fintype.card_pi,ZMod.card] using sub_card_le U f t ht hU q hroot

end LogCubeDoubling


namespace LatticeCube
open scoped Pointwise

/-- The bounded logarithmic cube in a full lattice is finite. -/
theorem finite_cube {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (t : ℝ) (ht : 0 ≤ t) : {x : L | ∀ i, |(x : ι → ℝ) i| ≤ t}.Finite := by
  letI : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
  have hclosed : IsClosed (L : Set (ι → ℝ)) := by
    change IsClosed (L.toAddSubgroup : Set (ι → ℝ))
    exact AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall 0 t ∩ (L : Set (ι → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall hclosed
  apply Set.Finite.of_finite_image (f := fun x : L => (x : ι → ℝ)) _ Subtype.val_injective.injOn
  apply hfin.subset
  rintro x ⟨y,hy,rfl⟩
  refine ⟨?_,y.property⟩
  rw [mem_closedBall_zero_iff,pi_norm_le_iff_of_nonneg ht]
  simpa only [Real.norm_eq_abs] using hy

/-- A cube in a rank-`r` lattice has doubling at most `5^r`. -/
theorem sub_card_le {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (U : Finset L) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) :
    (U-U).card ≤ 5^(Fintype.card ι) * U.card := by
  classical
  let e := (IsZLattice.basis L).equivFun
  let q : L → (ι → ZMod 5) := fun x i => e x i
  have hroot : ∀ x y, q x = q y → ∃ z, (5 : ℕ) • z = x-y := by
    intro x y hxy
    refine ⟨e.symm (fun i => (e x i-e y i)/5),?_⟩
    apply e.injective
    ext i
    have hdiv : (5 : ℤ) ∣ e x i-e y i := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp (by
      rw [Int.cast_sub,sub_eq_zero]
      exact congrFun hxy i)
    simpa using Int.mul_ediv_cancel' hdiv
  simpa [Fintype.card_pi,ZMod.card] using
    LogCubeDoubling.sub_card_le U L.subtype.toAddMonoidHom t ht hU q hroot

/-- Uniform lower cardinality and doubling bounds for a lattice cube. -/
theorem exists_cube {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    [DecidableEq L] (t : ℝ) (ht : 0 ≤ t) :
    ∃ U : Finset L,
      (∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t) ∧
      t^(Fintype.card ι) ≤ (U.card : ℝ)*ZLattice.covolume L ∧
      (U-U).card ≤ 5^(Fintype.card ι)*U.card := by
  classical
  let U := (finite_cube L t ht).toFinset
  have hU : ∀ x : L, x ∈ U ↔ ∀ i, |(x : ι → ℝ) i| ≤ t := by simp [U]
  exact ⟨U,hU,BlichfeldtCounting.cube_card_lower_bound L U t ht hU,
    sub_card_le L U t ht hU⟩

end LatticeCube


/- Balancing the coordinate sum of a finite cube by a single pigeonhole
step, followed by translation. -/

namespace BalancedFiniteSets
open scoped BigOperators Pointwise

theorem linear_le_pow (r : ℕ) : 2*r+1 ≤ 3^r := by
  induction r with
  | zero => norm_num
  | succ r ih => rw [pow_succ]; nlinarith

/-- Translation of one sum bucket costs only `2r+1` points in density and
controls the omitted coordinate (the negative coordinate sum). -/
theorem exists_balanced {G ι : Type*} [AddCommGroup G] [DecidableEq G] [Fintype ι]
    (S : Finset G) (hS : S.Nonempty) (f : G →+ (ι → ℝ)) (t : ℝ) (ht : 0 < t)
    (hbound : ∀ x ∈ S, ∀ i, |f x i| ≤ t) :
    ∃ W : Finset G, W.Nonempty ∧ S.card ≤ (2*Fintype.card ι+1)*W.card ∧
      ∀ w ∈ W, (∀ i, |f w i| ≤ 2*t) ∧ |∑ i, f w i| ≤ t := by
  classical
  let r := Fintype.card ι
  let q : G → ℤ := fun x => ⌊(∑ i, f x i)/t⌋
  have hq : ∀ x ∈ S, q x ∈ Finset.Icc (-(r : ℤ)) r := by
    intro x hx
    have hs : |∑ i, f x i| ≤ (r : ℝ)*t :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa [r] using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound x hx i)))
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      have hh := (abs_le.mp hs).1
      rw [le_div_iff₀ ht]
      simpa using hh
    · apply Int.floor_le_iff.mpr
      have hh := (div_le_iff₀ ht).mpr (abs_le.mp hs).2
      exact hh.trans_lt (by simp)
  have hqcard : (S.image q).card ≤ 2*r+1 := by
    have hs : S.image q ⊆ Finset.Icc (-(r : ℤ)) r := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact hq x hx
    have hc : (Finset.Icc (-(r : ℤ)) r).card = 2*r+1 := by rw [Int.card_Icc]; omega
    exact (Finset.card_le_card hs).trans_eq hc
  obtain ⟨c,hc,hmax⟩ := (S.image q).exists_max_image
    (fun c => (S.filter (fun x => q x = c)).card) (hS.image q)
  let V := S.filter (fun x => q x = c)
  obtain ⟨v,hv,hqv⟩ := Finset.mem_image.mp hc
  have hvV : v ∈ V := Finset.mem_filter.mpr ⟨hv,hqv⟩
  let W := V.image (fun x => x-v)
  have hW : W.Nonempty := (Finset.nonempty_iff_ne_empty.mpr (by
    exact Finset.ne_empty_of_mem hvV)).image _
  have hcW : W.card = V.card := Finset.card_image_iff.mpr (by
    intro a _ b _ h
    exact sub_left_injective h)
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW]
    exact (Finset.card_le_mul_card_image S V.card hmax).trans (by nlinarith [hqcard])
  · intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hx,hqc⟩ := Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · intro i
      simp only [map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])
    · have heq : q x = q v := hqc.trans hqv.symm
      have h₁ := Int.floor_le ((∑ i, f x i)/t)
      have h₂ := Int.lt_floor_add_one ((∑ i, f x i)/t)
      have h₃ := Int.floor_le ((∑ i, f v i)/t)
      have h₄ := Int.lt_floor_add_one ((∑ i, f v i)/t)
      change (q x : ℝ) ≤ _ at h₁
      change _ < (q x : ℝ)+1 at h₂
      change (q v : ℝ) ≤ _ at h₃
      change _ < (q v : ℝ)+1 at h₄
      rw [heq] at h₁ h₂
      have hh : |(∑ i, f x i)/t-(∑ i, f v i)/t| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
      rw [← sub_div,abs_div,abs_of_pos ht] at hh
      have hh' := (div_lt_iff₀ ht).mp hh
      simpa only [map_sub,Pi.sub_apply,Finset.sum_sub_distrib,one_mul] using hh'.le

end BalancedFiniteSets


namespace BalancedLattice
open scoped BigOperators

/-- Many lattice points with every coordinate AND their sum bounded. -/
theorem exists_many {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (t : ℝ) (ht : 0 < t) :
    ∃ W : Finset L, W.Nonempty ∧
      (t/3)^(Fintype.card ι) ≤ (W.card : ℝ)*ZLattice.covolume L ∧
      ∀ w ∈ W, (∀ i, |(w : ι → ℝ) i| ≤ 2*t) ∧ |∑ i, (w : ι → ℝ) i| ≤ t := by
  classical
  obtain ⟨U,hU,hUcard,_⟩ := LatticeCube.exists_cube L t ht.le
  have hUpos : U.Nonempty := ⟨0,(hU 0).mpr (by simpa using fun _ : ι => ht.le)⟩
  obtain ⟨W,hW,hcard,hbound⟩ := BalancedFiniteSets.exists_balanced U hUpos L.subtype.toAddMonoidHom t ht
    (fun x hx => (hU x).mp hx)
  refine ⟨W,hW,?_,hbound⟩
  have hc : U.card ≤ 3^(Fintype.card ι)*W.card :=
    hcard.trans (Nat.mul_le_mul_right _ (BalancedFiniteSets.linear_le_pow _))
  have hh : t^(Fintype.card ι) ≤ (3 : ℝ)^(Fintype.card ι)*W.card*ZLattice.covolume L :=
    hUcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (ZLattice.covolume_pos L).le)
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) _)).mpr
  nlinarith

end BalancedLattice


namespace BoundedUnits
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]

/-- A lower count for units with every infinite-place logarithm bounded.
The standard omitted log coordinate is explicitly controlled. -/
theorem exists_many (t : ℝ) (ht : 0 < t) :
    ∃ U : Finset (𝓞 K)ˣ, U.Nonempty ∧
      (t/3)^(NumberField.Units.rank K) ≤ (U.card : ℝ)*NumberField.Units.regulator K ∧
      ∀ u ∈ U, ∀ w : InfinitePlace K, |Real.log (w (u : K))| ≤ 2*t := by
  let L := NumberField.Units.unitLattice K
  have hlift : ∀ x : L, ∃ u : (𝓞 K)ˣ, NumberField.Units.logEmbedding K (Additive.ofMul u) = (x : logSpace K) := by
    intro x
    obtain ⟨a,_,ha⟩ := Submodule.mem_map.mp x.property
    exact ⟨a.toMul,ha⟩
  choose lift hlift using hlift
  have hinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    rw [← hlift x,← hlift y,hxy]
  obtain ⟨W,hW,hWcard,hWbound⟩ := BalancedLattice.exists_many L t ht
  let U := W.image lift
  have hc : U.card = W.card := Finset.card_image_of_injective _ hinj
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  refine ⟨U,hW.image lift,?_,?_⟩
  · simpa only [hc,hcard,NumberField.Units.regulator] using hWcard
  · intro u hu w
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
    have hm : (1 : ℝ) ≤ mult w := by simp only [mult]; split_ifs <;> norm_num
    have hm0 : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have hle : |Real.log (w ((lift x : (𝓞 K)ˣ) : K))| ≤
        (mult w : ℝ)*|Real.log (w ((lift x : (𝓞 K)ˣ) : K))| :=
      le_mul_of_one_le_left (abs_nonneg _) hm
    by_cases hw : w = w₀
    · have hh := (hWbound x hx).2
      have hsum := sum_logEmbedding_component (lift x)
      rw [hlift x] at hsum
      rw [hsum,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)] at hh
      rw [← hw] at hh
      exact hle.trans (hh.trans (by linarith))
    · have hh := (hWbound x hx).1 ⟨w,hw⟩
      rw [← hlift x,logEmbedding_component,abs_mul,abs_of_nonneg hm0] at hh
      exact hle.trans hh

/-- The same finite family has uniformly bounded house at every complex embedding. -/
theorem exists_many_house_bounded (t : ℝ) (ht : 0 < t) :
    ∃ U : Finset (𝓞 K)ˣ, U.Nonempty ∧
      (t/3)^(NumberField.Units.rank K) ≤ (U.card : ℝ)*NumberField.Units.regulator K ∧
      ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ Real.exp (2*t) := by
  obtain ⟨U,hU,hcard,hbound⟩ := exists_many K t ht
  refine ⟨U,hU,hcard,?_⟩
  intro u hu σ
  have hh := hbound u hu (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : K)‖| ≤ 2*t at hh
  have hp : 0 < ‖σ (u : K)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  exact (Real.log_le_iff_le_exp hp).mp ((le_abs_self _).trans hh)

end BoundedUnits


/- An elementary, uniform positive height bound for nontrivial totally
real units. This is an auxiliary arithmetic estimate. -/

namespace TotallyRealHeight
open NumberField NumberField.InfinitePlace
open scoped BigOperators

/-- A degree-four real inequality sufficient for a uniform height bound. -/
theorem scalar_bound (y : ℝ) (hy : 0 ≤ y) :
    2*y*|y^2-1| ≤ (max 1 y)^4 := by
  by_cases h : y ≤ 1
  · rw [max_eq_left h,abs_of_nonpos (by nlinarith : y^2-1 ≤ 0)]
    have hh : 0 ≤ y^2*(1-y^2) := mul_nonneg (sq_nonneg y) (by nlinarith)
    nlinarith [sq_nonneg (y^2+y-1)]
  · have h' : 1 ≤ y := le_of_not_ge h
    rw [max_eq_right h',abs_of_nonneg (by nlinarith : 0 ≤ y^2-1)]
    nlinarith [sq_nonneg (y^2-y-1)]

private theorem log_max_identity (x : ℝ) (hx : 0 < x) :
    2*Real.log (max 1 x) = |Real.log x| + Real.log x := by
  by_cases h : 1 ≤ x
  · rw [max_eq_right h,abs_of_nonneg (Real.log_nonneg h)]
    ring
  · have h' : x ≤ 1 := le_of_not_ge h
    rw [max_eq_left h',Real.log_one,abs_of_nonpos (Real.log_nonpos hx.le h')]
    ring

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

private theorem place_quad (w : InfinitePlace K) (x : K) :
    w (x^2-1) = |(w x)^2-1| := by
  have hw := IsTotallyReal.isReal w
  rw [← norm_embedding_of_isReal hw (x^2-1),← norm_embedding_of_isReal hw x]
  simp [map_sub,map_pow,Real.norm_eq_abs]

private theorem prod_places_ge_one (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ ∏ w : InfinitePlace K, w (a : K) := by
  have hp := InfinitePlace.prod_eq_abs_norm (a : K)
  simp only [IsTotallyReal.mult_eq,pow_one] at hp
  rw [hp,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

/-- The multiplicative version, before taking logarithms. -/
theorem height_product_bound (u : (𝓞 K)ˣ) (hu : (u : K)^2 ≠ 1) :
    (2 : ℝ)^(Fintype.card (InfinitePlace K)) ≤
      (∏ w : InfinitePlace K, max 1 (w (u : K)))^4 := by
  classical
  let a : 𝓞 K := (u : 𝓞 K)^2-1
  have ha : a ≠ 0 := by
    intro h
    have hh := congrArg (algebraMap (𝓞 K) K) h
    apply hu
    simpa [a,sub_eq_zero] using hh
  have hprod : 1 ≤ ∏ w : InfinitePlace K, w ((u : K)^2-1) := by
    simpa [a] using prod_places_ge_one K a ha
  have hunit : (∏ w : InfinitePlace K, w (u : K)) = 1 := by
    simpa only [IsTotallyReal.mult_eq,pow_one,NumberField.Units.norm,Rat.cast_one] using
      InfinitePlace.prod_eq_abs_norm (u : K)
  have hpoint (w : InfinitePlace K) :
      2*w (u : K)*w ((u : K)^2-1) ≤ (max 1 (w (u : K)))^4 := by
    rw [place_quad K]
    exact scalar_bound _ (apply_nonneg w _)
  have hp := Finset.prod_le_prod (s := Finset.univ)
    (fun w _ => mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg w _)) (apply_nonneg w _))
    (fun w _ => hpoint w)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Finset.prod_pow,hunit,mul_one] at hp
  exact (le_mul_of_one_le_right (by positivity) hprod).trans hp

/-- A nontrivial totally real unit has uniformly positive average logarithmic
height. The deliberately nonoptimal constant is sufficient for covolumes. -/
theorem log_height_bound (u : (𝓞 K)ˣ) (hu : (u : K)^2 ≠ 1) :
    (Fintype.card (InfinitePlace K) : ℝ)*Real.log 2 ≤
      2*∑ w : InfinitePlace K, |Real.log (w (u : K))| := by
  classical
  have hp := height_product_bound K u hu
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2^(Fintype.card (InfinitePlace K))) hp
  rw [Real.log_pow,Real.log_pow,Real.log_prod (fun w _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))] at hlog
  have hsum : (∑ w : InfinitePlace K, Real.log (w (u : K))) = 0 := by
    simpa only [IsTotallyReal.mult_eq,Nat.cast_one,one_mul] using NumberField.Units.sum_mult_mul_log u
  have hid : 2*(∑ w : InfinitePlace K, Real.log (max 1 (w (u : K)))) =
      ∑ w : InfinitePlace K, |Real.log (w (u : K))| := by
    rw [Finset.mul_sum]
    simp_rw [log_max_identity _ (NumberField.Units.pos_at_place u _)]
    rw [Finset.sum_add_distrib,hsum,add_zero]
  norm_num at hlog
  linarith

open NumberField.Units.dirichletUnitTheorem in
/-- In the standard truncated logarithmic embedding, a fixed small cube
contains no nonzero vector coming from a totally real unit. -/
theorem small_log_cube_sq_eq_one (u : (𝓞 K)ˣ)
    (hsmall : ∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    (u : K)^2 = 1 := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 ≤ Real.log 2/8 := by positivity
  have hcard : (0 : ℝ) < Fintype.card (InfinitePlace K) := by exact_mod_cast Fintype.card_pos
  have hsum := sum_logEmbedding_component u
  simp only [logEmbedding_component,IsTotallyReal.mult_eq,Nat.cast_one,one_mul] at hsum hsmall
  let N := Fintype.card (InfinitePlace K)
  let S := ∑ i : {w : InfinitePlace K // w ≠ w₀}, |Real.log (i.val (u : K))|
  have hs : S ≤ N*(Real.log 2/8) := by
    calc
      S ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ)*(Real.log 2/8) := by
        simpa [S] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hsmall i)
      _ ≤ N*(Real.log 2/8) := mul_le_mul_of_nonneg_right (by
        exact_mod_cast Fintype.card_subtype_le (fun w : InfinitePlace K => w ≠ w₀)) ht
  have hlast : |Real.log (w₀ (u : K))| ≤ S := by
    have hh := Finset.abs_sum_le_sum_abs
      (fun i : {w : InfinitePlace K // w ≠ w₀} => Real.log (i.val (u : K))) Finset.univ
    rw [hsum] at hh
    simpa [S] using hh
  have hall : (∑ w : InfinitePlace K, |Real.log (w (u : K))|) ≤ 2*N*(Real.log 2/8) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
    change |Real.log (w₀ (u : K))| + S ≤ _
    linarith
  have hu : (u : K)^2 = 1 := by
    by_contra hu
    have hh := log_height_bound K u hu
    change (N : ℝ)*Real.log 2 ≤ _ at hh
    have hp : (0 : ℝ) < N*Real.log 2 := mul_pos hcard hlog
    linarith
  exact hu

/-- The corresponding nonzero-vector exclusion for the unit log lattice. -/
theorem small_log_cube_trivial (u : (𝓞 K)ˣ)
    (hsmall : ∀ i, |NumberField.Units.logEmbedding K (Additive.ofMul u) i| ≤ Real.log 2/8) :
    NumberField.Units.logEmbedding K (Additive.ofMul u) = 0 := by
  classical
  have hu := small_log_cube_sq_eq_one K u hsmall
  rcases sq_eq_one_iff.mp hu with hu | hu
  · ext i
    simp [NumberField.Units.logEmbedding,hu]
  · ext i
    have hv : i.val (-1 : K) = 1 := by
      rw [← norm_embedding_of_isReal (IsTotallyReal.isReal i.val)]
      simp
    simp [NumberField.Units.logEmbedding,hu,hv]

end TotallyRealHeight


/- Finite packing bounds in real coordinates, and their application to
sumsets. These lemmas do not assume a lattice covolume or use integration. -/

open scoped Pointwise
namespace EmbeddingPacking

/-- Points separated by one in some coordinate occupy distinct unit boxes. -/
theorem card_le_of_separated_coordinates {α ι : Type*} [Fintype ι]
    (S : Finset α) (f : α → ι → ℝ) (R : ℕ)
    (hbound : ∀ a ∈ S, ∀ i, |f a i| ≤ R)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ i, 1 ≤ |f a i-f b i|) :
    S.card ≤ (2*R+1)^(Fintype.card ι) := by
  classical
  let box : Finset (ι → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(R : ℤ)) R)
  let g : α → ι → ℤ := fun a i => ⌊f a i⌋
  have hmaps : Set.MapsTo g (S : Set α) (box : Set (ι → ℤ)) := by
    intro a ha
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hb := abs_le.mp (hbound a ha i)
    constructor
    · exact Int.le_floor.mpr (by simpa using hb.1)
    · apply Int.floor_le_iff.mpr
      exact lt_of_le_of_lt hb.2 (by simp)
  have hinj : Set.InjOn g (S : Set α) := by
    intro a ha b hb heq
    by_contra hab
    obtain ⟨i,hi⟩ := hsep a ha b hb hab
    have hge : ⌊f a i⌋ = ⌊f b i⌋ := congrFun heq i
    have h₁ := Int.floor_le (f a i)
    have h₂ := Int.floor_le (f b i)
    have h₃ := Int.lt_floor_add_one (f a i)
    have h₄ := Int.lt_floor_add_one (f b i)
    rw [hge] at h₁ h₃
    have hlt : |f a i-f b i| < 1 := abs_lt.mpr ⟨by linarith,by linarith⟩
    exact hlt.not_ge hi
  have hc : box.card = (2*R+1)^(Fintype.card ι) := by
    simp only [box,Fintype.card_piFinset,Int.card_Icc]
    have hnat : ((R : ℤ)+1 - -(R : ℤ)).toNat = 2*R+1 := by omega
    simp only [hnat, Finset.prod_const, Finset.card_univ]
  exact hc ▸ Finset.card_le_card_of_injOn g hmaps hinj

/-- A sum of `j` elements has coordinate bounds multiplied by `j`. -/
theorem sumset_coordinate_bound {α ι : Type*} [AddCommGroup α] [DecidableEq α]
    (U : Finset α) (f : ι → α →+ ℝ) (R : ℝ)
    (hbound : ∀ u ∈ U, ∀ i, |f i u| ≤ R) (j : ℕ) :
    ∀ x ∈ j • U, ∀ i, |f i x| ≤ j*R := by
  classical
  induction j with
  | zero =>
    intro x hx i
    simp only [zero_nsmul,Finset.mem_zero] at hx
    subst x
    simp
  | succ j ih =>
    intro x hx i
    rw [add_nsmul,one_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    calc
      |f i (a+b)| = |f i a+f i b| := by rw [map_add]
      _ ≤ |f i a|+|f i b| := abs_add_le _ _
      _ ≤ j*R+R := add_le_add (ih a ha i) (hbound b hb i)
      _ = (j+1 : ℕ)*R := by push_cast; ring

/-- A uniform coordinate bound and separation yield polynomial additive
sumset growth. The number of coordinates, not a covolume, is the exponent. -/
theorem sumset_card_le {α ι : Type*} [AddCommGroup α] [DecidableEq α] [Fintype ι]
    (U : Finset α) (f : ι → α →+ ℝ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ i, |f i u| ≤ R)
    (hsep : ∀ a b : α, a ≠ b → ∃ i, 1 ≤ |f i a-f i b|) (j : ℕ) :
    (j • U).card ≤ ((2*R+1)*(j+1))^(Fintype.card ι) := by
  classical
  have hh : ∀ x ∈ j • U, ∀ i, |f i x| ≤ (j*R : ℕ) := by
    simpa only [Nat.cast_mul] using
      sumset_coordinate_bound U f (R : ℝ) hbound j
  have hc := card_le_of_separated_coordinates (j • U) (fun a i => f i a) (j*R)
    hh (fun a _ b _ hab => hsep a b hab)
  exact hc.trans (Nat.pow_le_pow_left (by nlinarith : 2*(j*R)+1 ≤ (2*R+1)*(j+1)) _)

end EmbeddingPacking


namespace TotallyRealUnitCounting
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

private noncomputable abbrev logU (u : (𝓞 K)ˣ) : logSpace K := NumberField.Units.logEmbedding K (Additive.ofMul u)

omit [IsTotallyReal K] in
private theorem log_div (u v : (𝓞 K)ˣ) : logU K (u/v) = logU K u-logU K v := by
  exact map_sub (NumberField.Units.logEmbedding K) (Additive.ofMul u) (Additive.ofMul v)

/-- The only ambiguity of a totally real unit's logarithmic coordinates is sign. -/
theorem coe_eq_or_neg_of_log_eq (u v : (𝓞 K)ˣ) (h : logU K u = logU K v) :
    (u : K) = (v : K) ∨ (u : K) = -(v : K) := by
  have hs := TotallyRealHeight.small_log_cube_sq_eq_one K (u/v) (by
    intro i
    change |logU K (u/v) i| ≤ _
    rw [log_div,h,sub_self]
    simp only [Pi.zero_apply,abs_zero]
    positivity)
  have hm : ((u/v : (𝓞 K)ˣ) : K)*(v : K) = (u : K) := by
    rw [← NumberField.Units.coe_mul,div_mul_cancel]
  rcases sq_eq_one_iff.mp hs with hh | hh
  · left
    simpa [hh] using hm.symm
  · right
    simpa [hh] using hm.symm

private theorem fiber_card_le_two (U : Finset (𝓞 K)ˣ) (y : logSpace K) :
    (U.filter (fun u => logU K u = y)).card ≤ 2 := by
  classical
  let V := U.filter (fun u => logU K u = y)
  by_cases hV : V.Nonempty
  · obtain ⟨v,hv⟩ := hV
    have hv' := (Finset.mem_filter.mp hv).2
    have hh : V.card ≤ ({(v : K),-(v : K)} : Finset K).card := by
      apply Finset.card_le_card_of_injOn (fun u : (𝓞 K)ˣ => (u : K))
      · intro u hu
        have he := coe_eq_or_neg_of_log_eq K u v ((Finset.mem_filter.mp hu).2.trans hv'.symm)
        simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using he
      · exact (NumberField.Units.coe_injective K).injOn
    exact hh.trans (Finset.card_insert_le _ _)
  · exact (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hV)).le.trans (by norm_num)

/-- Uniformly bounded log coordinates permit only exponentially many totally
real units; the base grows linearly with the coordinate bound. -/
theorem card_le_of_log_bound (U : Finset (𝓞 K)ˣ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ i, |logU K u i| ≤ R*(Real.log 2/8)) :
    U.card ≤ 2*(2*R+1)^(NumberField.Units.rank K) := by
  classical
  let c : ℝ := Real.log 2/8
  have hc : 0 < c := by dsimp [c]; positivity
  let W := U.image (logU K)
  have hwbound : ∀ x ∈ W, ∀ i, |x i/c| ≤ R := by
    intro x hx i
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    rw [abs_div,abs_of_pos hc]
    exact (div_le_iff₀ hc).mpr (hbound u hu i)
  have hwsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∃ i, 1 ≤ |x i/c-y i/c| := by
    intro x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    by_contra! h
    have hs : ∀ i, |logU K (u/v) i| ≤ c := by
      intro i
      have hh := h i
      rw [← sub_div,abs_div,abs_of_pos hc] at hh
      have hh' := (div_lt_iff₀ hc).mp hh
      rw [log_div,Pi.sub_apply]
      linarith
    have hz := TotallyRealHeight.small_log_cube_trivial K (u/v) hs
    change logU K (u/v) = 0 at hz
    rw [log_div,sub_eq_zero] at hz
    exact hxy hz
  have hw := EmbeddingPacking.card_le_of_separated_coordinates W (fun x i => x i/c) R hwbound hwsep
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  rw [hcard] at hw
  exact (Finset.card_le_mul_card_image U 2 (fun y _ => fiber_card_le_two K U y)).trans (Nat.mul_le_mul_left 2 hw)

end TotallyRealUnitCounting


/- Relative norms and logarithmic bounds at infinite places. -/

namespace RelativeNormLog
open NumberField NumberField.InfinitePlace
open scoped BigOperators Classical

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

noncomputable def unitNorm : (𝓞 L)ˣ →* (𝓞 K)ˣ := Units.map (RingOfIntegers.norm K)

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
@[simp] theorem coe_unitNorm (u : (𝓞 L)ˣ) : ((unitNorm K L u : (𝓞 K)ˣ) : K) = Algebra.norm K (u : L) := rfl

omit [NumberField L] in
/-- A relative norm multiplies a full logarithmic bound by the relative degree. -/
theorem log_bound (u : (𝓞 L)ˣ) (t : ℝ)
    (hbound : ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t) (w : InfinitePlace K) :
    |Real.log (w ((unitNorm K L u : (𝓞 K)ˣ) : K))| ≤ (Module.finrank K L : ℝ)*t := by
  letI : Algebra K ℂ := w.embedding.toAlgebra
  have he : w.embedding (Algebra.norm K (u : L)) = ∏ σ : L →ₐ[K] ℂ, σ (u : L) :=
    Algebra.norm_eq_prod_embeddings K ℂ (u : L)
  have hlog : Real.log (w ((unitNorm K L u : (𝓞 K)ˣ) : K)) =
      ∑ σ : L →ₐ[K] ℂ, Real.log ‖σ (u : L)‖ := by
    rw [← norm_embedding_eq,coe_unitNorm,he,norm_prod,Real.log_prod]
    intro σ _
    apply norm_ne_zero_iff.mpr
    simpa only [map_zero] using σ.injective.ne (NumberField.Units.coe_ne_zero u)
  rw [hlog]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh : ∀ σ : L →ₐ[K] ℂ, |Real.log ‖σ (u : L)‖| ≤ t := by
    intro σ
    exact hbound (InfinitePlace.mk σ.toRingHom)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AlgHom.card] using
    Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hh σ)

end RelativeNormLog


/- A large norm fiber gives a large bounded subset of a homomorphism kernel. -/

namespace KernelFiber

theorem exists_large {G H ι : Type*} [CommGroup G] [CommGroup H]
    [DecidableEq G] [DecidableEq H] (S : Finset G) (hS : S.Nonempty)
    (N : G →* H) (f : Additive G →+ (ι → ℝ)) (t : ℝ)
    (hbound : ∀ x ∈ S, ∀ i, |f (Additive.ofMul x) i| ≤ t) :
    ∃ W : Finset G, W.Nonempty ∧ S.card ≤ (S.image N).card*W.card ∧
      ∀ w ∈ W, N w = 1 ∧ ∀ i, |f (Additive.ofMul w) i| ≤ 2*t := by
  classical
  obtain ⟨c,hc,hmax⟩ := (S.image N).exists_max_image
    (fun c => (S.filter (fun x => N x = c)).card) (hS.image N)
  let V := S.filter (fun x => N x = c)
  obtain ⟨v,hv,hNv⟩ := Finset.mem_image.mp hc
  have hvV : v ∈ V := Finset.mem_filter.mpr ⟨hv,hNv⟩
  let W := V.image (fun x => x/v)
  have hW : W.Nonempty := (show V.Nonempty from ⟨v,hvV⟩).image _
  have hcW : W.card = V.card := Finset.card_image_of_injective _ div_left_injective
  refine ⟨W,hW,?_,?_⟩
  · rw [hcW,mul_comm]
    exact Finset.card_le_mul_card_image S V.card hmax
  · intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hx,hNx⟩ := Finset.mem_filter.mp hx
    refine ⟨?_,?_⟩
    · rw [map_div,hNx,hNv,div_self']
    · intro i
      rw [ofMul_div,map_sub,Pi.sub_apply]
      exact (abs_sub _ _).trans (by linarith [hbound x hx i,hbound v hv i])

end KernelFiber

namespace BoundedNormOne
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in
/-- The full (unweighted) logarithmic map on units. -/
noncomputable def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w := Real.log (w (u.toMul : L))
  map_zero' := by simp; rfl
  map_add' := by intro u v; simp [Real.log_mul]; rfl

/-- Extract many bounded relative norm-one units. The saving is governed by
`rank U_L - rank U_K`, rather than by the degree of the base field. -/
theorem exists_many (N : ℕ) (hN : 0 < N) :
    ∃ W : Finset (𝓞 L)ˣ, W.Nonempty ∧
      ((Real.log 2/8)*N/3)^(NumberField.Units.rank L) ≤
        2*(4*Module.finrank K L*N+1 : ℕ)^(NumberField.Units.rank K) *
          (W.card : ℝ)*NumberField.Units.regulator L ∧
      ∀ u ∈ W, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ 4*(Real.log 2/8)*N := by
  let t : ℝ := (Real.log 2/8)*N
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨S,hS,hcard,hbound⟩ := BoundedUnits.exists_many L t ht
  let nm := RelativeNormLog.unitNorm K L
  have him : (S.image nm).card ≤ 2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K) := by
    have hh := TotallyRealUnitCounting.card_le_of_log_bound K (S.image nm) (2*Module.finrank K L*N) (by
      intro u hu i
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have hn := RelativeNormLog.log_bound K L v (2*t) (hbound v hv) i.val
      change |NumberField.Units.logEmbedding K (Additive.ofMul (nm v)) i| ≤ _
      rw [logEmbedding_component,InfinitePlace.mult,if_pos (IsTotallyReal.isReal i.val)]
      simp only [Nat.cast_one,one_mul]
      convert hn using 1; push_cast; dsimp [t]; ring)
    convert hh using 1; congr 3; ring
  obtain ⟨W,hW,hWcard,hWbound⟩ := KernelFiber.exists_large S hS nm (fullLog L) (2*t) hbound
  refine ⟨W,hW,?_,?_⟩
  · have hc : S.card ≤ (2*(4*Module.finrank K L*N+1)^(NumberField.Units.rank K))*W.card :=
      hWcard.trans (Nat.mul_le_mul_right W.card him)
    have hr : 0 ≤ NumberField.Units.regulator L := (NumberField.Units.regulator_pos L).le
    exact hcard.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hr)
  · intro u hu
    refine ⟨(hWbound u hu).1,?_⟩
    intro w
    convert (hWbound u hu).2 w using 1; dsimp [t]; ring

end BoundedNormOne



/- Residues of Dirichlet unit exponents give fifth roots of quotients. -/

namespace UnitResidues
open NumberField
open scoped Classical BigOperators

variable (L : Type*) [Field L] [NumberField L]

noncomputable def decomp (u : (𝓞 L)ˣ) : NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ℤ) :=
  Classical.choose (NumberField.Units.exist_unique_eq_mul_prod L u).exists

theorem decomp_spec (u : (𝓞 L)ˣ) :
    u = (decomp L u).1 * ∏ i, NumberField.Units.fundSystem L i ^ ((decomp L u).2 i) :=
  Classical.choose_spec (NumberField.Units.exist_unique_eq_mul_prod L u).exists

noncomputable def residue (u : (𝓞 L)ˣ) :
    NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
  ((decomp L u).1,fun i => (decomp L u).2 i)

/-- Quotients in a residue class are fifth powers. Torsion is included in
the color, so no surjectivity of fifth powers on torsion is assumed. -/
theorem exists_fifth_root (u v : (𝓞 L)ˣ) (h : residue L u = residue L v) :
    ∃ z : (𝓞 L)ˣ, z^5 = u/v := by
  let a := (decomp L u).2
  let b := (decomp L v).2
  have hζ : (decomp L u).1 = (decomp L v).1 := by
    simpa only [residue] using congrArg Prod.fst h
  have hexp : ∀ i, (5 : ℤ) ∣ a i-b i := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp
    rw [Int.cast_sub,sub_eq_zero]
    exact congrFun (congrArg Prod.snd h) i
  refine ⟨∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5),?_⟩
  calc
    (∏ i, NumberField.Units.fundSystem L i ^ ((a i-b i)/5))^5 =
        ∏ i, NumberField.Units.fundSystem L i ^ (a i-b i) := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro i _
      rw [← zpow_natCast,← zpow_mul]
      congr 1
      exact Int.ediv_mul_cancel (hexp i)
    _ = (∏ i, NumberField.Units.fundSystem L i ^ (a i)) /
        (∏ i, NumberField.Units.fundSystem L i ^ (b i)) := by
      simp only [zpow_sub,Finset.prod_mul_distrib,Finset.prod_inv_distrib,div_eq_mul_inv]
    _ = u/v := by
      conv_rhs => rw [decomp_spec L u,decomp_spec L v,hζ]
      dsimp only [a,b]
      rw [mul_div_mul_comm,div_self',one_mul]

end UnitResidues


/- A finite-index residue argument bounds the doubling of a complete
logarithmic cube. It includes torsion, provided the residue hypothesis holds. -/

open scoped Pointwise
namespace MultiplicativeLogCube

/-- A complete bounded logarithmic cube has small doubling whenever division
by five is available within each of a bounded number of residue classes. -/
theorem div_card_le {G ι Q : Type*} [CommGroup G] [DecidableEq G] [Fintype Q]
    (U : Finset G) (f : Additive G →+ (ι → ℝ)) (t : ℝ) (ht : 0 ≤ t)
    (hU : ∀ x, x ∈ U ↔ ∀ i, |f (Additive.ofMul x) i| ≤ t)
    (q : G → Q) (hroot : ∀ x y, q x = q y → ∃ z, z^5 = x/y) :
    (U/U).card ≤ Fintype.card Q * U.card := by
  classical
  let V : Finset G := U/U
  have hV : ∀ x ∈ V, ∀ i, |f (Additive.ofMul x) i| ≤ 2*t := by
    intro x hx i
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_div.mp hx
    calc
      |f (Additive.ofMul (a/b)) i| = |f (Additive.ofMul a) i-f (Additive.ofMul b) i| := by simp
      _ ≤ |f (Additive.ofMul a) i|+|f (Additive.ofMul b) i| := abs_sub _ _
      _ ≤ t+t := add_le_add ((hU a).mp ha i) ((hU b).mp hb i)
      _ = 2*t := by ring
  have hf : ∀ c ∈ V.image q, (V.filter (fun x => q x = c)).card ≤ U.card := by
    intro c hc
    let T : Finset G := V.filter (fun x => q x = c)
    obtain ⟨x₀,hx₀,hq₀⟩ := Finset.mem_image.mp hc
    have hex : ∀ x ∈ T, ∃ z ∈ U, z^5 = x/x₀ := by
      intro x hx
      obtain ⟨hx,hqx⟩ := Finset.mem_filter.mp hx
      obtain ⟨z,hz⟩ := hroot x x₀ (hqx.trans hq₀.symm)
      refine ⟨z,(hU z).mpr ?_,hz⟩
      intro i
      have he : 5 * f (Additive.ofMul z) i = f (Additive.ofMul x) i - f (Additive.ofMul x₀) i := by
        have hh := congrArg (fun w => f (Additive.ofMul w) i) hz
        simpa using hh
      have hb : |f (Additive.ofMul x) i - f (Additive.ofMul x₀) i| ≤ 4*t :=
        (abs_sub _ _).trans (by linarith [hV x hx i,hV x₀ hx₀ i])
      rw [← he,abs_mul] at hb
      norm_num at hb
      linarith
    let g : T → U := fun x => ⟨Classical.choose (hex x x.property),
      (Classical.choose_spec (hex x x.property)).1⟩
    have hg (x : T) : (g x : G)^5 = (x : G)/x₀ :=
      (Classical.choose_spec (hex x x.property)).2
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have hh := congrArg (fun z : U => (z : G)^5) hxy
      dsimp only at hh
      rw [hg,hg] at hh
      exact div_left_injective hh
    simpa using Fintype.card_le_of_injective g hinj
  calc
    (U/U).card ≤ U.card * (V.image q).card := Finset.card_le_mul_card_image V U.card hf
    _ ≤ U.card * Fintype.card Q := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
    _ = Fintype.card Q * U.card := Nat.mul_comm _ _


end MultiplicativeLogCube

namespace UnitCubeDoubling
open NumberField NumberField.Units.dirichletUnitTheorem
open scoped Classical BigOperators Pointwise

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]

omit [NumberField K] [NumberField L] in
noncomputable def fullLog : Additive (𝓞 L)ˣ →+ (InfinitePlace L → ℝ) where
  toFun u w := Real.log (w (u.toMul : L))
  map_zero' := by simp; rfl
  map_add' := by intro u v; simp [Real.log_mul]; rfl

/-- Bounded full logarithms give a finite set of units. -/
theorem finite_fullLog (t : ℝ) :
    {u : (𝓞 L)ˣ | ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t}.Finite := by
  apply Set.Finite.of_finite_image (f := fun u : (𝓞 L)ˣ => (u : L)) ?_
    (NumberField.Units.coe_injective L).injOn
  apply (Embeddings.finite_of_norm_le L ℂ (Real.exp t)).subset
  rintro _ ⟨u,hu,rfl⟩
  refine ⟨u.val.isIntegral_coe,?_⟩
  intro σ
  have hh := hu (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : L)‖| ≤ t at hh
  have hp : 0 < ‖σ (u : L)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  exact (Real.log_le_iff_le_exp hp).mp ((le_abs_self _).trans hh)

variable [IsTotallyReal K]

/-- A fifth root of unity in a totally real field is trivial. -/
theorem pow_five_eq_one (u : (𝓞 K)ˣ) (h : u^5 = 1) : u = 1 := by
  let σ : K →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace K))
  apply NumberField.Units.coe_injective K
  apply σ.injective
  have hh := congrArg (fun u : (𝓞 K)ˣ => σ (u : K)) h
  simp only [NumberField.Units.coe_pow,NumberField.Units.coe_one,map_pow,map_one] at hh ⊢
  exact (Odd.pow_inj (by decide : Odd 5)).mp (by simpa using hh)

/-- Any homomorphism into totally real units has a finite complete logarithmic
kernel cube, with a doubling factor controlled by the ambient unit rank and
torsion order. -/
theorem exists_cube (N : (𝓞 L)ˣ →* (𝓞 K)ˣ) (t : ℝ) (ht : 0 ≤ t) :
    ∃ U : Finset (𝓞 L)ˣ,
      (∀ u, u ∈ U ↔ N u = 1 ∧ ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤ t) ∧
      (U/U).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*U.card := by
  let G := N.ker
  have hf : {u : G | ∀ w : InfinitePlace L, |Real.log (w ((u : (𝓞 L)ˣ) : L))| ≤ t}.Finite :=
    (finite_fullLog L t).preimage (Function.Injective.injOn Subtype.val_injective)
  let V : Finset G := hf.toFinset
  have hV (u : G) : u ∈ V ↔ ∀ w : InfinitePlace L, |Real.log (w ((u : (𝓞 L)ˣ) : L))| ≤ t := by
    exact Set.Finite.mem_toFinset hf
  let f : Additive G →+ (InfinitePlace L → ℝ) :=
    (fullLog L).comp N.ker.subtype.toAdditive
  let q : G → NumberField.Units.torsion L × (Fin (NumberField.Units.rank L) → ZMod 5) :=
    fun u => UnitResidues.residue L (u : (𝓞 L)ˣ)
  have hroot : ∀ x y : G, q x = q y → ∃ z : G, z^5 = x/y := by
    intro x y hxy
    obtain ⟨z,hz⟩ := UnitResidues.exists_fifth_root L (x : (𝓞 L)ˣ) (y : (𝓞 L)ˣ) hxy
    have hnz : N z = 1 := by
      apply pow_five_eq_one K
      rw [← map_pow,hz,map_div,x.property,y.property,div_self']
    exact ⟨⟨z,hnz⟩,Subtype.ext hz⟩
  have hcard := MultiplicativeLogCube.div_card_le V f t ht hV q hroot
  have hc : (V/V).card ≤ (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L)*V.card := by
    simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,ZMod.card] using hcard
  let U := V.image N.ker.subtype
  refine ⟨U,?_,?_⟩
  · intro u
    constructor
    · intro hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      exact ⟨v.property,(hV v).mp hv⟩
    · intro hu
      exact Finset.mem_image.mpr ⟨⟨u,hu.1⟩,(hV _).mpr hu.2,rfl⟩
  · dsimp only [U]
    rw [← Finset.image_div,Finset.card_image_of_injective (f := N.ker.subtype) _ Subtype.val_injective,
      Finset.card_image_of_injective (f := N.ker.subtype) _ Subtype.val_injective]
    exact hc

end UnitCubeDoubling

namespace NumberFieldPacking
open NumberField
open scoped Pointwise

variable (K : Type*) [Field K] [NumberField K]

/-- Redundant real coordinates; the factor two gives unit separation. -/
noncomputable def coordinate (i : (K →+* ℂ) × Bool) : 𝓞 K →+ ℝ :=
  (2 : ℕ) • ((if i.2 then Complex.reAddGroupHom else Complex.imAddGroupHom).comp
    ((i.1.comp (algebraMap (𝓞 K) K)).toAddMonoidHom))

private theorem separated (a b : 𝓞 K) (hab : a ≠ b) :
    ∃ i, 1 ≤ |coordinate K i a-coordinate K i b| := by
  obtain ⟨σ,hσ⟩ := NumberField.exists_conjugate_one_le_norm (sub_ne_zero.mpr hab)
  have he := Complex.norm_le_abs_re_add_abs_im (σ ((a-b : 𝓞 K) : K))
  by_cases hr : 1 ≤ 2*|(σ ((a-b : 𝓞 K) : K)).re|
  · refine ⟨(σ,true),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hr
  · have hi : 1 ≤ 2*|(σ ((a-b : 𝓞 K) : K)).im| := by linarith
    refine ⟨(σ,false),?_⟩
    simpa [coordinate,map_sub,← mul_sub,abs_mul] using hi

variable [DecidableEq (𝓞 K)]

/-- Algebraic integers with uniformly bounded conjugates have polynomial
sumset growth in their field degree. No discriminant estimate is needed. -/
theorem sumset_card_le (U : Finset (𝓞 K)) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ R) (j : ℕ) :
    (j • U).card ≤ ((4*R+1)*(j+1))^(2*Module.finrank ℚ K) := by
  classical
  have hb : ∀ u ∈ U, ∀ i, |coordinate K i u| ≤ (2*R : ℕ) := by
    intro u hu ⟨σ,b⟩
    cases b
    · have hh := (Complex.abs_im_le_norm (σ (u : K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
    · have hh := (Complex.abs_re_le_norm (σ (u : K))).trans (hbound u hu σ)
      simpa [coordinate,abs_mul] using (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2))
  have hc := EmbeddingPacking.sumset_card_le U (coordinate K) (2*R) hb (separated K) j
  simpa [Fintype.card_prod,NumberField.Embeddings.card,mul_comm,mul_left_comm,mul_assoc] using hc

/-- The same packing estimate after any one embedding into the plane. -/
theorem image_sumset_card_le (U : Finset (𝓞 K)) (σ₀ : K →+* ℂ) (R : ℕ)
    (hbound : ∀ u ∈ U, ∀ σ : K →+* ℂ, ‖σ (u : K)‖ ≤ R) (j : ℕ) :
    (j • U.image (σ₀.comp (algebraMap (𝓞 K) K))).card ≤
      ((4*R+1)*(j+1))^(2*Module.finrank ℚ K) := by
  classical
  rw [← Finset.image_nsmul]
  exact Finset.card_image_le.trans (sumset_card_le K U R hbound j)

end NumberFieldPacking

namespace TorsionCount
open NumberField
open scoped Classical Pointwise

/-- A deliberately coarse exponential bound for roots of unity, obtained
from packing all conjugates rather than estimates for Euler's totient. -/
theorem card_le (L : Type*) [Field L] [NumberField L] :
    Fintype.card (NumberField.Units.torsion L) ≤ 10^(2*Module.finrank ℚ L) := by
  let f : NumberField.Units.torsion L → 𝓞 L := fun u => (u : (𝓞 L)ˣ).val
  have hf : Function.Injective f := Units.val_injective.comp Subtype.val_injective
  let U := Finset.univ.image f
  have hU : U.card = Fintype.card (NumberField.Units.torsion L) := by
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ]
  have hb : ∀ u ∈ U, ∀ σ : L →+* ℂ, ‖σ (u : L)‖ ≤ (1 : ℕ) := by
    intro u hu σ
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
    simpa only [f,Nat.cast_one,InfinitePlace.apply] using
      ((NumberField.Units.mem_torsion L).mp v.property (InfinitePlace.mk σ)).le
  have hh := NumberFieldPacking.sumset_card_le L U 1 hb 1
  simpa only [one_nsmul,hU] using hh

end TorsionCount


/- Explicit uniform constants for the norm-fiber unit count. -/

namespace NormOneArithmetic

theorem lower_count (d r s R B : ℕ) (hd : 0 < d) (hR : 0 < R) (hB : 0 < B)
    (hr : r ≤ d) (hs : s ≤ d) (hgap : 4*s+d ≤ 4*r)
    (A : ℝ) (hA : 0 ≤ A)
    (h : (((864*R*B : ℕ)^4 : ℝ)/48)^r ≤
      2*(9*((864*R*B : ℕ)^4 : ℝ))^s*A*(R : ℝ)^d) :
    (B : ℝ)^d ≤ A := by
  let T := 864*R*B
  let N := T^4
  have hT : 0 < T := by dsimp [T]; positivity
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hsr : s ≤ r := by omega
  have hgap' : d ≤ 4*(r-s) := by omega
  have hm : (N : ℝ)^r ≤ 2*(48 : ℝ)^r*(9*(N : ℝ))^s*A*(R : ℝ)^d := by
    have h' : ((N : ℝ)/48)^r ≤ 2*(9*(N : ℝ))^s*A*(R : ℝ)^d := by
      simpa only [N,T,Nat.cast_pow] using h
    rw [div_pow] at h'
    have hh := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 48) r)).mp h'
    nlinarith only [hh]
  have hc : (N : ℝ)^(r-s) ≤ 2*(48 : ℝ)^r*(9 : ℝ)^s*A*(R : ℝ)^d := by
    apply le_of_mul_le_mul_left ?_ (pow_pos hN s)
    calc
      (N : ℝ)^s * (N : ℝ)^(r-s) = (N : ℝ)^r := by rw [← pow_add,Nat.add_sub_of_le hsr]
      _ ≤ _ := hm
      _ = _ := by rw [mul_pow]; ring
  have h48 : (48 : ℝ)^r ≤ 48^d := pow_le_pow_right₀ (by norm_num) hr
  have h9 : (9 : ℝ)^s ≤ 9^d := pow_le_pow_right₀ (by norm_num) hs
  have hu : (N : ℝ)^(r-s) ≤ 2*(432*(R : ℝ))^d*A := by
    calc
      (N : ℝ)^(r-s) ≤ _ := hc
      _ ≤ 2*(48 : ℝ)^d*9^d*A*(R : ℝ)^d := by gcongr
      _ = _ := by rw [show (432 : ℝ) = 48*9 by norm_num]; simp only [mul_pow]; ring
  have hl : 2*(432*(R : ℝ))^d*(B : ℝ)^d ≤ (N : ℝ)^(r-s) := by
    calc
      2*(432*(R : ℝ))^d*(B : ℝ)^d ≤ (2 : ℝ)^d*(432*(R : ℝ))^d*(B : ℝ)^d := by
        gcongr
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hd
      _ = ((2 : ℝ)*(432*(R : ℝ))*(B : ℝ))^d := by simp only [mul_pow]
      _ = (T : ℝ)^d := by congr 1; dsimp [T]; push_cast; ring
      _ ≤ (T : ℝ)^(4*(r-s)) := pow_le_pow_right₀ (by exact_mod_cast hT) hgap'
      _ = (N : ℝ)^(r-s) := by dsimp [N]; rw [Nat.cast_pow,pow_mul]
  exact le_of_mul_le_mul_left (hl.trans hu) (by positivity)

end NormOneArithmetic


/- Elementary bounds relating unit rank and field degree. -/
namespace UnitRankBounds
open NumberField

theorem rank_le_degree (L : Type*) [Field L] [NumberField L] :
    NumberField.Units.rank L ≤ Module.finrank ℚ L := by
  have hh := InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [NumberField.Units.rank,InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

end UnitRankBounds

namespace UniformNormOne
open NumberField
open scoped Classical BigOperators Pointwise

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

/-- An exponential regulator bound and a linear rank gap provide an
arbitrarily large fixed exponential family of bounded norm-one units. -/
theorem exists_many (R B : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L ≤ 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ W : Finset (𝓞 L)ˣ, W.Nonempty ∧ B^(Module.finrank ℚ L) ≤ W.card ∧
      ∀ u ∈ W, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
          4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ) := by
  let N := (864*R*B)^4
  have hN : 0 < N := by dsimp [N]; positivity
  obtain ⟨W,hW,hcard,hbound⟩ := BoundedNormOne.exists_many K L N hN
  refine ⟨W,hW,?_,?_⟩
  · have hd : 0 < Module.finrank ℚ L := Module.finrank_pos
    have hr := UnitRankBounds.rank_le_degree L
    have hs : NumberField.Units.rank K ≤ Module.finrank ℚ L := by omega
    have hh : ((N : ℝ)/48)^(NumberField.Units.rank L) ≤
        2*(9*(N : ℝ))^(NumberField.Units.rank K)*(W.card : ℝ)*(R : ℝ)^(Module.finrank ℚ L) := by
      calc
        ((N : ℝ)/48)^(NumberField.Units.rank L) ≤
            ((Real.log 2/8)*N/3)^(NumberField.Units.rank L) := by
          apply pow_le_pow_left₀ (by positivity)
          have hl : (1 : ℝ)/48 ≤ Real.log 2/24 := by linarith [Real.log_two_gt_d9]
          nlinarith [mul_le_mul_of_nonneg_right hl (Nat.cast_nonneg N)]
        _ ≤ _ := hcard
        _ ≤ _ := by
          have hr0 := (NumberField.Units.regulator_pos L).le
          have hnat : 4*Module.finrank K L*N+1 ≤ 9*N := by nlinarith
          have hb : (4*Module.finrank K L*N+1 : ℕ) ≤ (9*(N : ℝ)) := by exact_mod_cast hnat
          gcongr
    have hc := NormOneArithmetic.lower_count (Module.finrank ℚ L) (NumberField.Units.rank L)
      (NumberField.Units.rank K) R B hd hR hB hr hs hgap (W.card : ℝ) (Nat.cast_nonneg _)
      (by simpa only [N,Nat.cast_pow] using hh)
    exact_mod_cast hc
  · intro u hu
    simpa only [N,Nat.cast_pow] using hbound u hu

/-- A complete norm-one logarithmic cube with uniform exponential lower
cardinality and uniform exponential multiplicative doubling. -/
theorem exists_cube (R B : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L ≤ 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L) :
    ∃ U : Finset (𝓞 L)ˣ, U.Nonempty ∧ B^(Module.finrank ℚ L) ≤ U.card ∧
      (U/U).card ≤ 500^(Module.finrank ℚ L)*U.card ∧
      ∀ u ∈ U, RelativeNormLog.unitNorm K L u = 1 ∧
        ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
          4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ) := by
  let t : ℝ := 4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  obtain ⟨W,hW,hWcard,hWbound⟩ := exists_many K L R B hR hB hreg hrel hgap
  obtain ⟨U,hU,hcard⟩ := UnitCubeDoubling.exists_cube K L (RelativeNormLog.unitNorm K L) t ht
  have hsub : W ⊆ U := by intro u hu; exact (hU u).mpr (hWbound u hu)
  refine ⟨U,hW.mono hsub,hWcard.trans (Finset.card_le_card hsub),?_,fun u hu => (hU u).mp hu⟩
  have hp : (Fintype.card (NumberField.Units.torsion L))*5^(NumberField.Units.rank L) ≤
      500^(Module.finrank ℚ L) := by
    calc
      _ ≤ 10^(2*Module.finrank ℚ L)*5^(Module.finrank ℚ L) :=
        Nat.mul_le_mul (TorsionCount.card_le L) (Nat.pow_le_pow_right (by norm_num) (UnitRankBounds.rank_le_degree L))
      _ = _ := by rw [pow_mul,← mul_pow]; norm_num
  exact hcard.trans (Nat.mul_le_mul_right _ hp)

end UniformNormOne


/- A complex place of a quadratic extension of a totally real field sends
relative norm-one elements to the unit circle. -/

namespace QuadraticCircle
open NumberField
open scoped Classical BigOperators ComplexConjugate

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField L] in
theorem norm_eq_one (hdeg : Module.finrank K L = 2) (σ : L →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (x : L) (hx : Algebra.norm K x = 1) :
    ‖σ x‖ = 1 := by
  let φ : K →+* ℂ := σ.comp (algebraMap K L)
  letI : Algebra K ℂ := φ.toAlgebra
  let a : L →ₐ[K] ℂ := { σ with commutes' := fun _ => rfl }
  have hφ : ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b : L →ₐ[K] ℂ := { ComplexEmbedding.conjugate σ with
    commutes' := fun r => DFunLike.congr_fun hφ r }
  have hab : a ≠ b := by
    intro h
    apply hσ
    apply ComplexEmbedding.isReal_iff.mpr
    exact (congrArg AlgHom.toRingHom h).symm
  have hp : ({a,b} : Finset (L →ₐ[K] ℂ)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hab,AlgHom.card,hdeg])
  have he := Algebra.norm_eq_prod_embeddings K ℂ x
  rw [hx,map_one,← hp,Finset.prod_pair hab] at he
  have he' : (1 : ℂ) = σ x * conj (σ x) := he
  have hn := congrArg norm he'
  rw [norm_one,norm_mul,Complex.norm_conj] at hn
  nlinarith [norm_nonneg (σ x)]

end QuadraticCircle

namespace UniformDirections
open NumberField
open scoped Classical Pointwise

/-- The house bound used for the uniform norm-one cube. -/
def houseBound (R B : ℕ) : ℕ := 2^((864*R*B)^4)

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]

omit [NumberField K] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K] in
theorem house_bound (R B : ℕ) (u : (𝓞 L)ˣ)
    (hlog : ∀ w : InfinitePlace L, |Real.log (w (u : L))| ≤
      4*(Real.log 2/8)*((864*R*B : ℕ)^4 : ℝ)) (σ : L →+* ℂ) :
    ‖σ (u : L)‖ ≤ houseBound R B := by
  have hh := hlog (InfinitePlace.mk σ)
  change |Real.log ‖σ (u : L)‖| ≤ _ at hh
  have hp : 0 < ‖σ (u : L)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u))
  apply (Real.log_le_log_iff hp (by dsimp [houseBound]; positivity)).mp
  simp only [houseBound,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hl : 0 ≤ Real.log 2 := by positivity
  have hN : (0 : ℝ) ≤ (864*R*B : ℕ)^4 := by positivity
  have hm := mul_nonneg hl hN
  nlinarith [le_abs_self (Real.log ‖σ (u : L)‖)]

/-- Suitable number fields produce the circle directions required by the
finite geometric reduction. All bounds are uniform in the field degree. -/
theorem exists_directions (R : ℕ) (hR : 0 < R)
    (hreg : NumberField.Units.regulator L ≤ (R : ℝ)^(Module.finrank ℚ L))
    (hrel : Module.finrank K L = 2)
    (hgap : 4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L)
    (σ : L →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ V : Finset ℂ,
      (∀ v ∈ V, ‖v‖ = 1) ∧
      (16*500)^(2*Module.finrank ℚ L) ≤ V.card ∧
      (V/V).card ≤ 500^(2*Module.finrank ℚ L)*V.card ∧
      ∀ j : ℕ, (j • V).card ≤ ((4*houseBound R ((16*500)^2)+1)*(j+1))^(2*Module.finrank ℚ L) := by
  let B := (16*500)^2
  obtain ⟨U,hU,hcard,hdiv,hbound⟩ := UniformNormOne.exists_cube K L R B hR (by norm_num [B]) hreg hrel.le hgap
  let f : (𝓞 L)ˣ →* ℂ := (Units.coeHom ℂ).comp (NumberField.Units.complexEmbedding σ)
  have hf : Function.Injective f := σ.injective.comp (NumberField.Units.coe_injective L)
  let V := U.image f
  have hVcard : V.card = U.card := Finset.card_image_of_injective _ hf
  refine ⟨V,?_,?_,?_,?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    apply QuadraticCircle.norm_eq_one K L hrel σ hσ
    have hh := congrArg (fun u : (𝓞 K)ˣ => (u : K)) (hbound u hu).1
    exact hh
  · rw [hVcard]
    simpa only [B,pow_mul] using hcard
  · dsimp only [V]
    rw [← Finset.image_div,Finset.card_image_of_injective (f := f) _ hf,
      Finset.card_image_of_injective (f := f) _ hf]
    exact hdiv.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · intro j
    let A : Finset (𝓞 L) := U.image Units.val
    have hA : ∀ u ∈ A, ∀ τ : L →+* ℂ, ‖τ (u : L)‖ ≤ houseBound R B := by
      intro u hu τ
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      exact house_bound L R B a (hbound a ha).2 τ
    have he : A.image (σ.comp (algebraMap (𝓞 L) L)) = V := by
      rw [Finset.image_image]
      rfl
    rw [← he]
    exact NumberFieldPacking.image_sumset_card_le L A σ (houseBound R B) hA j

end UniformDirections


/- An elementary uniform bound for positive integer tuples of bounded product. -/

namespace ProductCounting
open scoped BigOperators

theorem card_le {ι : Type*} [Fintype ι] (S : Finset (ι → ℕ)) (B : ℕ)
    (hpos : ∀ x ∈ S, ∀ i, 0 < x i) (hprod : ∀ x ∈ S, ∏ i, x i ≤ B) :
    S.card ≤ 2^(Fintype.card ι) * B^2 := by
  classical
  let box : Finset (ι → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 B)
  let w : (ι → ℕ) → ℝ := fun x => ∏ i, ((x i : ℝ)^2)⁻¹
  have hs : S ⊆ box := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Finset.mem_Icc.mpr ⟨hpos x hx i,?_⟩
    have hp : 0 < ∏ i, x i := Finset.prod_pos (fun i _ => hpos x hx i)
    exact (Nat.le_of_dvd hp (Finset.dvd_prod_of_mem x (Finset.mem_univ i))).trans (hprod x hx)
  have hw (x : ι → ℕ) (hx : x ∈ S) : 1 ≤ (B : ℝ)^2*w x := by
    have hp : (0 : ℝ) < ∏ i, (x i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hpos x hx i)
    have hle : (∏ i, (x i : ℝ)) ≤ B := by exact_mod_cast hprod x hx
    dsimp only [w]
    rw [Finset.prod_inv_distrib,Finset.prod_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (sq_pos_of_pos hp)).mpr (by nlinarith)
  have hsum : (∑ n ∈ Finset.Icc 1 B, ((n : ℝ)^2)⁻¹) ≤ 2 := by
    have hset : Finset.Icc 1 B = Finset.Ioo 0 (B+1) := by ext n; simp; omega
    simpa [hset] using (sum_Ioo_inv_sq_le (α := ℝ) 0 (B+1))
  have hweight : ∑ x ∈ box, w x ≤ (2 : ℝ)^(Fintype.card ι) := by
    dsimp only [box,w]
    rw [Finset.sum_prod_piFinset (Finset.Icc 1 B) (fun (_ : ι) n => ((n : ℝ)^2)⁻¹)]
    simpa only [Finset.prod_const,Finset.card_univ] using
      Finset.prod_le_prod (s := (Finset.univ : Finset ι))
        (f := fun _ => ∑ n ∈ Finset.Icc 1 B, ((n : ℝ)^2)⁻¹) (g := fun _ => (2 : ℝ))
        (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) (fun _ _ => hsum)
  have hreal : (S.card : ℝ) ≤ (2 : ℝ)^(Fintype.card ι)*(B : ℝ)^2 := by
    calc
      (S.card : ℝ) = ∑ _x ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ x ∈ S, (B : ℝ)^2*w x := Finset.sum_le_sum (fun x hx => hw x hx)
      _ = (B : ℝ)^2 * ∑ x ∈ S, w x := (Finset.mul_sum _ _ _).symm
      _ ≤ (B : ℝ)^2 * ∑ x ∈ box, w x := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by dsimp [w]; positivity)) (sq_nonneg _)
      _ ≤ (B : ℝ)^2 * (2 : ℝ)^(Fintype.card ι) := mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
      _ = _ := mul_comm _ _
  exact_mod_cast hreal

end ProductCounting


/- Encode a multiset of colored rational primes by one positive integer
per color. Unique factorization makes the encoding injective. -/

open scoped BigOperators
namespace PrimeMultiset

noncomputable def encode {ι : Type*} (s : Multiset (ℕ × ι)) (i : ι) : ℕ := by
  classical
  exact ((s.filter (fun a => a.2 = i)).map Prod.fst).prod

private theorem count_color {ι : Type*} [DecidableEq ι] (s : Multiset (ℕ × ι)) (a : ℕ × ι) :
    Multiset.count a.1 ((s.filter (fun x => x.2 = a.2)).map Prod.fst) = Multiset.count a s := by
  rw [Multiset.count_map,Multiset.filter_filter,Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro x _
  constructor
  · rintro ⟨h₁,h₂⟩
    exact Prod.ext h₁ h₂.symm
  · intro h
    subst x
    simp

theorem encode_injective {ι : Type*} (s t : Multiset (ℕ × ι))
    (hs : ∀ a ∈ s, a.1.Prime) (ht : ∀ a ∈ t, a.1.Prime)
    (he : encode s = encode t) : s = t := by
  classical
  have hn (v : Multiset (ℕ × ι)) (hv : ∀ a ∈ v, a.1.Prime) (i : ι) :
      UniqueFactorizationMonoid.normalizedFactors (encode v i) =
        ((v.filter (fun a => a.2 = i)).map Prod.fst) := by
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro p hp
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hp
    exact Nat.prime_iff.mp (hv a (Multiset.mem_filter.mp ha).1)
  apply Multiset.ext.mpr
  intro a
  have hh := congrArg UniqueFactorizationMonoid.normalizedFactors (congrFun he a.2)
  rw [hn s hs,hn t ht] at hh
  have hc := congrArg (Multiset.count a.1) hh
  rw [count_color s a,count_color t a] at hc
  exact hc

theorem prod_encode {ι : Type*} [Fintype ι] (s : Multiset (ℕ × ι)) :
    (∏ i, encode s i) = (s.map Prod.fst).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [encode]
  | @cons a s ih =>
    have hc (i : ι) : encode (a ::ₘ s) i = (if a.2 = i then a.1 else 1)*encode s i := by
      by_cases h : a.2 = i <;> simp [encode,h]
    simp_rw [hc]
    rw [Finset.prod_mul_distrib,ih]
    simp

theorem encode_pos {ι : Type*} (s : Multiset (ℕ × ι))
    (hs : ∀ a ∈ s, a.1.Prime) (i : ι) : 0 < encode s i := by
  classical
  apply Multiset.prod_pos
  intro p hp
  obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hp
  exact (hs a (Multiset.mem_filter.mp ha).1).pos

end PrimeMultiset


namespace NormedFactorCounting
open UniqueFactorizationMonoid
open scoped BigOperators

variable {α ι : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  [NormalizationMonoid α] [Subsingleton αˣ]

noncomputable def primeFactors (a : α) : Multiset {p : α // Prime p} :=
  (normalizedFactors a).pmap (fun p hp => ⟨p,hp⟩) (fun p hp => prime_of_normalized_factor p hp)

omit [Subsingleton αˣ] in
private theorem map_primeFactors (a : α) :
    (primeFactors a).map Subtype.val = normalizedFactors a := by
  rw [primeFactors,Multiset.map_pmap,Multiset.pmap_eq_map]
  exact Multiset.map_id _

private theorem prod_primeFactors (a : α) (ha : a ≠ 0) :
    ((primeFactors a).map Subtype.val).prod = a := by
  rw [map_primeFactors]
  simpa only [associated_eq_eq] using prod_normalizedFactors ha

noncomputable def encode (c : {p : α // Prime p} → ℕ × ι) (a : α) : ι → ℕ :=
  PrimeMultiset.encode ((primeFactors a).map c)

theorem encode_injective (c : {p : α // Prime p} → ℕ × ι)
    (hc : Function.Injective c) (hp : ∀ p, (c p).1.Prime)
    {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (he : encode c a = encode c b) : a = b := by
  have hprime (x : α) : ∀ p ∈ (primeFactors x).map c, p.1.Prime := by
    intro p hpm
    obtain ⟨q,_,rfl⟩ := Multiset.mem_map.mp hpm
    exact hp q
  have hf := PrimeMultiset.encode_injective _ _ (hprime a) (hprime b) he
  have hpf := Multiset.map_injective hc hf
  have hn := congrArg (fun s : Multiset {p : α // Prime p} => (s.map Subtype.val).prod) hpf
  simpa only [prod_primeFactors a ha,prod_primeFactors b hb] using hn

theorem prod_encode_le [Fintype ι] (N : α →*₀ ℕ)
    (c : {p : α // Prime p} → ℕ × ι) (hN : ∀ p, (c p).1 ≤ N p.val)
    (a : α) (ha : a ≠ 0) : (∏ i, encode c a i) ≤ N a := by
  rw [encode,PrimeMultiset.prod_encode,Multiset.map_map]
  calc
    _ ≤ ((primeFactors a).map (fun p => N p.val)).prod :=
      Multiset.prod_map_le_prod_map _ _ (fun p _ => hN p)
    _ = N (((primeFactors a).map Subtype.val).prod) := by
      rw [← Multiset.prod_hom _ N,Multiset.map_map]
      rfl
    _ = N a := by rw [prod_primeFactors a ha]

/-- A normed unique-factorization monoid with at most `d` prime types over
each rational prime has at most `2^d B^2` nonzero elements of norm at most B. -/
theorem card_le [Fintype ι] (N : α →*₀ ℕ)
    (c : {p : α // Prime p} → ℕ × ι) (hc : Function.Injective c)
    (hp : ∀ p, (c p).1.Prime) (hN : ∀ p, (c p).1 ≤ N p.val)
    (S : Finset α) (B : ℕ) (hzero : ∀ a ∈ S, a ≠ 0) (hbound : ∀ a ∈ S, N a ≤ B) :
    S.card ≤ 2^(Fintype.card ι)*B^2 := by
  classical
  have he : (S.image (encode c)).card = S.card := Finset.card_image_iff.mpr (by
    intro a ha b hb hab
    exact encode_injective c hc hp (hzero a ha) (hzero b hb) hab)
  rw [← he]
  apply ProductCounting.card_le
  · intro x hx i
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    apply PrimeMultiset.encode_pos
    intro q hq
    obtain ⟨p,_,rfl⟩ := Multiset.mem_map.mp hq
    exact hp p
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact (prod_encode_le N c hN a (hzero a ha)).trans (hbound a ha)

end NormedFactorCounting


namespace IdealCounting
open NumberField
open scoped BigOperators

variable (K : Type*) [Field K] [NumberField K]

private abbrev PrimeIdeals := {P : Ideal (𝓞 K) // Prime P}

private def base (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p.val : ℤ)}

private theorem base_ne_bot (p : Nat.Primes) : base p ≠ ⊥ := by
  intro h
  have hp : (p.val : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
  exact p.property.ne_zero (by exact_mod_cast hp)

private instance base_maximal (p : Nat.Primes) : (base p).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast p.property.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp p.property)).isMaximal (base_ne_bot p)

private noncomputable def primeUnder (P : PrimeIdeals K) : Nat.Primes := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  letI : NeZero P.val := ⟨P.property.ne_zero⟩
  exact ⟨Ideal.absNorm (Ideal.under ℤ P.val),Nat.absNorm_under_prime P.val⟩

private theorem mem_fiber (P : PrimeIdeals K) :
    P.val ∈ primesOverFinset (base (primeUnder K P)) (𝓞 K) := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  have he : base (primeUnder K P) = Ideal.under ℤ P.val := Int.ideal_span_absNorm_eq_self _
  letI : P.val.LiesOver (base (primeUnder K P)) := by rw [he]; infer_instance
  exact (mem_primesOverFinset_iff (base_ne_bot _) _).mpr ⟨inferInstance,inferInstance⟩

private noncomputable def slot (p : Nat.Primes) :
    (primesOverFinset (base p) (𝓞 K)) ↪ Fin (Module.finrank ℚ K) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  change Fintype.card ↥(primesOverFinset (base p) (𝓞 K)) ≤ Fintype.card (Fin (Module.finrank ℚ K))
  rw [Fintype.card_coe,Fintype.card_fin]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K (base_ne_bot p)

private noncomputable def toSigma : PrimeIdeals K ↪
    (Σ p : Nat.Primes, (primesOverFinset (base p) (𝓞 K))) where
  toFun P := ⟨primeUnder K P,⟨P.val,mem_fiber K P⟩⟩
  inj' := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun x => x.2.val) h

private noncomputable def code : PrimeIdeals K ↪ ℕ × Fin (Module.finrank ℚ K) :=
  (toSigma K).trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl Nat.Primes) (slot K)).trans
      ((Equiv.sigmaEquivProd Nat.Primes (Fin (Module.finrank ℚ K))).toEmbedding.trans
        (Function.Embedding.prodMap ⟨Subtype.val,Subtype.val_injective⟩ (Function.Embedding.refl _))))

private theorem code_prime (P : PrimeIdeals K) : ((code K) P).1.Prime :=
  (primeUnder K P).property

private theorem code_le_norm (P : PrimeIdeals K) : ((code K) P).1 ≤ Ideal.absNorm P.val := by
  letI : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  letI : NeZero P.val := ⟨P.property.ne_zero⟩
  have hp : (Ideal.under ℤ P.val).IsPrime := inferInstance
  have hp0 : Ideal.under ℤ P.val ≠ ⊥ := by
    intro h
    have hh := Nat.absNorm_under_prime P.val
    rw [h] at hh
    exact Nat.not_prime_zero (by simpa using hh)
  letI : (Ideal.under ℤ P.val).IsMaximal := hp.isMaximal hp0
  change Ideal.absNorm (Ideal.under ℤ P.val) ≤ _
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P.val (Ideal.under ℤ P.val) hp hp0]
  exact Nat.le_self_pow (Ideal.inertiaDeg_ne_zero (Ideal.under ℤ P.val) P.val) _

/-- A uniform elementary ideal count, avoiding analytic properties of the
Dedekind zeta function. -/
theorem card_le (S : Finset (Ideal (𝓞 K))) (B : ℕ)
    (hzero : ∀ I ∈ S, I ≠ ⊥) (hbound : ∀ I ∈ S, Ideal.absNorm I ≤ B) :
    S.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
  classical
  simpa using NormedFactorCounting.card_le Ideal.absNorm (code K) (code K).injective
    (code_prime K) (code_le_norm K) S B hzero hbound

end IdealCounting


/- A dimension-uniform volume bound for the logarithmic simplex used in
Minkowski regulator estimates. -/

open MeasureTheory
open scoped ENNReal BigOperators
namespace SimplexVolume

def simplex {ι : Type*} [Fintype ι] (a : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, -a ≤ x i) ∧ ∑ i, x i ≤ a}

theorem l1_bound {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ) (ha : 0 ≤ a)
    (x : ι → ℝ) (hx : x ∈ simplex a) :
    ∑ i, |x i| ≤ 3*(Fintype.card ι)*a := by
  classical
  have hp (i : ι) : |x i| ≤ x i+2*a := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1 i]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc' := mul_le_mul_of_nonneg_right hc ha
  linarith [hx.2]

theorem volume_le {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ) (ha : 0 ≤ a) :
    volume (simplex (ι := ι) a) ≤ ENNReal.ofReal ((18*a)^(Fintype.card ι)) := by
  classical
  let r := Fintype.card ι
  have hs : simplex (ι := ι) a ⊆ {x : ι → ℝ | ∑ i, |x i| ≤ 3*r*a} :=
    fun x hx => l1_bound a ha x hx
  have hv : volume {x : ι → ℝ | ∑ i, |x i| ≤ 3*r*a} =
      ENNReal.ofReal ((3*r*a)^r * (2^r / r.factorial)) := by
    have h := volume_sum_rpow_le ι (p := 1) le_rfl (3*r*a)
    simp only [Real.rpow_one,div_one,one_add_one_eq_two,Real.Gamma_two,mul_one,
      Real.Gamma_nat_eq_factorial] at h
    rw [h,← ENNReal.ofReal_pow (by positivity : 0 ≤ 3*(r : ℝ)*a),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (3*(r : ℝ)*a)^r)]
  have he : (r : ℝ)^r / r.factorial ≤ (3 : ℝ)^r := by
    have h := Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg _) r
    have he' : Real.exp (r : ℝ) = (Real.exp 1)^r := by simpa only [mul_one] using Real.exp_nat_mul 1 r
    rw [he'] at h
    exact h.trans (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_d9.le.trans (by norm_num)) r)
  have hb : (3*(r : ℝ)*a)^r * (2^r / r.factorial) ≤ (18*a)^r := by
    calc
      _ = (6*a)^r * ((r : ℝ)^r / r.factorial) := by rw [show (6 : ℝ) = 3*2 by norm_num]; simp only [mul_pow]; ring
      _ ≤ (6*a)^r * (3 : ℝ)^r := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [← mul_pow]; congr 1; ring
  exact (measure_mono hs).trans (hv ▸ ENNReal.ofReal_le_ofReal hb)

end SimplexVolume


namespace LatticeCovering
open MeasureTheory
open scoped ENNReal Pointwise

/-- Every measurable orbit-covering set has measure at least that of a
fundamental domain. Measurability of the covering set is not needed here. -/
theorem measure_fundamental_le {G E : Type*} [AddGroup G] [Countable G]
    [AddAction G E] [MeasurableSpace E] [MeasurableConstVAdd G E]
    (μ : Measure E) [VAddInvariantMeasure G E μ]
    (F S : Set E) (hF : IsAddFundamentalDomain G F μ)
    (hcover : ∀ x : E, ∃ g : G, g +ᵥ x ∈ S) : μ F ≤ μ S := by
  have hsub : F ⊆ ⋃ g : G, (g +ᵥ S) ∩ F := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x
    refine Set.mem_iUnion.mpr ⟨-g,?_,hx⟩
    exact ⟨g +ᵥ x,hg,neg_vadd_vadd g x⟩
  calc
    μ F ≤ μ (⋃ g : G, (g +ᵥ S) ∩ F) := measure_mono hsub
    _ ≤ ∑' g : G, μ ((g +ᵥ S) ∩ F) := measure_iUnion_le _
    _ = μ S := (hF.measure_eq_tsum S).symm

/-- A finite simplex covering of a lattice torus controls its covolume,
with no factors growing faster than exponentially in the dimension. -/
theorem covolume_le_of_simplex_cover {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (T : Finset (ι → ℝ)) (a : ℝ) (ha : 0 ≤ a)
    (hcover : ∀ x : ι → ℝ, ∃ g : L, ∃ t ∈ T,
      (g : ι → ℝ)+x-t ∈ SimplexVolume.simplex a) :
    ZLattice.covolume L ≤ T.card * (18*a)^(Fintype.card ι) := by
  classical
  letI : MeasurableVAdd L (ι → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (ι → ℝ))
  letI : VAddInvariantMeasure L (ι → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (ι → ℝ) volume)
  let b := Module.Free.chooseBasis ℤ L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  let S : Set (ι → ℝ) := ⋃ t : T, t.val +ᵥ SimplexVolume.simplex a
  have hs : ∀ x : ι → ℝ, ∃ g : L, g +ᵥ x ∈ S := by
    intro x
    obtain ⟨g,t,ht,hmem⟩ := hcover x
    refine ⟨g,Set.mem_iUnion.mpr ⟨⟨t,ht⟩,?_⟩⟩
    refine ⟨(g : ι → ℝ)+x-t,hmem,?_⟩
    change t+((g : ι → ℝ)+x-t) = (g : ι → ℝ)+x
    abel
  have hS : volume S ≤ (T.card : ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)) := by
    calc
      volume S ≤ ∑' t : T, volume (t.val +ᵥ SimplexVolume.simplex a) := measure_iUnion_le _
      _ = (T.card : ℝ≥0∞)*volume (SimplexVolume.simplex (ι := ι) a) := by simp [tsum_fintype]
      _ ≤ _ := mul_le_mul_right (SimplexVolume.volume_le a ha) _
  have h := (measure_fundamental_le volume F S hF hs).trans hS
  have hr := ENNReal.toReal_mono (by finiteness :
    (T.card : ℝ≥0∞)*ENNReal.ofReal ((18*a)^(Fintype.card ι)) ≠ ⊤) h
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal (by positivity)] at hr
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF]
  exact hr

end LatticeCovering



/- Quantitative Minkowski approximation in logarithmic coordinates. -/

namespace MinkowskiLogCover
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def extend (x : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ i, x i else x ⟨w,h⟩

private theorem extend_sum (x : logSpace K) : ∑ w, extend K x w = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have hs : (∑ i : {w : InfinitePlace K // w ≠ w₀}, extend K x i.val) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    exact dif_neg i.property
  rw [hs]
  simp [extend]

private noncomputable def radii (t : ℝ) (x : logSpace K) (w : InfinitePlace K) : ℝ≥0 :=
  ⟨Real.exp (t+extend K x w/(mult w : ℝ)),(Real.exp_pos _).le⟩

private theorem radii_prod (t : ℝ) (x : logSpace K) :
    (∏ w : InfinitePlace K, (radii K t x w : ℝ≥0∞)^(mult w)) =
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)) := by
  classical
  have hreal : ((∏ w : InfinitePlace K, (radii K t x w)^(mult w) : ℝ≥0) : ℝ) =
      Real.exp ((Module.finrank ℚ K : ℝ)*t) := by
    simp only [NNReal.coe_prod,NNReal.coe_pow,radii,NNReal.coe_mk,← Real.exp_nat_mul]
    rw [← Real.exp_sum]
    congr 1
    have he (w : InfinitePlace K) : (mult w : ℝ)*(t+extend K x w/(mult w : ℝ)) =
        (mult w : ℝ)*t+extend K x w := by
      have hm : (mult w : ℝ) ≠ 0 := mult_coe_ne_zero
      field_simp
    simp_rw [he]
    rw [Finset.sum_add_distrib,extend_sum,add_zero,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hnn : (∏ w : InfinitePlace K, (radii K t x w)^(mult w) : ℝ≥0) =
      ⟨Real.exp ((Module.finrank ℚ K : ℝ)*t),(Real.exp_pos _).le⟩ := NNReal.eq hreal
  simp_rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_finset_prod,hnn,ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]

/-- Every log-space point has a nearby projected algebraic-integer point,
with norm bounded uniformly by the Minkowski volume parameter. -/
theorem exists_integer (t : ℝ)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (x : logSpace K) : ∃ a : 𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a : K)) ≤ Real.exp ((Module.finrank ℚ K : ℝ)*t) ∧
      ∀ w : InfinitePlace K, (mult w : ℝ)*Real.log (w (a : K)) ≤
        extend K x w+(mult w : ℝ)*t := by
  classical
  obtain ⟨a,ha,hab⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := radii K t x)
    (by rw [convexBodyLT_volume,ENNReal.coe_finset_prod]; simp_rw [ENNReal.coe_pow]; rw [radii_prod]; exact hM)
  refine ⟨a,ha,?_,?_⟩
  · rw [mixedEmbedding.norm_apply]
    have hh : (∏ w : InfinitePlace K, normAtPlace w (mixedEmbedding K (a : K))^(mult w)) ≤
        ∏ w : InfinitePlace K, (radii K t x w : ℝ)^(mult w) := by
      apply Finset.prod_le_prod
      · intro w _; exact pow_nonneg (normAtPlace_nonneg _ _) _
      · intro w _
        rw [normAtPlace_apply]
        exact pow_le_pow_left₀ (apply_nonneg w _) (hab w).le _
    apply hh.trans_eq
    have hp := congrArg ENNReal.toReal (radii_prod K t x)
    simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hp
  · intro w
    have hp : 0 < w (a : K) := pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha)
    have hl : Real.log (w (a : K)) < t+extend K x w/(mult w : ℝ) :=
      (Real.log_lt_iff_lt_exp hp).mpr (hab w)
    have hm : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have he := mul_le_mul_of_nonneg_left hl.le hm
    have hn : (mult w : ℝ) ≠ 0 := mult_coe_ne_zero
    convert he using 1
    field_simp
    ring

end MinkowskiLogCover


namespace MinkowskiLogCover
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def fullLog (a : K) (w : InfinitePlace K) : ℝ :=
  (mult w : ℝ)*(Real.log (w a)-Real.log (mixedEmbedding.norm (mixedEmbedding K a))/(Module.finrank ℚ K : ℝ))

private theorem logMap_eq_fullLog (a : K) (i : {w : InfinitePlace K // w ≠ w₀}) :
    logMap (mixedEmbedding K a) i = fullLog K a i.val := by
  simp [logMap_apply,fullLog,div_eq_mul_inv]

private theorem fullLog_sum (a : K) (ha : a ≠ 0) : ∑ w, fullLog K a w = 0 := by
  have hs : Real.log (mixedEmbedding.norm (mixedEmbedding K a)) =
      ∑ w : InfinitePlace K, (mult w : ℝ)*Real.log (w a) := by
    rw [mixedEmbedding.norm_apply,Real.log_prod]
    · simp [normAtPlace_apply,Real.log_pow]
    · intro w _
      rw [normAtPlace_apply]
      exact pow_ne_zero _ ((pos_iff.mpr ha).ne')
  simp only [fullLog,mul_sub,Finset.sum_sub_distrib]
  rw [← hs,← Finset.sum_mul,← Nat.cast_sum,sum_mult_eq]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  field_simp
  ring

private theorem integer_norm_ge_one (a : 𝓞 K) (ha : a ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (a : K)) := by
  rw [norm_eq_norm,← Algebra.coe_norm_int,← Int.cast_one,← Int.cast_abs,Rat.cast_intCast,Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr ha)

/-- Each log-space point is covered by a projected small-norm algebraic
integer plus a simplex of dimension-uniform width. -/
theorem exists_approximation (t : ℝ) (ht : 0 ≤ t)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (x : logSpace K) : ∃ a : 𝓞 K, a ≠ 0 ∧
      mixedEmbedding.norm (mixedEmbedding K (a : K)) ≤ Real.exp ((Module.finrank ℚ K : ℝ)*t) ∧
      x-logMap (mixedEmbedding K (a : K)) ∈ SimplexVolume.simplex (2*t) := by
  obtain ⟨a,ha,hanorm,hbound⟩ := exists_integer K t hM x
  have hN : 0 ≤ Real.log (mixedEmbedding.norm (mixedEmbedding K (a : K))) :=
    Real.log_nonneg (integer_norm_ge_one K a ha)
  have hfull : ∀ w : InfinitePlace K, fullLog K (a : K) w ≤ extend K x w+2*t := by
    intro w
    have hm : (mult w : ℝ) ≤ 2 := by simp only [mult]; split_ifs <;> norm_num
    have hm0 : (0 : ℝ) ≤ mult w := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
    have hn := mul_nonneg hm0 (div_nonneg hN hd)
    have hb := hbound w
    have hc := mul_le_mul_of_nonneg_right hm ht
    dsimp only [fullLog]
    nlinarith
  let δ : InfinitePlace K → ℝ := fun w => extend K x w-fullLog K (a : K) w
  have hid (i : {w : InfinitePlace K // w ≠ w₀}) :
      (x-logMap (mixedEmbedding K (a : K))) i = δ i.val := by
    rw [Pi.sub_apply,logMap_eq_fullLog]
    dsimp only [δ,extend]
    rw [dif_neg i.property]
  have hsum : δ w₀ + ∑ i : {w : InfinitePlace K // w ≠ w₀}, δ i.val = 0 := by
    rw [← Fintype.sum_eq_add_sum_subtype_ne δ w₀]
    dsimp only [δ]
    rw [Finset.sum_sub_distrib,extend_sum,fullLog_sum K (a : K) (RingOfIntegers.coe_ne_zero_iff.mpr ha)]
    simp
  refine ⟨a,ha,hanorm,?_,?_⟩
  · intro i
    rw [hid]
    dsimp only [δ]
    linarith [hfull i.val]
  · simp_rw [hid]
    have hh := hfull w₀
    dsimp only [δ] at hsum ⊢
    linarith

end MinkowskiLogCover


namespace RegulatorUpper
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators ENNReal NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

private theorem norm_span_eq (a : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {a}) : ℝ) = mixedEmbedding.norm (mixedEmbedding K (a : K)) := by
  rw [Ideal.absNorm_span_singleton,norm_eq_norm,← Algebra.coe_norm_int]
  simp

/-- Quantitative regulator upper bound from the explicit Minkowski volume
condition. All constants except the degree and unit rank are visible. -/
theorem regulator_upper_bound_of_minkowski (t : ℝ) (ht : 0 ≤ t) (B : ℕ)
    (hrank : 0 < NumberField.Units.rank K)
    (hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*t)))
    (hB : Real.exp ((Module.finrank ℚ K : ℝ)*t) ≤ (B : ℝ)) :
    NumberField.Units.regulator K ≤
      (2 : ℝ)^(Module.finrank ℚ K)*(B : ℝ)^2*(36*t)^(NumberField.Units.rank K) := by
  classical
  let Iset : Finset (Ideal (𝓞 K)) := ((Ideal.finite_setOf_absNorm_le B).toFinset).filter
    (fun I => ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I)
  have hgen : ∀ I : Iset, ∃ a : 𝓞 K, a ≠ 0 ∧ Ideal.span {a} = I.val :=
    fun I => (Finset.mem_filter.mp I.property).2
  choose gen hgen0 hgenspan using hgen
  let T : Finset (logSpace K) := Iset.attach.image
    (fun I => logMap (mixedEmbedding K (gen I : K)))
  have hIcard : Iset.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
    apply IdealCounting.card_le
    · intro I hI
      obtain ⟨a,ha,rfl⟩ := (Finset.mem_filter.mp hI).2
      exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
    · intro I hI
      simpa using (Finset.mem_filter.mp hI).1
  have hTcard : T.card ≤ 2^(Module.finrank ℚ K)*B^2 := by
    exact (Finset.card_image_le.trans_eq Finset.card_attach).trans hIcard
  have hcover : ∀ x : logSpace K, ∃ g : NumberField.Units.unitLattice K, ∃ z ∈ T,
      (g : logSpace K)+x-z ∈ SimplexVolume.simplex (2*t) := by
    intro x
    obtain ⟨a,ha,hanorm,haapprox⟩ := MinkowskiLogCover.exists_approximation K t ht hM x
    have hI : Ideal.span {a} ∈ Iset := by
      apply Finset.mem_filter.mpr
      refine ⟨(Set.Finite.mem_toFinset _).mpr ?_,a,ha,rfl⟩
      change Ideal.absNorm (Ideal.span {a}) ≤ B
      exact_mod_cast (show (Ideal.absNorm (Ideal.span {a}) : ℝ) ≤ B by
        rw [norm_span_eq]; exact hanorm.trans hB)
    let I : Iset := ⟨Ideal.span {a},hI⟩
    obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hgenspan I)
    have hmul : mixedEmbedding K (a : K) =
        mixedEmbedding K (u : K)*mixedEmbedding K (gen I : K) := by
      rw [← map_mul]
      congr 1
      have hh := congrArg (algebraMap (𝓞 K) K) hu
      simpa only [map_mul,mul_comm] using hh.symm
    have hn := MinkowskiLogCover.integer_norm_ge_one K (gen I) (hgen0 I)
    have hlog : logMap (mixedEmbedding K (a : K)) =
        NumberField.Units.logEmbedding K (Additive.ofMul u)+logMap (mixedEmbedding K (gen I : K)) := by
      rw [hmul,logMap_mul (by rw [norm_unit]; norm_num) ((lt_of_lt_of_le zero_lt_one hn).ne'),
        logMap_eq_logEmbedding]
    let lu : NumberField.Units.unitLattice K :=
      ⟨NumberField.Units.logEmbedding K (Additive.ofMul u),
        Submodule.mem_map.mpr ⟨Additive.ofMul u,Submodule.mem_top,rfl⟩⟩
    refine ⟨-lu,logMap (mixedEmbedding K (gen I : K)),?_,?_⟩
    · exact Finset.mem_image.mpr ⟨I,Finset.mem_attach _ _,rfl⟩
    · rw [hlog] at haapprox
      convert haapprox using 1
      change -(NumberField.Units.logEmbedding K (Additive.ofMul u))+x-
        logMap (mixedEmbedding K (gen I : K)) = _
      abel
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = NumberField.Units.rank K := by
    simpa using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
  letI : Nonempty {w : InfinitePlace K // w ≠ w₀} := Fintype.card_pos_iff.mp (hcard.symm ▸ hrank)
  have hc := LatticeCovering.covolume_le_of_simplex_cover (NumberField.Units.unitLattice K)
    T (2*t) (by positivity) hcover
  have hh : (T.card : ℝ) ≤ (2 : ℝ)^(Module.finrank ℚ K)*(B : ℝ)^2 := by exact_mod_cast hTcard
  apply hc.trans
  rw [hcard,show 18*(2*t) = 36*t by ring]
  exact mul_le_mul_of_nonneg_right hh (by positivity)


private theorem minkowskiBound_le (R : ℕ) (hR : 0 < R)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    minkowskiBound K 1 ≤ (2*(R : ℝ≥0∞))^(Module.finrank ℚ K) := by
  have hsqrt : (NNReal.sqrt ‖NumberField.discr K‖₊ : ℝ≥0∞) ≤ (R : ℝ≥0∞)^(Module.finrank ℚ K) := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    have hh : Real.sqrt |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(Module.finrank ℚ K) :=
      Real.sqrt_le_iff.mpr ⟨by positivity,by simpa only [← pow_mul,mul_comm 2] using hD⟩
    simpa [Real.coe_sqrt,Int.norm_eq_abs] using hh
  rw [minkowskiBound,volume_fundamentalDomain_fractionalIdealLatticeBasis,
    volume_fundamentalDomain_latticeBasis,mixedEmbedding.finrank]
  simp only [Units.val_one,FractionalIdeal.absNorm_one,Rat.cast_one,ENNReal.ofReal_one,one_mul]
  have hi : (2⁻¹ : ℝ≥0∞)^(nrComplexPlaces K) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
  calc
    _ ≤ (1*(R : ℝ≥0∞)^(Module.finrank ℚ K))*2^(Module.finrank ℚ K) := by gcongr
    _ = _ := by rw [one_mul,mul_pow,mul_comm]

/-- Uniform exponential regulator upper bound for fields of bounded root
discriminant, with an explicit (nonoptimal) constant. -/
theorem regulator_upper_bound_of_discriminant (R : ℕ) (hR : 0 < R)
    (hrank : 0 < NumberField.Units.rank K)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hT : (0 : ℝ) < 4*R := by positivity
  have hT1 : (1 : ℝ) ≤ 4*R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have ht : 0 ≤ Real.log (4*R : ℝ) := Real.log_nonneg hT1
  have hexp : Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ)) = (4*R : ℝ)^(Module.finrank ℚ K) := by
    rw [Real.exp_nat_mul,Real.exp_log hT]
  have hM : minkowskiBound K 1 < convexBodyLTFactor K *
      ENNReal.ofReal (Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ))) := by
    rw [hexp]
    have hpow : (2*(R : ℝ))^(Module.finrank ℚ K) < (4*(R : ℝ))^(Module.finrank ℚ K) :=
      pow_lt_pow_left₀ (by linarith) (by positivity) Module.finrank_pos.ne'
    have hpow' : (2*(R : ℝ≥0∞))^(Module.finrank ℚ K) < ENNReal.ofReal ((4*R : ℝ)^(Module.finrank ℚ K)) := by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      simpa [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*R : ℝ)^(Module.finrank ℚ K))] using hpow
    have hfac : (1 : ℝ≥0∞) ≤ convexBodyLTFactor K := by exact_mod_cast one_le_convexBodyLTFactor K
    exact (minkowskiBound_le K R hR hD).trans_lt (hpow'.trans_le (le_mul_of_one_le_left (by positivity) hfac))
  have hB : Real.exp ((Module.finrank ℚ K : ℝ)*Real.log (4*R : ℝ)) ≤ ((4*R)^(Module.finrank ℚ K) : ℕ) := by
    rw [hexp]
    push_cast
    rfl
  have h := regulator_upper_bound_of_minkowski K (Real.log (4*R : ℝ)) ht
    ((4*R)^(Module.finrank ℚ K)) hrank hM hB
  have hrankle : NumberField.Units.rank K ≤ Module.finrank ℚ K := by
    have hc := card_add_two_mul_card_eq_rank K
    simp only [NumberField.Units.rank,card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  have hlog : 36*Real.log (4*R : ℝ) ≤ 144*R := by linarith [Real.log_le_sub_one_of_pos hT]
  have hbase : (1 : ℝ) ≤ 144*R := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hfactor : (36*Real.log (4*R : ℝ))^(NumberField.Units.rank K) ≤
      (144*R : ℝ)^(Module.finrank ℚ K) :=
    (pow_le_pow_left₀ (by positivity) hlog _).trans (pow_le_pow_right₀ hbase hrankle)
  apply h.trans
  push_cast
  calc
    _ ≤ (2 : ℝ)^(Module.finrank ℚ K)*((4*R : ℝ)^(Module.finrank ℚ K))^2*
        (144*R : ℝ)^(Module.finrank ℚ K) := mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
      rw [pow_right_comm,← mul_pow,← mul_pow]
      congr 1
      ring


/-- The rank-zero case included. -/
theorem regulator_upper_bound (R : ℕ) (hR : 0 < R)
    (hD : |(NumberField.discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    NumberField.Units.regulator K ≤ (4608*(R : ℝ)^3)^(Module.finrank ℚ K) := by
  by_cases hr : NumberField.Units.rank K = 0
  · have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = 0 := by
      simpa [hr] using (Fintype.card_congr (NumberField.Units.equivFinRank K)).symm
    letI : IsEmpty {w : InfinitePlace K // w ≠ w₀} := Fintype.card_eq_zero_iff.mp hcard
    have hreg : NumberField.Units.regulator K = 1 := by
      unfold NumberField.Units.regulator
      rw [ZLattice.covolume_eq_det _ (IsZLattice.basis _),Matrix.det_isEmpty,abs_one]
    rw [hreg]
    apply one_le_pow₀
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hR1 3
    norm_num at hh
    linarith
  · exact regulator_upper_bound_of_discriminant K R hR (Nat.pos_of_ne_zero hr) hD

end RegulatorUpper


/- Additive-energy bounds for isosceles-free sets and a finite family of
same-length directions. These are auxiliary bounds, not a settlement of
Erdős 1207. -/

open scoped Pointwise Combinatorics.Additive ComplexConjugate
namespace DirectionCounting

set_option maxHeartbeats 1000000

/-- The energy counts the returning two-step walks, grouped by their start. -/
theorem energy_eq_walk_sum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A U : Finset G) :
    E[A,U] = ∑ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card := by
  classical
  rw [Finset.addEnergy, Finset.card_filter]
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := A) (t := U)]
  simp only [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have he (b : G) : a + u = b + v ↔ b = a + u - v := by
    constructor
    · intro h; exact eq_sub_iff_add_eq.mpr h.symm
    · intro h; exact (eq_sub_iff_add_eq.mp h).symm
  simp_rw [he]
  simp

/-- A bound on returning walks, combined with a sumset bound, bounds the set. -/
theorem card_bound_of_walks {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A U : Finset G) (L : ℕ)
    (h : ∀ a ∈ A, ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤ L) :
    U.card ^ 2 * A.card ≤ (A + U).card * L := by
  have he : E[A,U] ≤ A.card * L := by
    rw [energy_eq_walk_sum]
    simpa using Finset.sum_le_sum (fun a ha => h a ha)
  have hc := Finset.le_card_add_mul_addEnergy A U
  have hh := hc.trans (Nat.mul_le_mul_left (A + U).card he)
  by_cases ha : A.card = 0
  · simp [ha]
  have hp : 0 < A.card := Nat.pos_of_ne_zero ha
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh]

/-- Two circles of equal radius have at most two points of intersection.
The second point is written explicitly, avoiding any nondegeneracy of the
radius itself. -/
theorem equal_chord_start (u p w : ℂ) (hw : w ≠ 0)
    (h₁ : ‖u‖ = ‖p‖) (h₂ : ‖u - w‖ = ‖u‖)
    (h₃ : ‖p - w‖ = ‖p‖) : p = u ∨ p = w - u := by
  have hn₁ : u * conj u = p * conj p := by rw [Complex.mul_conj', Complex.mul_conj', h₁]
  have hn₂ : (u-w) * conj (u-w) = u * conj u := by
    rw [Complex.mul_conj', Complex.mul_conj', h₂]
  have hn₃ : (p-w) * conj (p-w) = p * conj p := by
    rw [Complex.mul_conj', Complex.mul_conj', h₃]
  simp only [map_sub] at hn₂ hn₃
  have hh : (p-u) * (p+u-w) * conj w = 0 := by
    linear_combination u * hn₂ - p * hn₃ + w * hn₁
  have hw' : conj w ≠ 0 := by simpa using hw
  have hz := (mul_eq_zero.mp hh).resolve_right hw'
  rcases mul_eq_zero.mp hz with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

/-- A nonzero chord has at most two ordered realizations on a fixed circle. -/
theorem chord_fiber_card_le_two (U : Finset ℂ) (r : ℝ)
    (hU : ∀ u ∈ U, ‖u‖ = r) (w : ℂ) (hw : w ≠ 0) :
    ((U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)).card ≤ 2 := by
  classical
  let F := (U ×ˢ U).filter (fun uv => uv.1 - uv.2 = w)
  by_cases he : F.Nonempty
  · obtain ⟨⟨u,v⟩, huv⟩ := he
    simp only [F, Finset.mem_filter, Finset.mem_product] at huv
    obtain ⟨⟨hu,hv⟩, huv'⟩ := huv
    have hs : F ⊆ {(u,v),(-v,-u)} := by
      rintro ⟨p,q⟩ hpq
      simp only [F, Finset.mem_filter, Finset.mem_product] at hpq
      obtain ⟨⟨hp,hq⟩, hpq'⟩ := hpq
      have hv' : u-w = v := by rw [← huv']; abel
      have hq' : p-w = q := by rw [← hpq']; abel
      have hc := equal_chord_start u p w hw
        ((hU u hu).trans (hU p hp).symm)
        (by rw [hv', hU v hv, hU u hu])
        (by rw [hq', hU q hq, hU p hp])
      rcases hc with hc | hc
      · have hqv : q = v := by rw [← hq', hc, hv']
        simp [hc,hqv]
      · have hpv : p = -v := by rw [hc, ← huv']; abel
        have hqu : q = -u := by rw [← hq', hc]; abel
        simp [hpv,hqu]
    exact (Finset.card_le_card hs).trans Finset.card_le_two
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    change F.card ≤ 2
    simp [hz]

/-- From a selected apex, a nonzero distance identifies at most one selected
endpoint. -/
theorem pinned_unique (A : Finset ℂ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    {a w v : ℂ} (ha : a ∈ A) (hw : w ≠ 0) (hv : v ≠ 0)
    (haw : a+w ∈ A) (hav : a+v ∈ A) (hn : ‖w‖ = ‖v‖) : w = v := by
  by_contra hne
  apply hA ha haw hav
    (by simpa using hw)
    (by simpa using hne)
    (by simpa using hv)
  apply Or.inr ∘ Or.inr
  simpa only [dist_self_add_left, dist_self_add_right] using hn.symm

/-- If the directions have a common length and use at most `C.card` different
nonzero chord lengths, there are at most `U.card + 2*C.card` returning walks
from each selected point. -/
theorem walk_bound (A U : Finset ℂ) (r : ℝ) (C : Finset ℝ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    (hU : ∀ u ∈ U, ‖u‖ = r)
    (hC : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C)
    {a : ℂ} (ha : a ∈ A) :
    ((U ×ˢ U).filter (fun uv => a + uv.1 - uv.2 ∈ A)).card ≤
      U.card + 2 * C.card := by
  classical
  let E := (U ×ˢ U).filter (fun uv => uv.1 ≠ uv.2 ∧ a+uv.1-uv.2 ∈ A)
  let color : ℂ × ℂ → ℝ := fun uv => ‖uv.1-uv.2‖
  have hf (c : ℝ) (hc : c ∈ E.image color) :
      (E.filter (fun uv => color uv = c)).card ≤ 2 := by
    obtain ⟨⟨u,v⟩, huv, he⟩ := Finset.mem_image.mp hc
    have huv' := huv
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv'
    have hw : u-v ≠ 0 := sub_ne_zero.mpr huv'.2.1
    have hs : E.filter (fun uv => color uv = c) ⊆
        (U ×ˢ U).filter (fun uv => uv.1 - uv.2 = u-v) := by
      rintro ⟨p,q⟩ hpq
      obtain ⟨hpq,hcol⟩ := Finset.mem_filter.mp hpq
      simp only [E, Finset.mem_filter, Finset.mem_product] at hpq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr hpq.1, ?_⟩
      apply pinned_unique A hA ha (sub_ne_zero.mpr hpq.2.1) hw
      · simpa only [add_sub_assoc] using hpq.2.2
      · simpa only [add_sub_assoc] using huv'.2.2
      · exact hcol.trans he.symm
    exact (Finset.card_le_card hs).trans (chord_fiber_card_le_two U r hU (u-v) hw)
  have hi : E.image color ⊆ C := by
    intro c hc
    obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hc
    simp only [E, Finset.mem_filter, Finset.mem_product] at huv
    exact hC u huv.1.1 v huv.1.2 huv.2.1
  have he : E.card ≤ 2 * C.card :=
    (Finset.card_le_mul_card_image E 2 hf).trans
      (Nat.mul_le_mul_left 2 (Finset.card_le_card hi))
  have hs : (U ×ˢ U).filter (fun uv => a+uv.1-uv.2 ∈ A) ⊆ U.diag ∪ E := by
    rintro ⟨u,v⟩ huv
    obtain ⟨huv,hmem⟩ := Finset.mem_filter.mp huv
    by_cases h : u = v
    · subst v
      exact Finset.mem_union_left _ (by simpa using (Finset.mem_product.mp huv).1)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huv,h,hmem⟩)
  calc
    _ ≤ (U.diag ∪ E).card := Finset.card_le_card hs
    _ ≤ U.diag.card + E.card := Finset.card_union_le _ _
    _ ≤ U.card + 2*C.card := by simpa using Nat.add_le_add_left he U.card

/-- The resulting energy bound, with the enlargement cost explicitly visible. -/
theorem isosceles_free_bound (A U : Finset ℂ) (r : ℝ) (C : Finset ℝ)
    (hA : (A : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z)
    (hU : ∀ u ∈ U, ‖u‖ = r)
    (hC : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ C) :
    U.card^2 * A.card ≤ (A+U).card * (U.card + 2*C.card) :=
  card_bound_of_walks A U _ (fun _ ha => walk_bound A U r C hA hU hC ha)


end DirectionCounting


namespace SumsetGrowth
open scoped Pointwise

/-- Exponential growth eventually exceeds the fixed-degree packing bound,
with a deliberately generous explicit cutoff. -/
theorem growth_cutoff (C : ℕ) : C * (4*C+5) < 2^(4*C+4) := by
  have hC : C+1 ≤ 2^C := Nat.lt_two_pow_self
  have hpow : (C+1)^2 ≤ (2^C)^2 := Nat.pow_le_pow_left hC 2
  have hbound : C*(4*C+5) < 8*(C+1)^2 := by nlinarith
  have hexp : 2*C+3 ≤ 4*C+4 := by omega
  calc
    C*(4*C+5) < 8*(C+1)^2 := hbound
    _ ≤ 8*(2^C)^2 := Nat.mul_le_mul_left 8 hpow
    _ = 2^(2*C+3) := by rw [pow_add, pow_mul']; norm_num; ring
    _ ≤ 2^(4*C+4) := Nat.pow_le_pow_right (by norm_num) hexp

/-- A polynomial packing bound forces a small enlargement at a bounded step.
No measure or lattice fundamental domain is used. -/
theorem exists_small_step (f : ℕ → ℕ) (C d : ℕ) (hd : 0 < d)
    (hf : 0 < f 0) (hbound : f (4*C+4) ≤ (C*(4*C+5))^d) :
    ∃ j < 4*C+4, f (j+1) ≤ 2^d * f j := by
  by_contra! h
  have hlow : ∀ j ≤ 4*C+4, (2^d)^j ≤ f j := by
    intro j hj
    induction j with
    | zero => simpa using hf
    | succ j ih =>
      have hj' : j < 4*C+4 := by omega
      calc
        (2^d)^(j+1) = 2^d * (2^d)^j := by rw [pow_succ'];
        _ ≤ 2^d * f j := Nat.mul_le_mul_left _ (ih (by omega))
        _ ≤ f (j+1) := (h j hj').le
  have hlt := Nat.pow_lt_pow_left (growth_cutoff C) (Nat.ne_of_gt hd)
  have hcomm : (2^d)^(4*C+4) = (2^(4*C+4))^d := by rw [← pow_mul, ← pow_mul, mul_comm d]
  have hh := (hlow _ le_rfl).trans hbound
  rw [hcomm] at hh
  exact hlt.not_ge hh

/-- The finite geometric reduction with explicit exponential constants. -/
theorem configuration_of_directions (U : Finset ℂ) (K C d : ℕ)
    (hd : 0 < d) (hK : 0 < K)
    (hunit : ∀ u ∈ U, ‖u‖ = 1)
    (hlarge : (16*K)^d ≤ U.card)
    (hquot : (U/U).card ≤ K^d * U.card)
    (hpacking : ∀ j ≤ 4*C+4, (j • U).card ≤ (C*(j+1))^d) :
    ∃ S : Finset ℂ, S.Nonempty ∧ S.card ≤ (C*(4*C+5))^d ∧
      ∀ A : Finset ℂ, A ⊆ S →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) →
        2^d * A.card ≤ S.card := by
  classical
  obtain ⟨j,hj,hstep⟩ := exists_small_step (fun j => (j • U).card) C d hd
    (by simp) (by simpa only [Nat.add_assoc] using hpacking (4*C+4) le_rfl)
  have hU : U.Nonempty := Finset.card_pos.mp ((by positivity : 0 < (16*K)^d).trans_le hlarge)
  let S : Finset ℂ := j • U
  have hS : S.Nonempty := by
    exact Finset.Nonempty.nsmul hU
  refine ⟨S,hS,(hpacking j hj.le).trans ?_,?_⟩
  · exact Nat.pow_le_pow_left (Nat.mul_le_mul_left C (by omega)) d
  intro A hAS hA
  let colors : Finset ℝ := (U/U).image (fun w => ‖1-w‖)
  have hc : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ‖u-v‖ ∈ colors := by
    intro u hu v hv _
    have hv0 : v ≠ 0 := by intro hv0; simpa [hv0] using hunit v hv
    have heq : ‖u-v‖ = ‖1-u/v‖ := by
      calc
        ‖u-v‖ = ‖(u/v-1)*v‖ := by congr 1; field_simp
        _ = ‖u/v-1‖ := by rw [norm_mul, hunit v hv, mul_one]
        _ = ‖1-u/v‖ := norm_sub_rev _ _
    rw [heq]
    exact Finset.mem_image.mpr ⟨u/v,Finset.div_mem_div hu hv,rfl⟩
  have hcol : colors.card ≤ K^d * U.card := (Finset.card_image_le).trans hquot
  have he := DirectionCounting.isosceles_free_bound A U 1 colors hA hunit hc
  have hadd : (A+U).card ≤ 2^d * S.card := by
    calc
      (A+U).card ≤ (S+U).card := Finset.card_le_card (Finset.add_subset_add hAS subset_rfl)
      _ = ((j+1) • U).card := by rw [add_nsmul, one_nsmul]
      _ ≤ 2^d * S.card := hstep
  have he' : U.card^2 * A.card ≤ 2^d * S.card * ((1+2*K^d)*U.card) :=
    he.trans (Nat.mul_le_mul hadd (by nlinarith [hcol]))
  have he'' : U.card * A.card ≤ 2^d * S.card * (1+2*K^d) := by
    apply (Nat.mul_le_mul_right_iff (Finset.card_pos.mpr hU)).mp
    nlinarith [he']
  have hKpow : 1 ≤ K^d := Nat.one_le_pow _ _ hK
  have hfour : 4 ≤ 4^d := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 4) hd
  have hcoef : 2^d * (2^d * (1+2*K^d)) ≤ U.card := by
    apply le_trans _ hlarge
    rw [mul_pow]
    have h16 : (16 : ℕ)^d = 2^d * 2^d * 4^d := by
      rw [← mul_pow, ← mul_pow]; norm_num
    rw [h16]
    calc
      _ = (2^d * 2^d) * (1+2*K^d) := by ring
      _ ≤ (2^d * 2^d) * (4^d * K^d) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have hh := Nat.mul_le_mul_right A.card hcoef
  have hh' := hh.trans he''
  have hp : 0 < 2^d * (1+2*K^d) := by positivity
  apply (Nat.mul_le_mul_right_iff hp).mp
  nlinarith [hh']

end SumsetGrowth


/-
# Erdős Problem 1207

*Reference:* [erdosproblems.com/1207](https://www.erdosproblems.com/1207)
-/

open Filter

namespace Erdos1207

/-- A finite configuration supplies an upper bound for `P`. -/
theorem P_le_of_configuration {d n m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : S.card = n)
    (h : ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m := by
  unfold P
  refine le_trans (Nat.sInf_le ⟨S, hS, rfl⟩) ?_
  apply csSup_le'
  rintro k ⟨A, hAS, hA, rfl⟩
  exact h A hAS hA

private theorem exists_injective_polynomial_eval {ι : Type*} [Fintype ι]
    (p : ι → Polynomial ℂ) (hp : Function.Injective p) :
    ∃ t : ℂ, Function.Injective (fun i => (p i).eval t) := by
  classical
  let q : Polynomial ℂ := ∏ ij ∈ (Finset.univ : Finset ι).offDiag, (p ij.1 - p ij.2)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ij hij
    exact sub_ne_zero.mpr (hp.ne (Finset.mem_offDiag.mp hij).2.2)
  obtain ⟨t, ht⟩ : ∃ t : ℂ, q.eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hq (Polynomial.funext (by simpa using h))
  refine ⟨t, fun i j hij => ?_⟩
  by_contra hne
  apply ht
  dsimp only [q]
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := (i,j))
  · simp [hne]
  · simp [hij]

/-- Larger configurations can be trimmed to any prescribed smaller size. -/
private theorem P_le_of_large_configuration {d n m : ℕ}
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hn : n ≤ S.card)
    (h : ∀ A : Finset (EuclideanSpace ℝ (Fin d)), A ⊆ S →
      IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) → A.card ≤ m) :
    P d n ≤ m := by
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hn
  exact P_le_of_configuration T hT fun A hAT hA => h A (hAT.trans hTS) hA


/- Disjoint translated copies preserve extremal upper bounds. This is a
replication lemma, not a submultiplicativity theorem or a power saving. -/

private theorem exists_injective_copies (S : Finset ℂ) (q : ℕ) :
    ∃ t : ℂ, Function.Injective
      (fun p : Fin q × S => (p.2 : ℂ) + (p.1.val : ℂ)*t) := by
  classical
  let p : Fin q × S → Polynomial ℂ := fun a =>
    Polynomial.C (a.2 : ℂ) + Polynomial.monomial 1 (a.1.val : ℂ)
  have hp : Function.Injective p := by
    intro a b hab
    have h0 := congrArg (fun f : Polynomial ℂ => f.coeff 0) hab
    have h1 := congrArg (fun f : Polynomial ℂ => f.coeff 1) hab
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C_zero,
      Polynomial.coeff_monomial, one_ne_zero, ↓reduceIte, add_zero] at h0
    simp only [p, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial,
      one_ne_zero, ↓reduceIte, zero_add, Nat.cast_inj] at h1
    exact Prod.ext (Fin.ext h1) (Subtype.ext h0)
  obtain ⟨t,ht⟩ := exists_injective_polynomial_eval p hp
  refine ⟨t, ?_⟩
  simpa only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_monomial,
    pow_one] using ht

/-- Replicate a complex configuration using disjoint translations. -/
theorem exists_replicated_configuration (S : Finset ℂ) (q M : ℕ)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    ∃ T : Finset ℂ, T.card = q*S.card ∧
      ∀ A : Finset ℂ, A ⊆ T →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ q*M := by
  classical
  obtain ⟨t,ht⟩ := exists_injective_copies S q
  let f : Fin q × S → ℂ := fun p => (p.2 : ℂ) + (p.1.val : ℂ)*t
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ht]
    simp
  intro A hAS hA
  obtain ⟨B,hB,rfl⟩ := Finset.subset_image_iff.mp hAS
  rw [Finset.card_image_of_injective _ ht]
  have hrow (i : Fin q) : (B.filter (fun p => p.1 = i)).card ≤ M := by
    let D := B.filter (fun p => p.1 = i)
    let C := D.image (fun p => (p.2 : ℂ))
    have hCsub : C ⊆ S := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact p.2.property
    have hmem (x : ℂ) (hx : x ∈ C) : x+(i.val : ℂ)*t ∈ B.image f := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
      have he : f p = (p.2 : ℂ) + (i.val : ℂ)*t := by simp [f,hi]
      exact he ▸ Finset.mem_image_of_mem f hp
    have hCfree : (C : Set ℂ).Triplewise fun x y z => ¬ IsIsosceles x y z := by
      intro x hx y hy z hz hxy hyz hxz hiso
      apply hA (hmem x hx) (hmem y hy) (hmem z hz)
        (by simpa using hxy) (by simpa using hyz) (by simpa using hxz)
      simpa only [IsIsosceles, dist_add_right] using hiso
    have hinj : Set.InjOn (fun p : Fin q × S => (p.2 : ℂ)) (D : Set (Fin q × S)) := by
      intro p hp r hr he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)
        (Subtype.ext he)
    have hc := hS C hCsub hCfree
    dsimp only [C] at hc
    rwa [Finset.card_image_of_injOn hinj] at hc
  have he : B.card = ∑ i : Fin q, (B.filter (fun p => p.1 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (by
      intro p hp
      exact Finset.mem_univ p.1)
  rw [he]
  calc
    _ ≤ ∑ _i : Fin q, M := Finset.sum_le_sum (fun i _ => hrow i)
    _ = q*M := by simp

/-- A complex configuration transfers to the original planar extremal function. -/
theorem P_two_le_of_complex_configuration (S : Finset ℂ) (n M : ℕ)
    (hn : n ≤ S.card)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    P 2 n ≤ M := by
  classical
  let e := Complex.orthonormalBasisOneI.repr
  apply P_le_of_large_configuration (S.image e)
  · simpa only [Finset.card_image_of_injective _ e.injective] using hn
  · intro A hAS hA
    obtain ⟨B,hB,rfl⟩ := Finset.subset_image_iff.mp hAS
    rw [Finset.card_image_of_injective _ e.injective]
    apply hS B hB
    intro a ha b hb c hc hab hbc hac hiso
    apply hA (Finset.mem_image_of_mem _ ha) (Finset.mem_image_of_mem _ hb)
      (Finset.mem_image_of_mem _ hc) (e.injective.ne hab) (e.injective.ne hbc)
      (e.injective.ne hac)
    simpa only [IsIsosceles, e.dist_map] using hiso

/-- Repetition fills size gaps at a cost of at most one extra copy. This does
not assert that arbitrary additional points preserve an extremal bound. -/
theorem P_two_bound_by_replication (S : Finset ℂ) (hSpos : S.Nonempty) (M n : ℕ)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ (n + S.card) * M := by
  classical
  let q := n / S.card + 1
  obtain ⟨T,hT,hbound⟩ := exists_replicated_configuration S q M hS
  have hn : n ≤ T.card := by
    rw [hT, mul_comm]
    exact (Nat.lt_mul_div_succ n hSpos.card_pos).le
  have hp := P_two_le_of_complex_configuration T n (q*M) hn hbound
  calc
    S.card * P 2 n ≤ S.card * (q*M) := Nat.mul_le_mul_left _ hp
    _ = (S.card * (n / S.card) + S.card) * M := by dsimp [q]; ring
    _ ≤ (n+S.card)*M := by
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le n S.card) _)

/-- Once n is at least the model size, replication loses at most a factor 2
in density. -/
theorem P_two_density_by_replication (S : Finset ℂ) (hSpos : S.Nonempty) (M n : ℕ)
    (hn : S.card ≤ n)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → A.card ≤ M) :
    S.card * P 2 n ≤ 2*n*M := by
  have h := P_two_bound_by_replication S hSpos M n hS
  exact h.trans (Nat.mul_le_mul_right M (by omega))

/-- A weighted density bound also survives repetition with only a factor 2. -/
theorem P_two_weighted_density_replication (S : Finset ℂ) (hSpos : S.Nonempty)
    (L n : ℕ) (hn : S.card ≤ n)
    (hS : ∀ A : Finset ℂ, A ⊆ S →
      (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) → L*A.card ≤ S.card) :
    L * P 2 n ≤ 2*n := by
  by_cases hL : L = 0
  · simp [hL]
  have hLpos := Nat.pos_of_ne_zero hL
  have h := P_two_density_by_replication S hSpos (S.card/L) n hn (by
    intro A hAS hA
    rw [Nat.le_div_iff_mul_le hLpos]
    simpa only [mul_comm] using hS A hAS hA)
  apply Nat.le_of_mul_le_mul_left (c := S.card) _ hSpos.card_pos
  calc
    S.card * (L * P 2 n) = L * (S.card * P 2 n) := by ring
    _ ≤ L * (2*n*(S.card/L)) := Nat.mul_le_mul_left L h
    _ = (2*n) * (L*(S.card/L)) := by ring
    _ ≤ (2*n) * S.card := Nat.mul_le_mul_left _ (Nat.mul_div_le S.card L)
    _ = S.card * (2*n) := by ring

private theorem power_saving_arithmetic (H d a n : ℕ)
    (hH : 0 < H) (hd : 3 ≤ d) (hn : 0 < n)
    (ha : 2^d * a ≤ 2*n) (hb : n ≤ 2^(2*H*d)) :
    (a : ℝ) < (n : ℝ)^(1 - 1/(4*H : ℝ)) := by
  let L := 4*H
  have hL : 0 < L := by dsimp [L]; omega
  have he : L+2*H*d < d*L := by dsimp [L]; nlinarith
  have hc : 2^L * 2^(2*H*d) < 2^(d*L) := by
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) he
  have hp : 2^(d*L) * a^L ≤ 2^L * n^L := by
    simpa only [mul_pow, ← pow_mul] using Nat.pow_le_pow_left ha L
  have hx : 2^(d*L) * (a^L*n) < 2^(d*L) * n^L := by
    calc
      _ = (2^(d*L) * a^L) * n := by ring
      _ ≤ (2^L * n^L) * n := Nat.mul_le_mul_right n hp
      _ = (2^L*n) * n^L := by ring
      _ ≤ (2^L * 2^(2*H*d)) * n^L :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
      _ < _ := Nat.mul_lt_mul_of_pos_right hc (pow_pos hn L)
  have hx' : a^L*n < n^L := (Nat.mul_lt_mul_left (by positivity : 0 < 2^(d*L))).mp hx
  have heL : L = (L-1)+1 := by omega
  have hnat : a^L < n^(L-1) := by
    have hen : n^L = n^(L-1)*n := by
      calc
        n^L = n^((L-1)+1) := congrArg (fun t : ℕ => n^t) heL
        _ = _ := pow_succ n (L-1)
    rw [hen] at hx'
    exact (Nat.mul_lt_mul_right hn).mp hx'
  have hreal : (a : ℝ)^L < (n : ℝ)^(L-1) := by exact_mod_cast hnat
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hexp : (1-1/(4*H : ℝ))*(L : ℝ) = ((L-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one]
    have heq : (4*H : ℝ) = L := by simp [L]
    rw [heq]
    field_simp
  have hpow : ((n : ℝ)^(1-1/(4*H : ℝ)))^L = (n : ℝ)^(L-1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hexp, Real.rpow_natCast]
  by_contra h
  have hle : (n : ℝ)^(1-1/(4*H : ℝ)) ≤ a := le_of_not_gt h
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hle L
  rw [hpow] at hh
  exact hreal.not_ge hh

/-- Precise sufficient configuration hypothesis for a tower whose degrees
increase by factors of 2. The hypothesis is NOT established here. -/
theorem power_saving_of_doubly_exponential_configurations
    (H : ℕ) (hH : 0 < H)
    (h : ∀ m : ℕ, ∃ S : Finset ℂ, S.Nonempty ∧ S.card ≤ 2^(H*2^m) ∧
      ∀ A : Finset ℂ, A ⊆ S →
        (A : Set ℂ).Triplewise (fun x y z => ¬ IsIsosceles x y z) →
          2^(2^m) * A.card ≤ S.card) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  refine ⟨1/(4*H : ℝ), by positivity, Filter.eventually_atTop.2 ⟨2^(4*H), ?_⟩⟩
  intro n hn
  have hnpos : 0 < n := (by positivity : 0 < 2^(4*H)).trans_le hn
  let l := Nat.log 2 n
  let q := l/H
  let m := Nat.log 2 q
  let d := 2^m
  have hl : 4*H ≤ l := Nat.le_log_of_pow_le (by norm_num) hn
  have hq : 4 ≤ q := (Nat.le_div_iff_mul_le hH).mpr (by simpa only [mul_comm] using hl)
  have hm : 2 ≤ m := Nat.le_log_of_pow_le (by norm_num) (by norm_num; exact hq)
  have hd : 3 ≤ d := by
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 2) hm
    norm_num at hh
    exact (by norm_num : 3 ≤ 4).trans hh
  have hdq : d ≤ q := Nat.pow_log_le_self 2 (by omega)
  have hqhigh : q+1 ≤ 2*d := by
    have hh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
    simpa only [pow_succ, mul_comm, Nat.lt_iff_add_one_le] using hh
  have hsmall : H*d ≤ l :=
    (Nat.mul_le_mul_left H hdq).trans (Nat.mul_div_le l H)
  have hlarge : l+1 ≤ 2*H*d := by
    have hh := Nat.lt_mul_div_succ l hH
    have hh' := Nat.mul_le_mul_left H hqhigh
    have : l < H*(2*d) := hh.trans_le hh'
    nlinarith
  obtain ⟨S,hSpos,hScard,hS⟩ := h m
  have hSn : S.card ≤ n := hScard.trans
    ((Nat.pow_le_pow_right (by norm_num : 0 < 2) hsmall).trans
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos)))
  have ha := P_two_weighted_density_replication S hSpos (2^d) n hSn hS
  have hb : n ≤ 2^(2*H*d) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hlarge)
  exact power_saving_arithmetic H d (P 2 n) n hH hd hnpos ha hb

end Erdos1207


namespace Erdos1207
open scoped Pointwise

/-- A purely finite sufficient condition for the original conjecture. The
existence of the direction sets in the premise is NOT established here. -/
theorem power_saving_of_unit_directions (K C : ℕ) (hK : 0 < K)
    (h : ∀ m : ℕ, ∃ U : Finset ℂ,
      (∀ u ∈ U, ‖u‖ = 1) ∧
      (16*K)^(2^m) ≤ U.card ∧
      (U/U).card ≤ K^(2^m) * U.card ∧
      ∀ j ≤ 4*C+4, (j • U).card ≤ (C*(j+1))^(2^m)) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  let H := C*(4*C+5)+1
  apply power_saving_of_doubly_exponential_configurations H (by dsimp [H]; omega)
  intro m
  obtain ⟨U,hunit,hlarge,hquot,hpacking⟩ := h m
  obtain ⟨S,hSpos,hScard,hS⟩ := SumsetGrowth.configuration_of_directions U K C (2^m)
    (by positivity) hK hunit hlarge hquot hpacking
  refine ⟨S,hSpos,hScard.trans ?_,hS⟩
  rw [pow_mul]
  exact Nat.pow_le_pow_left (by
    have hh := Nat.lt_two_pow_self (n := H)
    dsimp [H] at *
    omega) _

end Erdos1207

namespace Erdos1207
open NumberField
open scoped Classical Pointwise

/-- Uniform exponential regulator bounds for a family of suitable quadratic
extensions imply the exact original conjecture. The hypotheses on the fields
are substantive and are not proved here. -/
theorem power_saving_of_quadratic_field_family
    (K L : ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hreg : ∀ m, NumberField.Units.regulator (L m) ≤ (R : ℝ)^(Module.finrank ℚ (L m)))
    (hrel : ∀ m, Module.finrank (K m) (L m) = 2)
    (hgap : ∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex : ∀ m, ∃ σ : L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  let C := 4*UniformDirections.houseBound R ((16*500)^2)+1
  let H := (C*(4*C+5)+1)*2*D
  have hD : 0 < D := by have hh := hdegree 0; norm_num at hh; omega
  have hH : 0 < H := by dsimp [H]; positivity
  apply power_saving_of_doubly_exponential_configurations H hH
  intro m
  obtain ⟨σ,hσ⟩ := hcomplex m
  obtain ⟨U,hunit,hlarge,hdiv,hpacking⟩ := UniformDirections.exists_directions (K m) (L m) R hR
    (hreg m) (hrel m) (hgap m) σ hσ
  obtain ⟨S,hSpos,hScard,hS⟩ := SumsetGrowth.configuration_of_directions U 500 C
    (2*Module.finrank ℚ (L m)) (by have hh : 0 < Module.finrank ℚ (L m) := Module.finrank_pos; positivity) (by norm_num)
    hunit hlarge hdiv (fun j _ => hpacking j)
  refine ⟨S,hSpos,?_,?_⟩
  · calc
      S.card ≤ (C*(4*C+5))^(2*Module.finrank ℚ (L m)) := hScard
      _ ≤ (C*(4*C+5))^(2*(D*2^m)) := Nat.pow_le_pow_right (by dsimp [C]; positivity) (Nat.mul_le_mul_left 2 (hdegree m).2)
      _ ≤ (2^(C*(4*C+5)+1))^(2*(D*2^m)) := Nat.pow_le_pow_left (by
        have hh := Nat.lt_two_pow_self (n := C*(4*C+5)+1)
        omega) _
      _ = 2^(H*2^m) := by rw [← pow_mul]; congr 1; dsimp [H]; ring
  · intro A hAS hA
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by have hh := (hdegree m).1; omega))).trans
      (hS A hAS hA)

/-- Bounded root discriminant suffices for the regulator hypothesis in the
preceding conditional criterion. -/
theorem power_saving_of_bounded_discriminant_family
    (K L : ℕ → Type*) [∀ m, Field (K m)] [∀ m, Field (L m)]
    [∀ m, NumberField (K m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra (K m) (L m)] [∀ m, FiniteDimensional (K m) (L m)]
    [∀ m, IsTotallyReal (K m)]
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (L m) ∧ Module.finrank ℚ (L m) ≤ D*2^m)
    (hdisc : ∀ m, |(NumberField.discr (L m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (L m)))
    (hrel : ∀ m, Module.finrank (K m) (L m) = 2)
    (hgap : ∀ m, 4*NumberField.Units.rank (K m)+Module.finrank ℚ (L m) ≤ 4*NumberField.Units.rank (L m))
    (hcomplex : ∀ m, ∃ σ : L m →+* ℂ, ¬ ComplexEmbedding.IsReal σ) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  apply power_saving_of_quadratic_field_family K L (4608*R^3) D (by positivity) hdegree
    (fun m => ?_) hrel hgap hcomplex
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using
    RegulatorUpper.regulator_upper_bound (L m) R hR (hdisc m)

end Erdos1207


/- Adjoining a fourth root of five to a totally real field containing its square. -/


/- A fixed quartic field of signature (2,1), for mixed-signature extensions. -/

namespace PureQuartic
open Polynomial NumberField
open scoped Classical

private theorem irred_int : Irreducible (X^4-C (5 : ℤ)) := by
  let P : Ideal ℤ := Ideal.span {5}
  have hmon : (X^4-C (5 : ℤ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P := P)
  · exact (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn4 : n < 4 := by simpa only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 4),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega : n ≠ 4)]
    by_cases hn0 : n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 4)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive

theorem irreducible : Irreducible (X^4-C (5 : ℚ)) := by
  have hh := ((monic_X_pow_sub_C (5 : ℤ) (by norm_num : (4 : ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp irred_int
  simpa using hh

noncomputable instance : Fact (Irreducible (X^4-C (5 : ℚ))) := ⟨irreducible⟩
abbrev F := AdjoinRoot (X^4-C (5 : ℚ))

noncomputable def alpha : F := AdjoinRoot.root (X^4-C (5 : ℚ))

theorem alpha_pow : alpha^4 = 5 := by
  have hh := AdjoinRoot.eval₂_root (X^4-C (5 : ℚ))
  simpa [alpha,sub_eq_zero] using hh

theorem degree : Module.finrank ℚ F = 4 := by
  rw [(AdjoinRoot.powerBasis irreducible.ne_zero).finrank,AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

noncomputable def rho : ℝ := Real.sqrt (Real.sqrt 5)

theorem rho_pos : 0 < rho := by dsimp [rho]; positivity

theorem rho_pow : rho^4 = 5 := by
  have h₁ : rho^2 = Real.sqrt 5 := Real.sq_sqrt (by positivity)
  have h₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith

/-- The two real roots of `X^4-5`. -/
theorem real_roots (x : ℝ) (hx : x^4 = 5) : x = rho ∨ x = -rho := by
  have hs : (x^2)^2 = (rho^2)^2 := by nlinarith [rho_pow]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hh | hh
  · exact sq_eq_sq_iff_eq_or_eq_neg.mp hh
  · have hr : 0 < rho^2 := pow_pos rho_pos _
    nlinarith [sq_nonneg x]

noncomputable def realLift (x : ℝ) (hx : x^4 = 5) : F →+* ℂ :=
  Complex.ofRealHom.comp (AdjoinRoot.lift (f := X^4-C (5 : ℚ)) (algebraMap ℚ ℝ) x (by simp [hx]))

theorem realLift_alpha (x : ℝ) (hx : x^4 = 5) : realLift x hx alpha = (x : ℂ) := by
  simp [realLift,alpha,AdjoinRoot.lift_root]

theorem realLift_isReal (x : ℝ) (hx : x^4 = 5) : ComplexEmbedding.IsReal (realLift x hx) := by
  apply ComplexEmbedding.isReal_iff.mpr
  apply RingHom.ext
  intro a
  simp [ComplexEmbedding.conjugate_coe_eq,realLift]

theorem hom_ext {σ τ : F →+* ℂ} (h : σ alpha = τ alpha) : σ = τ :=
  AdjoinRoot.ringHom_ext (Subsingleton.elim _ _) h

theorem real_embeddings (σ : F →+* ℂ) (hσ : ComplexEmbedding.IsReal σ) :
    σ = realLift rho rho_pow ∨ σ = realLift (-rho) (by nlinarith [rho_pow]) := by
  let φ : F →+* ℝ := hσ.embedding
  have hx : (φ alpha)^4 = 5 := by
    simpa only [map_pow,map_ofNat] using congrArg φ alpha_pow
  have hval := hσ.coe_embedding_apply alpha
  rcases real_roots (φ alpha) hx with h | h
  · left
    apply hom_ext
    rw [realLift_alpha,← hval]
    exact congrArg Complex.ofReal h
  · right
    apply hom_ext
    rw [realLift_alpha,← hval]
    exact congrArg Complex.ofReal h

theorem nrRealPlaces : InfinitePlace.nrRealPlaces F = 2 := by
  let p : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} := ⟨realLift rho rho_pow,realLift_isReal _ _⟩
  let n : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} := ⟨realLift (-rho) (by nlinarith [rho_pow]),realLift_isReal _ _⟩
  have hpn : p ≠ n := by
    intro h
    have he := congrArg (fun σ : {σ : F →+* ℂ // ComplexEmbedding.IsReal σ} => σ.val alpha) h
    change realLift rho rho_pow alpha = realLift (-rho) (by nlinarith [rho_pow]) alpha at he
    rw [realLift_alpha,realLift_alpha] at he
    have hr : rho = -rho := Complex.ofReal_injective he
    linarith [rho_pos]
  have huniv : (Finset.univ : Finset {σ : F →+* ℂ // ComplexEmbedding.IsReal σ}) = {p,n} := by
    ext σ
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    rcases real_embeddings σ.val σ.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  rw [← InfinitePlace.card_real_embeddings,← Finset.card_univ,huniv,Finset.card_pair hpn]

end PureQuartic


/- A square root of five in a totally real number field cannot itself be a square. -/

namespace NegativeSquareRoot
open Polynomial NumberField
open scoped Classical

private theorem irred_int : Irreducible (X^2-C (5 : ℤ)) := by
  let P : Ideal ℤ := Ideal.span {5}
  have hmon : (X^2-C (5 : ℤ)).Monic := monic_X_pow_sub_C _ (by norm_num)
  apply irreducible_of_eisenstein_criterion (P := P)
  · exact (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).mpr (by norm_num)
  · rw [hmon.leadingCoeff]
    norm_num [P,Ideal.mem_span_singleton]
  · intro n hn
    have hn2 : n < 2 := by simpa only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2),Nat.cast_lt] using hn
    simp only [coeff_sub,coeff_X_pow,coeff_C,if_neg (by omega : n ≠ 2)]
    by_cases hn0 : n = 0 <;> simp [hn0,P,Ideal.mem_span_singleton]
  · simp only [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2)]; norm_num
  · norm_num [P,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  · exact hmon.isPrimitive

theorem irreducible_rat : Irreducible (X^2-C (5 : ℚ)) := by
  have hh := ((monic_X_pow_sub_C (5 : ℤ) (by norm_num : (2 : ℕ) ≠ 0)).irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp irred_int
  simpa using hh

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

theorem exists_negative_embedding (a : K) (ha : a^2 = 5) :
    ∃ φ : K →+* ℝ, φ a = -Real.sqrt 5 := by
  have hmin : minpoly ℚ a = X^2-C (5 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic irreducible_rat (by simp [ha]) (monic_X_pow_sub_C _ (by norm_num))).symm
  have hroot : (-(Real.sqrt 5 : ℂ)) ∈ (minpoly ℚ a).rootSet ℂ := by
    rw [hmin,mem_rootSet_of_ne irreducible_rat.ne_zero]
    have hs : (Real.sqrt 5 : ℂ)^2 = 5 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    simpa only [aeval_sub,map_pow,aeval_X,aeval_C,map_ofNat,neg_sq,sub_eq_zero] using hs
  rw [← Embeddings.range_eval_eq_rootSet_minpoly K ℂ a] at hroot
  obtain ⟨σ,hσ⟩ := hroot
  change σ a = -(Real.sqrt 5 : ℂ) at hσ
  let hr := IsTotallyReal.complexEmbedding_isReal σ
  refine ⟨hr.embedding,?_⟩
  apply Complex.ofReal_injective
  rw [hr.coe_embedding_apply,hσ,Complex.ofReal_neg]

theorem nonsquare (a : K) (ha : a^2 = 5) : ∀ b : K, b^2 ≠ a := by
  obtain ⟨φ,hφ⟩ := exists_negative_embedding K a ha
  intro b hb
  have hh := congrArg φ hb
  rw [map_pow,hφ] at hh
  have hp : 0 < Real.sqrt 5 := by positivity
  nlinarith [sq_nonneg (φ b)]

theorem irreducible_quadratic (a : K) (ha : a^2 = 5) : Irreducible (X^2-C a) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (nonsquare K a ha)

end NegativeSquareRoot


/- Signature bookkeeping for a compositum with a totally real field. -/

namespace CompositumSignature
open NumberField
open scoped Classical BigOperators

variable (F K L : Type*) [Field F] [Field K] [Field L]
  [NumberField F] [NumberField K] [NumberField L]
  [Algebra F L] [Algebra K L] [FiniteDimensional F L] [IsTotallyReal K]

omit [NumberField F] [NumberField K] [NumberField L] [FiniteDimensional F L] in
/-- In a compositum with a totally real field, an embedding is real exactly
when its restriction to the other factor is real. -/
theorem isReal_iff (hgen : Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤)
    (σ : L →+* ℂ) :
    ComplexEmbedding.IsReal σ ↔ ComplexEmbedding.IsReal (σ.comp (algebraMap F L)) := by
  refine ⟨fun h => h.comp _,fun h => ?_⟩
  let φ : K →+* ℂ := σ.comp (algebraMap K L)
  letI : Algebra K ℂ := φ.toAlgebra
  let a : L →ₐ[K] ℂ := { σ with commutes' := fun _ => rfl }
  have hφ : ComplexEmbedding.conjugate φ = φ :=
    ComplexEmbedding.isReal_iff.mp (IsTotallyReal.complexEmbedding_isReal φ)
  let b : L →ₐ[K] ℂ := { ComplexEmbedding.conjugate σ with
    commutes' := fun r => DFunLike.congr_fun hφ r }
  have hab : b = a := AlgHom.ext_of_adjoin_eq_top hgen (by
    rintro _ ⟨x,rfl⟩
    exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.mp h) x)
  exact ComplexEmbedding.isReal_iff.mpr (congrArg AlgHom.toRingHom hab)

omit [NumberField K] [Algebra K L] [IsTotallyReal K] in
/-- Every complex embedding of a base number field has exactly the relative
degree many extensions. -/
theorem card_extensions (φ : F →+* ℂ) :
    Fintype.card (ComplexEmbedding.Extension L φ) = Module.finrank F L := by
  letI : Algebra F ℂ := φ.toAlgebra
  let e : ComplexEmbedding.Extension L φ ≃ (L →ₐ[F] ℂ) :=
    { toFun σ := { σ.val with commutes' := fun r => DFunLike.congr_fun σ.property r }
      invFun σ := ⟨σ.toRingHom,by ext r; exact σ.commutes r⟩
      left_inv σ := by rfl
      right_inv σ := by rfl }
  exact (Fintype.card_congr e).trans (AlgHom.card F L ℂ)

omit [NumberField K] [Algebra K L] [IsTotallyReal K] in
/-- If real base embeddings have only real extensions, the number of real
places multiplies by the extension degree. -/
theorem nrRealPlaces_mul
    (hreal : ∀ σ : L →+* ℂ, ComplexEmbedding.IsReal (σ.comp (algebraMap F L)) → ComplexEmbedding.IsReal σ) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L := by
  let e : {σ : L →+* ℂ // ComplexEmbedding.IsReal σ} ≃
      Σ φ : {φ : F →+* ℂ // ComplexEmbedding.IsReal φ}, ComplexEmbedding.Extension L φ.val :=
    { toFun σ := ⟨⟨σ.val.comp (algebraMap F L),σ.property.comp _⟩,⟨σ.val,rfl⟩⟩
      invFun p := ⟨p.2.val,hreal p.2.val (by rw [p.2.property]; exact p.1.property)⟩
      left_inv σ := rfl
      right_inv p := by rcases p with ⟨⟨φ,hφ⟩,⟨σ,hσ⟩⟩; cases hσ; rfl }
  rw [← InfinitePlace.card_real_embeddings, Fintype.card_congr e,Fintype.card_sigma]
  simp only [card_extensions,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    InfinitePlace.card_real_embeddings,Nat.cast_id]

omit [NumberField K] in
/-- The signature multiplication theorem applied to a compositum. -/
theorem nrRealPlaces_compositum
    (hgen : Algebra.adjoin K (Set.range (algebraMap F L)) = ⊤) :
    InfinitePlace.nrRealPlaces L = InfinitePlace.nrRealPlaces F * Module.finrank F L :=
  nrRealPlaces_mul F L (fun σ h => (isReal_iff F K L hgen σ).mpr h)

end CompositumSignature


/- Discriminant control for a bounded square-root generator. -/


/- Elementary different-ideal bounds for a quadratic generator. -/

namespace QuadraticDifferent
set_option maxHeartbeats 1000000
open NumberField Polynomial
open scoped Classical

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- The derivative of any annihilating polynomial lies in the different
provided that the algebraic integer generates the extension. -/
theorem derivative_mem (x : 𝓞 L)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤)
    (p : (𝓞 K)[X]) (hp : aeval x p = 0) :
    aeval x p.derivative ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  obtain ⟨q,rfl⟩ := minpoly.isIntegrallyClosed_dvd (IsIntegralClosure.isIntegral (𝓞 K) L x) hp
  rw [derivative_mul,map_add,map_mul,map_mul,minpoly.aeval,zero_mul,add_zero]
  exact Ideal.mul_mem_right _ _ (aeval_derivative_mem_differentIdeal (𝓞 K) K L x hgen)

/-- A square-root generator has `2*x` in the relative different. -/
theorem two_mul_mem (a : 𝓞 K) (x : 𝓞 L)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a) :
    2*x ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hh := derivative_mem K L x hgen (X^2-C a) (by simp [hx])
  simpa only [derivative_sub,derivative_pow,derivative_X,derivative_C,pow_one,
    mul_one,sub_zero,map_mul,map_natCast,aeval_X,Nat.reduceSub,aeval_C,Nat.cast_ofNat,map_ofNat] using hh

end QuadraticDifferent


/- A house bound controls the norm of a principal ideal. -/

namespace IntegralNormBound
open NumberField
open scoped Classical BigOperators

variable (L : Type*) [Field L] [NumberField L]

theorem norm_span_eq_prod (x : 𝓞 L) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ (x : L)‖ := by
  have h := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : L))
  rw [← Algebra.coe_norm_int] at h
  simpa [Ideal.absNorm_span_singleton,norm_prod] using h

theorem norm_span_le (x : 𝓞 L) (H : ℝ)
    (hbound : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ H) :
    (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ H^(Module.finrank ℚ L) := by
  rw [norm_span_eq_prod]
  have hh := Finset.prod_le_prod (s := (Finset.univ : Finset (L →ₐ[ℚ] ℂ)))
    (fun σ _ => norm_nonneg (σ (x : L))) (fun σ _ => hbound σ.toRingHom)
  simpa only [Finset.prod_const,Finset.card_univ,AlgHom.card] using hh

end IntegralNormBound

namespace QuadraticDiscriminant
open NumberField
open scoped Classical BigOperators

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

/-- A bounded square-root generator gives an exponential bound for the
relative different. -/
theorem different_norm_le (a : 𝓞 K) (x : 𝓞 L) (hx0 : x ≠ 0)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (H : ℝ) (hhouse : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ H) :
    ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ) ≤ (2*H)^(Module.finrank ℚ L) := by
  have hm := QuadraticDifferent.two_mul_mem K L a x hgen hx
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
  have hpos : 0 < (Ideal.span ({2*x} : Set (𝓞 L))).absNorm := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq,Ideal.absNorm_eq_zero_iff,Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (by norm_num) hx0
  have hle := Nat.le_of_dvd hpos hdvd
  apply (show ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ) ≤ (Ideal.span ({2*x} : Set (𝓞 L))).absNorm by
    exact_mod_cast hle).trans
  apply IntegralNormBound.norm_span_le L (2*x) (2*H)
  intro σ
  norm_num only [map_mul,map_ofNat,norm_mul,RCLike.norm_two]
  exact mul_le_mul_of_nonneg_left (hhouse σ) (by norm_num : (0 : ℝ) ≤ 2)

/-- Absolute discriminants in a quadratic extension stay exponentially
bounded when a square-root generator has uniformly bounded conjugates. -/
theorem discr_le (a : 𝓞 K) (x : 𝓞 L) (hx0 : x ≠ 0)
    (hgen : Algebra.adjoin K {(x : L)} = ⊤) (hx : x^2 = algebraMap (𝓞 K) (𝓞 L) a)
    (hdeg : Module.finrank K L = 2) (R : ℕ)
    (hdisc : |(discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K))
    (hhouse : ∀ σ : L →+* ℂ, ‖σ (x : L)‖ ≤ 2) :
    |(discr L : ℝ)| ≤ (2*(R : ℝ))^(2*Module.finrank ℚ L) := by
  have hdiff := different_norm_le K L a x hx0 hgen hx 2 hhouse
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have her : |(discr L : ℝ)| = ((differentIdeal (𝓞 K) (𝓞 L)).absNorm : ℝ)*|(discr K : ℝ)|^2 := by
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_natAbs,Int.cast_abs,hdeg] using
      congrArg (fun n : ℕ => (n : ℝ)) he
  have hd := Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  rw [her]
  calc
    _ ≤ (4 : ℝ)^(Module.finrank ℚ L)*((R : ℝ)^(2*Module.finrank ℚ K))^2 := by
      gcongr
      simpa only [show (2 : ℝ)*2 = 4 by norm_num] using hdiff
    _ = (2*(R : ℝ))^(2*Module.finrank ℚ L) := by
      rw [show (4 : ℝ) = 2^2 by norm_num,← pow_mul,← pow_mul,mul_pow]
      congr 2; omega

end QuadraticDiscriminant

namespace MixedExtension
open Polynomial NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K] (a : K) [Fact (a^2 = 5)]

noncomputable instance : Fact (Irreducible (X^2-C a)) :=
  ⟨NegativeSquareRoot.irreducible_quadratic K a Fact.out⟩

abbrev L := AdjoinRoot (X^2-C a)

instance : Module.Finite K (L K a) := (monic_X_pow_sub_C a (by norm_num : (2 : ℕ) ≠ 0)).finite_adjoinRoot

noncomputable instance : NumberField (L K a) := NumberField.of_module_finite K (L K a)

noncomputable def b : L K a := AdjoinRoot.root (X^2-C a)

theorem b_sq : (b K a)^2 = algebraMap K (L K a) a := root_X_pow_sub_C_pow 2 a

theorem b_pow : (b K a)^4 = 5 := by
  calc
    (b K a)^4 = ((b K a)^2)^2 := by ring
    _ = (algebraMap K (L K a) a)^2 := by rw [b_sq]
    _ = algebraMap K (L K a) (a^2) := (map_pow _ _ _).symm
    _ = 5 := by rw [show a^2 = 5 from Fact.out,map_ofNat]

theorem degree : Module.finrank K (L K a) = 2 := by
  rw [(AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out : Irreducible (X^2-C a)).ne_zero)).finrank,
    AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

theorem adjoin_b : Algebra.adjoin K {b K a} = ⊤ := by
  exact (AdjoinRoot.powerBasis (show X^2-C a ≠ 0 from (Fact.out : Irreducible (X^2-C a)).ne_zero)).adjoin_gen_eq_top

noncomputable def quarticMap : PureQuartic.F →+* L K a :=
  AdjoinRoot.lift (algebraMap ℚ (L K a)) (b K a) (by simp [b_pow])

noncomputable instance quarticAlgebra : Algebra PureQuartic.F (L K a) := (quarticMap K a).toAlgebra

theorem quarticMap_alpha : algebraMap PureQuartic.F (L K a) PureQuartic.alpha = b K a := by
  change quarticMap K a PureQuartic.alpha = b K a
  simp [quarticMap,PureQuartic.alpha,AdjoinRoot.lift_root]

theorem compositum : Algebra.adjoin K (Set.range (algebraMap PureQuartic.F (L K a))) = ⊤ := by
  apply top_unique
  rw [← adjoin_b K a]
  apply Algebra.adjoin_mono
  exact Set.singleton_subset_iff.mpr ⟨PureQuartic.alpha,quarticMap_alpha K a⟩

theorem half_real : 2*InfinitePlace.nrRealPlaces (L K a) = Module.finrank ℚ (L K a) := by
  have hr := CompositumSignature.nrRealPlaces_compositum PureQuartic.F K (L K a) (compositum K a)
  rw [PureQuartic.nrRealPlaces] at hr
  have hd := Module.finrank_mul_finrank ℚ PureQuartic.F (L K a)
  rw [PureQuartic.degree] at hd
  omega

omit [NumberField K] [IsTotallyReal K] in
theorem integral_a : IsIntegral ℤ a := by
  refine ⟨X^2-C (5 : ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [show a^2 = 5 from Fact.out]

theorem integral_b : IsIntegral ℤ (b K a) := by
  refine ⟨X^4-C (5 : ℤ),monic_X_pow_sub_C _ (by norm_num),?_⟩
  simp [b_pow]

noncomputable def intA : 𝓞 K := ⟨a,integral_a K a⟩
noncomputable def intB : 𝓞 (L K a) := ⟨b K a,integral_b K a⟩

theorem house_b (σ : L K a →+* ℂ) : ‖σ (b K a)‖ ≤ 2 := by
  have hp := congrArg (fun z : L K a => ‖σ z‖) (b_pow K a)
  simp only [map_pow,norm_pow,map_ofNat,RCLike.norm_ofNat] at hp
  have hn := norm_nonneg (σ (b K a))
  by_contra h
  have hh : 2 < ‖σ (b K a)‖ := lt_of_not_ge h
  have hsq : 4 < ‖σ (b K a)‖^2 := by nlinarith
  nlinarith [sq_nonneg (‖σ (b K a)‖^2-4)]

theorem discr_bound (R : ℕ)
    (hdisc : |(discr K : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ K)) :
    |(discr (L K a) : ℝ)| ≤ (2*(R : ℝ))^(2*Module.finrank ℚ (L K a)) := by
  apply QuadraticDiscriminant.discr_le K (L K a) (intA K a) (intB K a) ?_
    (adjoin_b K a) ?_ (degree K a) R hdisc (house_b K a)
  · intro h
    have hb0 : b K a = 0 := congrArg (fun x : 𝓞 (L K a) => (x : L K a)) h
    have hp := b_pow K a
    rw [hb0] at hp
    norm_num at hp
  · apply RingOfIntegers.coe_injective
    exact b_sq K a

end MixedExtension



namespace UnitRankBounds
open NumberField
open NumberField.InfinitePlace
open scoped Classical

/-- A half-real quadratic extension of a totally real field has precisely
the linear unit-rank gap used in the arithmetic reduction. -/
theorem gap_of_half_real (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsTotallyReal K]
    (hdeg : Module.finrank K L = 2) (hhalf : 2*nrRealPlaces L = Module.finrank ℚ L) :
    4*NumberField.Units.rank K+Module.finrank ℚ L ≤ 4*NumberField.Units.rank L := by
  have hL := card_add_two_mul_card_eq_rank L
  have hK := IsTotallyReal.finrank K
  have hz := IsTotallyReal.nrComplexPlaces_eq_zero K
  have hd := Module.finrank_mul_finrank ℚ K L
  rw [hdeg] at hd
  have hp : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [NumberField.Units.rank,NumberField.Units.rank,
    card_eq_nrRealPlaces_add_nrComplexPlaces,card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

/-- A half-real number field has a nonreal complex embedding. -/
theorem exists_complex_of_half_real (L : Type*) [Field L] [NumberField L]
    (hhalf : 2*nrRealPlaces L = Module.finrank ℚ L) :
    ∃ σ : L →+* ℂ, ¬ ComplexEmbedding.IsReal σ := by
  have hL := card_add_two_mul_card_eq_rank L
  have hp : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hc : 0 < nrComplexPlaces L := by omega
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨w.val.embedding,isComplex_iff.mp w.property⟩

end UnitRankBounds

namespace Erdos1207
open NumberField
open scoped Classical

/-- The remaining arithmetic existence premise, with all downstream
unit, geometry, discriminant and signature estimates discharged. -/
theorem power_saving_of_totally_real_family
    (K : ℕ → Type*) [∀ m, Field (K m)] [∀ m, NumberField (K m)] [∀ m, IsTotallyReal (K m)]
    (a : ∀ m, K m) (ha : ∀ m, (a m)^2 = 5)
    (R D : ℕ) (hR : 0 < R)
    (hdegree : ∀ m, 2^m ≤ Module.finrank ℚ (K m) ∧ Module.finrank ℚ (K m) ≤ D*2^m)
    (hdisc : ∀ m, |(discr (K m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (K m))) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  letI : ∀ m, Fact ((a m)^2 = 5) := fun m => ⟨ha m⟩
  let L := fun m => MixedExtension.L (K m) (a m)
  have hrel (m : ℕ) : Module.finrank (K m) (L m) = 2 := MixedExtension.degree (K m) (a m)
  have hhalf (m : ℕ) : 2*InfinitePlace.nrRealPlaces (L m) = Module.finrank ℚ (L m) :=
    MixedExtension.half_real (K m) (a m)
  apply power_saving_of_bounded_discriminant_family K L (2*R) (2*D) (by positivity)
    (fun m => ?_) (fun m => ?_) hrel
    (fun m => UnitRankBounds.gap_of_half_real (K m) (L m) (hrel m) (hhalf m))
    (fun m => UnitRankBounds.exists_complex_of_half_real (L m) (hhalf m))
  · have he := Module.finrank_mul_finrank ℚ (K m) (L m)
    rw [hrel m] at he
    have hd := hdegree m
    constructor
    · omega
    · nlinarith
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      MixedExtension.discr_bound (K m) (a m) R (hdisc m)

end Erdos1207



/- Root-discriminant bounds pass to subfields. -/
namespace DiscriminantDescent
open NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem discr_pow_le :
    |(discr K : ℝ)|^(Module.finrank K L) ≤ |(discr L : ℝ)| := by
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have hpos : 0 < (discr L).natAbs := Int.natAbs_pos.mpr (discr_ne_zero L)
  have hnorm : 1 ≤ Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) := by
    rw [he] at hpos
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt (Nat.pos_of_mul_pos_right hpos))
  have hh : (discr K).natAbs^(Module.finrank K L) ≤ (discr L).natAbs := by
    rw [he]
    exact Nat.le_mul_of_pos_left _ hnorm
  have hh' : ((discr K).natAbs : ℝ)^(Module.finrank K L) ≤ ((discr L).natAbs : ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'

theorem root_bound (R : ℝ) (hR : 0 ≤ R)
    (hL : |(discr L : ℝ)| ≤ R^(2*Module.finrank ℚ L)) :
    |(discr K : ℝ)| ≤ R^(2*Module.finrank ℚ K) := by
  have hpow := (discr_pow_le K L).trans hL
  have hd := Module.finrank_mul_finrank ℚ K L
  have hp : 0 < Module.finrank K L := Module.finrank_pos
  have he : R^(2*Module.finrank ℚ L) =
      (R^(2*Module.finrank ℚ K))^(Module.finrank K L) := by
    rw [← pow_mul,← hd]
    congr 1
    ring
  rw [he] at hpow
  exact le_of_pow_le_pow_left₀ hp.ne' (by positivity) hpow

end DiscriminantDescent



/- Controlled intermediate degrees in finite Galois p-extensions. -/
namespace PFieldDegrees
open IntermediateField

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every power of p up to the degree of a Galois p-extension occurs as an
intermediate degree. Normality of the intermediate field is not required. -/
theorem exists_intermediate (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (m : ℕ) (hm : p^m ≤ Module.finrank K L) :
    ∃ E : IntermediateField K L, Module.finrank K E = p^m := by
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have hdegree : Module.finrank K L = p^a := (IsGalois.card_aut_eq_finrank K L).symm.trans ha
  have hma : m ≤ a := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hm.trans_eq hdegree)
  obtain ⟨H,hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Gal(L/K)) p
    (show p^(a-m) ∣ Nat.card Gal(L/K) by rw [ha]; exact pow_dvd_pow p (by omega))
  refine ⟨fixedField H,?_⟩
  have he := Module.finrank_mul_finrank K (fixedField H) L
  rw [finrank_fixedField_eq_card,hH,hdegree] at he
  have hh : p^a = p^m*p^(a-m) := by rw [← pow_add,Nat.add_sub_of_le hma]
  rw [hh] at he
  exact Nat.mul_right_cancel (show 0 < p^(a-m) from pow_pos (Fact.out : p.Prime).pos _) he

end PFieldDegrees

namespace Erdos1207
open NumberField
open scoped Classical

/-- A bounded-root-discriminant totally real Galois 2-family need only have
unbounded degrees: intermediate fields supply the controlled degree growth. -/
theorem power_saving_of_unbounded_galois_family
    (B : Type*) [Field B] [NumberField B] (a : B) (ha : a^2 = 5)
    (L : ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (R : ℕ) (hR : 0 < R)
    (hG : ∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree : ∀ m, 2^m ≤ Module.finrank B (L m))
    (hdisc : ∀ m, |(discr (L m) : ℝ)| ≤ (R : ℝ)^(2*Module.finrank ℚ (L m))) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have he : ∀ m, ∃ E : IntermediateField B (L m), Module.finrank B E = 2^m :=
    fun m => PFieldDegrees.exists_intermediate B (L m) 2 (hG m) m (hdegree m)
  choose E hE using he
  letI (m : ℕ) : NumberField (E m) := NumberField.of_module_finite ℚ (E m)
  letI (m : ℕ) : IsTotallyReal (E m) := IsTotallyReal.of_algebra (E m) (L m)
  apply power_saving_of_totally_real_family (fun m => E m)
    (fun m => algebraMap B (E m) a) (fun m => ?_) R (Module.finrank ℚ B) hR
    (fun m => ?_) (fun m => DiscriminantDescent.root_bound (E m) (L m) (R : ℝ) (by positivity) (hdisc m))
  · rw [← map_pow,ha,map_ofNat]
  · have hd := Module.finrank_mul_finrank ℚ B (E m)
    rw [hE m] at hd
    have hpos : 0 < Module.finrank ℚ B := Module.finrank_pos
    constructor
    · rw [← hd]
      exact Nat.le_mul_of_pos_left _ hpos
    · exact hd.ge

end Erdos1207
namespace Erdos1207
open NumberField
open scoped Classical

/-- An unbounded totally real unramified Galois 2-family is sufficient.
This is a conditional reduction, not an existence theorem for such a family. -/
theorem power_saving_of_unbounded_unramified_family
    (B : Type*) [Field B] [NumberField B] (a : B) (ha : a^2 = 5)
    (L : ℕ → Type*) [∀ m, Field (L m)] [∀ m, NumberField (L m)]
    [∀ m, Algebra B (L m)] [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)]
    (hG : ∀ m, IsPGroup 2 Gal(L m/B))
    (hdegree : ∀ m, 2^m ≤ Module.finrank B (L m))
    (hunram : ∀ m, differentIdeal (𝓞 B) (𝓞 (L m)) = ⊤) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  let R := (discr B).natAbs
  have hR : 0 < R := Int.natAbs_pos.mpr (discr_ne_zero B)
  apply power_saving_of_unbounded_galois_family B a ha L R hR hG hdegree
  intro m
  have he := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow B (𝓞 B) (L m) (𝓞 (L m))
  rw [hunram m,Ideal.absNorm_top,one_mul] at he
  have hexp : Module.finrank B (L m) ≤ 2*Module.finrank ℚ (L m) := by
    have hd := Module.finrank_mul_finrank ℚ B (L m)
    have hp : 0 < Module.finrank ℚ B := Module.finrank_pos
    have hh := Nat.le_mul_of_pos_left (Module.finrank B (L m)) hp
    omega
  have hb : (discr (L m)).natAbs ≤ R^(2*Module.finrank ℚ (L m)) := by
    rw [he]
    exact Nat.pow_le_pow_right hR hexp
  have hb' : ((discr (L m)).natAbs : ℝ) ≤ (R : ℝ)^(2*Module.finrank ℚ (L m)) := by exact_mod_cast hb
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hb'

end Erdos1207

/-! Cardinality of multiplication quotients for finitely generated abelian groups. -/
namespace ModNFinitelyGenerated
open scoped Classical

variable (A : Type*) [AddCommGroup A] (n : ℕ)

def mulN : A →ₗ[ℤ] A := LinearMap.lsmul ℤ A (n : ℤ)

@[simp] theorem mulN_apply (a : A) : mulN A n a = (n : ℤ) • a := rfl

noncomputable def congr {B : Type*} [AddCommGroup B] (e : A ≃ₗ[ℤ] B) :
    ModN A n ≃ₗ[ℤ] ModN B n :=
  Submodule.Quotient.equiv _ _ e (by
    ext b
    constructor
    · rintro ⟨a,⟨x,rfl⟩,rfl⟩
      exact ⟨e x, (e.map_smul (n : ℤ) x).symm⟩
    · rintro ⟨b,rfl⟩
      refine ⟨(n : ℤ) • e.symm b,⟨e.symm b,rfl⟩,?_⟩
      simp)

noncomputable def kerCongr {B : Type*} [AddCommGroup B] (e : A ≃ₗ[ℤ] B) :
    (mulN A n).ker ≃ (mulN B n).ker :=
  e.toEquiv.subtypeEquiv (fun a => by
    change ((n : ℤ) • a = 0) ↔ ((n : ℤ) • e a = 0)
    rw [← e.map_smul, ← e.map_zero]
    exact e.injective.eq_iff.symm)

noncomputable def prod (B : Type*) [AddCommGroup B] :
    ModN (A × B) n ≃ₗ[ℤ] ModN A n × ModN B n := by
  let f : A × B →ₗ[ℤ] ModN A n × ModN B n :=
    (mulN A n).range.mkQ.prodMap (mulN B n).range.mkQ
  have hf : Function.Surjective f := by
    rintro ⟨x,y⟩
    obtain ⟨a,rfl⟩ := (mulN A n).range.mkQ_surjective x
    obtain ⟨b,rfl⟩ := (mulN B n).range.mkQ_surjective y
    exact ⟨(a,b),rfl⟩
  have hk : (mulN (A × B) n).range = f.ker := by
    ext x
    change (∃ y, (n : ℤ) • y = x) ↔ f x = 0
    change (∃ y, (n : ℤ) • y = x) ↔
      ((Submodule.Quotient.mk x.1 : ModN A n),
        (Submodule.Quotient.mk x.2 : ModN B n)) = (0,0)
    rw [Prod.mk.injEq,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨⟨a,b⟩,rfl⟩
      exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
      exact ⟨(a,b),Prod.ext ha hb⟩
  exact (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hf)

noncomputable def kerProd (B : Type*) [AddCommGroup B] :
    (mulN (A × B) n).ker ≃ (mulN A n).ker × (mulN B n).ker :=
  (Equiv.refl (A × B) |>.subtypeEquiv (fun x => by
    change ((n : ℤ) • x = 0) ↔ ((n : ℤ) • x.1 = 0 ∧ (n : ℤ) • x.2 = 0)
    exact Prod.ext_iff)).trans Equiv.subtypeProdEquivProd

/-- For a finite abelian group, the kernel and cokernel of multiplication
by any integer have the same cardinality. -/
theorem card_modN_of_finite [Finite A] :
    Nat.card (ModN A n) = Nat.card (mulN A n).ker := by
  have h₁ := (mulN A n).range.card_eq_card_quotient_mul_card
  have h₂ := (mulN A n).ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr (mulN A n).quotKerEquivRange.toEquiv,mul_comm] at h₂
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h₁.symm.trans h₂)

variable [Module.Finite ℤ A]

/-- The torsion subgroup splits off a finitely generated abelian group. -/
noncomputable def splitTorsion :
    A ≃ₗ[ℤ] (Submodule.torsion ℤ A) × (A ⧸ Submodule.torsion ℤ A) := by
  let hf := Module.projective_lifting_property
    (Submodule.torsion ℤ A).mkQ LinearMap.id (Submodule.torsion ℤ A).mkQ_surjective
  let f := Classical.choose hf
  have hf : (Submodule.torsion ℤ A).mkQ.comp f = LinearMap.id := Classical.choose_spec hf
  exact (lequivProdOfRightSplitExact (Submodule.torsion ℤ A).injective_subtype
    (by rw [Submodule.range_subtype,Submodule.ker_mkQ]) hf).symm

/-- Multiplication modulo `n` counts the free part and the `n`-torsion. -/
theorem card_modN [NeZero n] :
    Nat.card (ModN A n) = n ^ Module.finrank ℤ A * Nat.card (mulN A n).ker := by
  let T := Submodule.torsion ℤ A
  let F := A ⧸ T
  letI : Finite T := Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  have hr : Module.finrank ℤ F = Module.finrank ℤ A := by
    apply Nat.cast_injective (R := Cardinal)
    rw [Module.finrank_eq_rank,Module.finrank_eq_rank]
    exact rank_quotient_eq_of_le_torsion le_rfl
  have hk : (mulN F n).ker = ⊥ := by
    ext x
    simp only [LinearMap.mem_ker,mulN_apply,Submodule.mem_bot]
    exact smul_eq_zero_iff_right (by exact_mod_cast NeZero.ne n)
  have hkc : Nat.card (mulN F n).ker = 1 := by
    rw [hk]
    exact Nat.card_unique
  have hc : Nat.card (ModN A n) = Nat.card (ModN T n) * Nat.card (ModN F n) := by
    rw [Nat.card_congr (congr A n (splitTorsion A)).toEquiv,
      Nat.card_congr (prod T n F).toEquiv,Nat.card_prod]
  have htk : Nat.card (mulN A n).ker = Nat.card (mulN T n).ker := by
    rw [Nat.card_congr (kerCongr A n (splitTorsion A)),
      Nat.card_congr (kerProd T n F),Nat.card_prod,hkc,mul_one]
  rw [hc,card_modN_of_finite,ModN.natCard_eq,hr,htk,mul_comm]

/-- Every multiplication quotient of a finitely generated abelian group
is finite when the multiplier is nonzero. -/
theorem finite_modN [NeZero n] : Finite (ModN A n) := by
  have : Finite (mulN A n).ker := Module.finite_of_fg_torsion _ (by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast NeZero.ne n)⟩,?_⟩
    apply Subtype.ext
    exact x.property)
  exact Nat.finite_of_card_ne_zero (by
    rw [card_modN]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne n)) (Nat.ne_of_gt Nat.card_pos))

end ModNFinitelyGenerated

/-! Elementary cardinal identities behind the Herbrand quotient of an involution. -/
namespace InvolutionHerbrand
open scoped Classical

variable {A : Type*} [AddCommGroup A]
variable (σ : A →ₗ[ℤ] A) (hσ : σ.comp σ = LinearMap.id)

def plus : Submodule ℤ A := (σ-LinearMap.id).ker

def minus : Submodule ℤ A := (σ+LinearMap.id).ker

@[simp] theorem mem_plus (x : A) : x ∈ plus σ ↔ σ x = x := by
  simp [plus,sub_eq_zero]

@[simp] theorem mem_minus (x : A) : x ∈ minus σ ↔ σ x+x = 0 := by
  simp [minus]

include hσ in
theorem involutive (x : A) : σ (σ x) = x := LinearMap.congr_fun hσ x

def norm : A →ₗ[ℤ] plus σ := (σ+LinearMap.id).codRestrict (plus σ) (fun x => by
  rw [mem_plus]
  change σ (σ x+x) = σ x+x
  rw [map_add,involutive σ hσ]
  abel)

def double (V : Type*) [AddCommGroup V] : V →ₗ[ℤ] V := LinearMap.lsmul ℤ V 2

@[simp] theorem double_apply (V : Type*) [AddCommGroup V] (x : V) :
    double V x = x+x := by simp [double,two_smul]

def modNorm : A →ₗ[ℤ] ModN (plus σ) 2 :=
  (LinearMap.range (double (plus σ))).mkQ.comp (norm σ hσ)

/-- The kernel of the norm modulo twice the invariant subgroup consists
exactly of sums of invariant and anti-invariant elements. -/
theorem ker_modNorm : (modNorm σ hσ).ker = plus σ ⊔ minus σ := by
  ext x
  change (modNorm σ hσ x = 0) ↔ _
  change (Submodule.Quotient.mk (norm σ hσ x) : (plus σ) ⧸ (double (plus σ)).range) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    have he : σ x+x = (y : A)+(y : A) := by
      have hh := congrArg (fun y : plus σ => (y : A)) hy
      simpa only [double_apply,Submodule.coe_add] using hh.symm
    refine Submodule.mem_sup.mpr ⟨y,y.property,x-y,?_,by abel⟩
    rw [mem_minus]
    have hyσ : σ (y : A) = y := (mem_plus σ _).mp y.property
    calc
      σ (x-y)+(x-y) = (σ x+x)-(σ (y : A)+y) := by rw [map_sub]; abel
      _ = 0 := by rw [he,hyσ,sub_self]
  · intro hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨y,hy⟩,?_⟩
    apply Subtype.ext
    change ((double (plus σ)) ⟨y,hy⟩ : A) = σ (y+z)+(y+z)
    rw [double_apply,Submodule.coe_add,map_add]
    have hyσ := (mem_plus σ y).mp hy
    have hzσ := (mem_minus σ z).mp hz
    rw [hyσ]
    calc
      y+y = y+y+(σ z+z) := by rw [hzσ,add_zero]
      _ = y+σ z+(y+z) := by abel

/-- Twice every invariant element is a norm. -/
theorem double_le_norm_range : (double (plus σ)).range ≤ (norm σ hσ).range := by
  rintro x ⟨y,rfl⟩
  refine ⟨y,?_⟩
  apply Subtype.ext
  change σ (y : A)+(y : A) = ((double (plus σ)) y : A)
  rw [double_apply,Submodule.coe_add,(mem_plus σ _).mp y.property]

/-- The norm modulo two identifies the common finite-index quotient. -/
noncomputable def quotientEquivNormRange :
    (A ⧸ (plus σ ⊔ minus σ)) ≃ₗ[ℤ]
      ((norm σ hσ).range.map (LinearMap.range (double (plus σ))).mkQ) := by
  have hr : (modNorm σ hσ).range =
      (norm σ hσ).range.map (LinearMap.range (double (plus σ))).mkQ := by
    rw [modNorm,LinearMap.range_comp]
  exact (Submodule.quotEquivOfEq _ _ (ker_modNorm σ hσ).symm).trans
    ((modNorm σ hσ).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

/-- The basic norm cardinality identity, valid even before any finiteness
or freeness hypotheses are imposed. -/
theorem norm_card_identity :
    Nat.card (A ⧸ (plus σ ⊔ minus σ)) *
      Nat.card ((plus σ) ⧸ (norm σ hσ).range) = Nat.card (ModN (plus σ) 2) := by
  rw [Nat.card_congr (quotientEquivNormRange σ hσ).toEquiv]
  exact Submodule.card_quotient_mul_card_quotient (norm σ hσ).range
    (double (plus σ)).range (double_le_norm_range σ hσ)

/-- For a free finitely generated lattice this becomes a power-of-two formula. -/
theorem norm_card_identity_of_free [Module.Free ℤ A] [Module.Finite ℤ A] :
    Nat.card (A ⧸ (plus σ ⊔ minus σ)) *
      Nat.card ((plus σ) ⧸ (norm σ hσ).range) = 2^Module.finrank ℤ (plus σ) := by
  rw [norm_card_identity]
  exact ModN.natCard_eq (plus σ) 2

include hσ in
theorem neg_involution : (-σ).comp (-σ) = LinearMap.id := by
  ext x
  simp only [LinearMap.comp_apply,LinearMap.neg_apply,map_neg,neg_neg,LinearMap.id_apply]
  exact involutive σ hσ x

@[simp] theorem plus_neg : plus (-σ) = minus σ := by
  ext x
  rw [mem_plus,mem_minus,LinearMap.neg_apply]
  constructor
  · intro h
    calc
      σ x+x = σ x+(-σ x) := congrArg (σ x+·) h.symm
      _ = 0 := add_neg_cancel (σ x)
  · intro h
    apply neg_injective
    simpa only [neg_neg] using eq_neg_of_add_eq_zero_left h

@[simp] theorem minus_neg : minus (-σ) = plus σ := by
  have h := plus_neg (-σ)
  simpa only [neg_neg] using h.symm

/-- The lattice Herbrand quotient, stated without rational division so that
all cardinalities and ranks remain natural numbers. -/
theorem herbrand_identity [Module.Free ℤ A] [Module.Finite ℤ A] :
    Nat.card ((plus σ) ⧸ (norm σ hσ).range) * 2^Module.finrank ℤ (minus σ) =
      Nat.card ((plus (-σ)) ⧸ (norm (-σ) (neg_involution σ hσ)).range) *
        2^Module.finrank ℤ (plus σ) := by
  have hplus := norm_card_identity_of_free σ hσ
  have hminus := norm_card_identity_of_free (-σ) (neg_involution σ hσ)
  simp only [plus_neg,minus_neg,sup_comm (minus σ)] at hminus
  have hr : Module.finrank ℤ (plus (-σ)) = Module.finrank ℤ (minus σ) :=
    (LinearEquiv.ofEq _ _ (plus_neg σ)).finrank_eq
  rw [hr] at hminus
  calc
    _ = Nat.card ((plus σ) ⧸ (norm σ hσ).range) *
        (Nat.card (A ⧸ (plus σ ⊔ minus σ)) *
          Nat.card ((plus (-σ)) ⧸ (norm (-σ) (neg_involution σ hσ)).range)) := by
      rw [hminus]
    _ = Nat.card ((plus (-σ)) ⧸ (norm (-σ) (neg_involution σ hσ)).range) *
        (Nat.card (A ⧸ (plus σ ⊔ minus σ)) * Nat.card ((plus σ) ⧸ (norm σ hσ).range)) := by ring
    _ = _ := by rw [hplus]

end InvolutionHerbrand

namespace InvolutionHerbrand
open scoped Classical
open ModNFinitelyGenerated

variable {A : Type*} [AddCommGroup A]
variable (σ : A →ₗ[ℤ] A) (hσ : σ.comp σ = LinearMap.id)

private theorem fixed_neg_of_two (x : A) (hfix : σ x = x) (hx : x+x=0) :
    -σ x = x := by
  rw [hfix]
  exact (eq_neg_of_add_eq_zero_left hx).symm

/-- The two eigensubgroups have the same two-torsion, including when the
ambient group itself has torsion. -/
noncomputable def twoTorsionEquiv :
    (mulN (plus σ) 2).ker ≃ (mulN (plus (-σ)) 2).ker where
  toFun x := ⟨⟨x.1.1, by
    rw [mem_plus,LinearMap.neg_apply]
    apply fixed_neg_of_two σ _ ((mem_plus σ _).mp x.1.2)
    have h := congrArg Subtype.val x.2
    change (2 : ℤ) • x.1.1 = 0 at h
    simpa only [two_zsmul] using h⟩,by
      apply Subtype.ext
      have h := congrArg Subtype.val x.2
      exact h⟩
  invFun x := ⟨⟨x.1.1,by
    rw [mem_plus]
    have h := congrArg Subtype.val x.2
    change (2 : ℤ) • x.1.1 = 0 at h
    have hx := fixed_neg_of_two (-σ) _ ((mem_plus (-σ) _).mp x.1.2)
      (by simpa only [two_zsmul] using h)
    simpa only [LinearMap.neg_apply,neg_neg] using hx⟩,by
      apply Subtype.ext
      have h := congrArg Subtype.val x.2
      exact h⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Module.Finite ℤ A]

theorem finite_norm_quotient : Finite ((plus σ) ⧸ (norm σ hσ).range) := by
  letI : Finite ((plus σ) ⧸ (double (plus σ)).range) := finite_modN (plus σ) 2
  exact Finite.of_surjective (Submodule.factor (double_le_norm_range σ hσ))
    (Submodule.factor_surjective (double_le_norm_range σ hσ))

/-- Herbrand's cardinality identity for a finitely generated abelian group,
without any torsion-free hypothesis. -/
theorem herbrand_identity_fg :
    Nat.card ((plus σ) ⧸ (norm σ hσ).range) * 2^Module.finrank ℤ (minus σ) =
      Nat.card ((plus (-σ)) ⧸ (norm (-σ) (neg_involution σ hσ)).range) *
        2^Module.finrank ℤ (plus σ) := by
  have hplus := norm_card_identity σ hσ
  have hminus := norm_card_identity (-σ) (neg_involution σ hσ)
  have hc :
      Nat.card ((plus σ) ⧸ (norm σ hσ).range) * Nat.card (ModN (plus (-σ)) 2) =
        Nat.card ((plus (-σ)) ⧸ (norm (-σ) (neg_involution σ hσ)).range) *
          Nat.card (ModN (plus σ) 2) := by
    rw [← hminus,← hplus]
    simp only [plus_neg,minus_neg,sup_comm (minus σ)]
    ring
  rw [card_modN,card_modN] at hc
  have he : Nat.card (mulN (plus (-σ)) 2).ker = Nat.card (mulN (plus σ) 2).ker :=
    (Nat.card_congr (twoTorsionEquiv σ)).symm
  rw [he,← mul_assoc,← mul_assoc] at hc
  have ht : Finite (mulN (plus σ) 2).ker := Module.finite_of_fg_torsion _ (by
    intro x
    refine ⟨⟨2,by simp⟩,?_⟩
    apply Subtype.ext
    exact x.property)
  have h := Nat.eq_of_mul_eq_mul_right Nat.card_pos hc
  have hr : Module.finrank ℤ (plus (-σ)) = Module.finrank ℤ (minus σ) :=
    (LinearEquiv.ofEq _ _ (plus_neg σ)).finrank_eq
  rwa [hr] at h

include hσ in
/-- The ranks of the invariant and anti-invariant subgroups add to the
rank of the whole finitely generated group. -/
theorem rank_plus_add_minus :
    Module.finrank ℤ (plus σ) + Module.finrank ℤ (minus σ) = Module.finrank ℤ A := by
  have hk : (norm σ hσ).ker = minus σ := by
    ext x
    change (norm σ hσ x = 0) ↔ σ x+x = 0
    exact Subtype.ext_iff
  have h₁ := (norm σ hσ).ker.finrank_quotient_add_finrank
  rw [(norm σ hσ).quotKerEquivRange.finrank_eq,hk] at h₁
  have h₂ := (norm σ hσ).range.finrank_quotient_add_finrank
  letI := finite_norm_quotient σ hσ
  have hz : Module.finrank ℤ ((plus σ) ⧸ (norm σ hσ).range) = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  rw [hz,zero_add] at h₂
  rwa [h₂] at h₁

end InvolutionHerbrand

namespace InvolutionSequence
open InvolutionHerbrand
open scoped Classical

variable {U A B : Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]

/-- A short exact sequence of abelian groups with compatible involutions. -/
structure Sequence (U A B : Type*) [AddCommGroup U] [AddCommGroup A] [AddCommGroup B] where
  i : U →ₗ[ℤ] A
  p : A →ₗ[ℤ] B
  hi : Function.Injective i
  hp : Function.Surjective p
  exact : i.range = p.ker
  u : U →ₗ[ℤ] U
  a : A →ₗ[ℤ] A
  b : B →ₗ[ℤ] B
  hu : u.comp u = LinearMap.id
  ha : a.comp a = LinearMap.id
  hb : b.comp b = LinearMap.id
  iu : ∀ x, i (u x) = a (i x)
  pa : ∀ x, p (a x) = b (p x)

variable (S : Sequence U A B)

@[simp] theorem p_i (u : U) : S.p (S.i u) = 0 := by
  have h : S.i u ∈ S.p.ker := S.exact ▸ LinearMap.mem_range_self S.i u
  exact h

noncomputable def factor {C D F : Type*} [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (p : C →ₗ[ℤ] D) (hp : Function.Surjective p) (f : C →ₗ[ℤ] F) (h : p.ker ≤ f.ker) :
    D →ₗ[ℤ] F :=
  (p.ker.liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap

@[simp] theorem factor_apply {C D F : Type*} [AddCommGroup C] [AddCommGroup D] [AddCommGroup F]
    (p : C →ₗ[ℤ] D) (hp : Function.Surjective p) (f : C →ₗ[ℤ] F) (h : p.ker ≤ f.ker) (x : C) :
    factor p hp f h (p x) = f x := by
  change p.ker.liftQ f h ((p.quotKerEquivOfSurjective hp).symm (p x)) = _
  rw [← p.quotKerEquivOfSurjective_apply_mk hp x,LinearEquiv.symm_apply_apply]
  rfl

def fixedLift : Submodule ℤ A := (plus S.b).comap S.p

def pFixed : fixedLift S →ₗ[ℤ] plus S.b :=
  (S.p.domRestrict (fixedLift S)).codRestrict _ (fun x => x.property)

theorem pFixed_surjective : Function.Surjective (pFixed S) := by
  intro y
  obtain ⟨x,hx⟩ := S.hp y.1
  refine ⟨⟨x,?_⟩,Subtype.ext hx⟩
  change S.p x ∈ plus S.b
  rw [hx]
  exact y.property

def pOnFixed : plus S.a →ₗ[ℤ] plus S.b :=
  (S.p.domRestrict (plus S.a)).codRestrict _ (fun x => by
    rw [mem_plus]
    change S.b (S.p x.1) = S.p x.1
    rw [← S.pa,(mem_plus S.a _).mp x.property])

private def differenceRaw : fixedLift S →ₗ[ℤ] A :=
  (LinearMap.id-S.a).domRestrict (fixedLift S)

private theorem differenceRaw_mem (x : fixedLift S) : differenceRaw S x ∈ S.i.range := by
  rw [S.exact]
  change S.p (x.1-S.a x.1) = 0
  rw [map_sub,S.pa,(mem_plus S.b _).mp x.property,sub_self]

noncomputable def differenceLift : fixedLift S →ₗ[ℤ] U :=
  (LinearEquiv.ofInjective S.i S.hi).symm.toLinearMap.comp
    ((differenceRaw S).codRestrict S.i.range (differenceRaw_mem S))

@[simp] theorem i_differenceLift (x : fixedLift S) :
    S.i (differenceLift S x) = x.1-S.a x.1 := by
  change ((LinearEquiv.ofInjective S.i S.hi)
    ((LinearEquiv.ofInjective S.i S.hi).symm ⟨differenceRaw S x,differenceRaw_mem S x⟩)).1 = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem differenceLift_cycles (x : fixedLift S) : differenceLift S x ∈ plus (-S.u) := by
  rw [mem_plus,LinearMap.neg_apply]
  apply S.hi
  rw [map_neg,S.iu,i_differenceLift,map_sub,involutive S.a S.ha]
  abel

noncomputable def cycleLift : fixedLift S →ₗ[ℤ] plus (-S.u) :=
  (differenceLift S).codRestrict _ (differenceLift_cycles S)

abbrev H1 := plus (-S.u) ⧸ (norm (-S.u) (neg_involution S.u S.hu)).range

noncomputable def cycleClass : fixedLift S →ₗ[ℤ] H1 S :=
  (norm (-S.u) (neg_involution S.u S.hu)).range.mkQ.comp (cycleLift S)

private theorem ker_pFixed_le : (pFixed S).ker ≤ (cycleClass S).ker := by
  intro x hx
  have hpx : S.p x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨u,hu⟩ := S.exact.symm ▸ (show x.1 ∈ S.p.ker from hpx)
  change Submodule.Quotient.mk (cycleLift S x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply S.hi
  change S.i (-S.u u+u) = S.i (differenceLift S x)
  rw [i_differenceLift]
  rw [map_add,map_neg,S.iu,hu]
  abel

/-- The connecting homomorphism from fixed elements to first involution
cohomology, constructed by subtracting a lift from its conjugate. -/
noncomputable def connecting : plus S.b →ₗ[ℤ] H1 S :=
  factor (pFixed S) (pFixed_surjective S) (cycleClass S) (ker_pFixed_le S)

@[simp] theorem connecting_lift (x : fixedLift S) :
    connecting S (pFixed S x) = Submodule.Quotient.mk (cycleLift S x) :=
  factor_apply _ _ _ _ x

/-- Exactness at the fixed elements of the quotient. -/
theorem ker_connecting : (connecting S).ker = (pOnFixed S).range := by
  ext y
  obtain ⟨x,rfl⟩ := pFixed_surjective S y
  change connecting S (pFixed S x) = 0 ↔ _
  rw [connecting_lift,Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u,hu⟩
    have hdu : S.i u-S.a (S.i u) = x.1-S.a x.1 := by
      have h := congrArg (fun z : plus (-S.u) => S.i z.1) hu
      change S.i (-S.u u+u) = S.i (differenceLift S x) at h
      rw [map_add,map_neg,S.iu,i_differenceLift] at h
      convert h using 1 <;> abel
    have hz : x.1-S.i u ∈ plus S.a := by
      rw [mem_plus,map_sub]
      calc
        S.a x.1-S.a (S.i u) = S.a x.1+(S.i u-S.a (S.i u))-S.i u := by abel
        _ = S.a x.1+(x.1-S.a x.1)-S.i u := by rw [hdu]
        _ = x.1-S.i u := by abel
    refine ⟨⟨x.1-S.i u,hz⟩,Subtype.ext ?_⟩
    change S.p (x.1-S.i u) = S.p x.1
    rw [map_sub,p_i,sub_zero]
  · rintro ⟨z,hz⟩
    have hpz : S.p z.1 = S.p x.1 := congrArg Subtype.val hz
    have hxz : x.1-z.1 ∈ S.p.ker := by rw [LinearMap.mem_ker,map_sub,hpz,sub_self]
    obtain ⟨u,hu⟩ := S.exact.symm ▸ hxz
    refine ⟨u,?_⟩
    apply Subtype.ext
    apply S.hi
    change S.i (-S.u u+u) = S.i (differenceLift S x)
    rw [i_differenceLift]
    rw [map_add,map_neg,S.iu,hu,map_sub,(mem_plus S.a _).mp z.property]
    abel

/-- If every anti-invariant middle element is a difference, the connecting
homomorphism is onto. This is the form used with Hilbert's Theorem 90. -/
theorem connecting_surjective
    (h90 : ∀ z : A, -S.a z = z → ∃ x, x-S.a x = z) :
    Function.Surjective (connecting S) := by
  intro c
  obtain ⟨u,rfl⟩ := (norm (-S.u) (neg_involution S.u S.hu)).range.mkQ_surjective c
  have hu : -S.a (S.i u.1) = S.i u.1 := by
    have hf := (mem_plus (-S.u) _).mp u.property
    change -S.u u.1 = u.1 at hf
    rw [← S.iu,← map_neg,hf]
  obtain ⟨x,hx⟩ := h90 (S.i u.1) hu
  have hpx : x ∈ fixedLift S := by
    change S.p x ∈ plus S.b
    rw [mem_plus]
    have h := congrArg S.p hx
    rw [map_sub,S.pa,p_i] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨pFixed S ⟨x,hpx⟩,?_⟩
  rw [connecting_lift]
  congr 1
  apply Subtype.ext
  apply S.hi
  exact (i_differenceLift S ⟨x,hpx⟩).trans hx

end InvolutionSequence

namespace InvolutionSequence
open InvolutionHerbrand
open scoped Classical

variable {U A B : Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S : Sequence U A B)

/-- Negating all three involutions interchanges norms and differences. -/
def Sequence.neg : Sequence U A B where
  i := S.i
  p := S.p
  hi := S.hi
  hp := S.hp
  exact := S.exact
  u := -S.u
  a := -S.a
  b := -S.b
  hu := neg_involution S.u S.hu
  ha := neg_involution S.a S.ha
  hb := neg_involution S.b S.hb
  iu x := by change S.i (-S.u x) = -S.a (S.i x); rw [map_neg,S.iu]
  pa x := by change S.p (-S.a x) = -S.b (S.p x); rw [map_neg,S.pa]

variable (h90 : ∀ z : A, -S.a z = z → ∃ x, x-S.a x = z)

include h90 in
/-- When the middle term has trivial first cohomology, the kernel of the
opposite connecting map consists exactly of differences in the quotient. -/
theorem ker_opposite_connecting :
    (connecting S.neg).ker = (norm (-S.b) (neg_involution S.b S.hb)).range := by
  rw [ker_connecting]
  ext y
  constructor
  · rintro ⟨a,ha⟩
    have ha' : -S.a a.1 = a.1 := (mem_plus (-S.a) _).mp a.property
    obtain ⟨x,hx⟩ := h90 a.1 ha'
    refine ⟨S.p x,Subtype.ext ?_⟩
    have h := congrArg Subtype.val ha
    change S.p a.1 = y.1 at h
    change -S.b (S.p x)+S.p x = y.1
    rw [← h,← hx,map_sub,S.pa]
    abel
  · rintro ⟨b,rfl⟩
    obtain ⟨a,ha⟩ := S.hp b
    have hm : a-S.a a ∈ plus S.neg.a := by
      rw [mem_plus]
      change -S.a (a-S.a a) = a-S.a a
      rw [map_sub,involutive S.a S.ha]
      abel
    refine ⟨⟨a-S.a a,hm⟩,Subtype.ext ?_⟩
    change S.p (a-S.a a) = -S.b b+b
    rw [map_sub,S.pa,ha]
    abel

abbrev quotientH1 := plus (-S.b) ⧸ (norm (-S.b) (neg_involution S.b S.hb)).range

/-- The first cohomology of the quotient embeds in the zeroth Tate
cohomology of the kernel, assuming Hilbert 90 in the middle term. -/
noncomputable def oppositeEmbedding : quotientH1 S →ₗ[ℤ] H1 S.neg :=
  (norm (-S.b) (neg_involution S.b S.hb)).range.liftQ (connecting S.neg)
    (le_of_eq (ker_opposite_connecting S h90).symm)

theorem oppositeEmbedding_injective : Function.Injective (oppositeEmbedding S h90) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (ker_opposite_connecting S h90).symm

include h90 in
theorem card_quotientH1_le [Finite (H1 S.neg)] :
    Nat.card (quotientH1 S) ≤ Nat.card (H1 S.neg) :=
  Nat.card_le_card_of_injective _ (oppositeEmbedding_injective S h90)

end InvolutionSequence

namespace InvolutionSequence
open InvolutionHerbrand
open scoped Classical

variable {U A B : Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S : Sequence U A B)

def iOnFixed : plus S.u →ₗ[ℤ] plus S.a :=
  (S.i.domRestrict (plus S.u)).codRestrict _ (fun x => by
    rw [mem_plus]
    change S.a (S.i x.1) = S.i x.1
    rw [← S.iu,(mem_plus S.u _).mp x.property])

theorem iOnFixed_injective : Function.Injective (iOnFixed S) := by
  intro x y h
  exact Subtype.ext (S.hi (congrArg Subtype.val h))

/-- Taking invariants preserves exactness on the left. -/
theorem ker_pOnFixed : (pOnFixed S).ker = (iOnFixed S).range := by
  ext x
  constructor
  · intro hx
    have hpx : S.p x.1 = 0 := congrArg Subtype.val hx
    obtain ⟨u,hu⟩ := S.exact.symm ▸ (show x.1 ∈ S.p.ker from hpx)
    have huf : u ∈ plus S.u := by
      rw [mem_plus]
      apply S.hi
      rw [S.iu,hu,(mem_plus S.a _).mp x.property]
    exact ⟨⟨u,huf⟩,Subtype.ext hu⟩
  · rintro ⟨u,rfl⟩
    apply Subtype.ext
    exact p_i S u.1

/-- Counting a quotient by a submodule transported through an injection. -/
theorem card_quotient_map (j : A →ₗ[ℤ] B) (hj : Function.Injective j) (V : Submodule ℤ A) :
    Nat.card (B ⧸ V.map j) = Nat.card (A ⧸ V) * Nat.card (B ⧸ j.range) := by
  let f := (V.map j).mkQ.comp j
  have hk : f.ker = V := by
    rw [LinearMap.ker_comp,Submodule.ker_mkQ,Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr hj,sup_bot_eq]
  have hr : f.range = j.range.map (V.map j).mkQ := LinearMap.range_comp _ _
  have he : (A ⧸ V) ≃ₗ[ℤ] (j.range.map (V.map j).mkQ) :=
    (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))
  rw [Nat.card_congr he.toEquiv]
  exact (Submodule.card_quotient_mul_card_quotient j.range (V.map j) (by rintro _ ⟨a,ha,rfl⟩; exact ⟨a,rfl⟩)).symm

end InvolutionSequence

namespace InvolutionSequence
open InvolutionHerbrand
open scoped Classical

variable {U A B : Type*} [AddCommGroup U] [AddCommGroup A] [AddCommGroup B]
  (S : Sequence U A B)

/-- Surjectivity of the opposite connecting map means that every invariant
kernel element is the norm of an element of the middle group. -/
theorem exists_norm_of_opposite_surjective (hc : Function.Surjective (connecting S.neg))
    (u : plus S.u) : ∃ x : A, x+S.a x = S.i u.1 := by
  let u' : plus (-S.neg.u) := ⟨u.1,by
    rw [mem_plus]
    change -(-S.u u.1) = u.1
    simpa only [neg_neg] using (mem_plus S.u _).mp u.property⟩
  obtain ⟨b,hb⟩ := hc (Submodule.Quotient.mk u')
  obtain ⟨x,rfl⟩ := pFixed_surjective S.neg b
  rw [connecting_lift] at hb
  obtain ⟨v,hv⟩ := (Submodule.Quotient.eq _).mp hb
  have h := congrArg (fun z : plus (-S.neg.u) => S.i z.1) hv
  change S.i (-(-S.u v)+v) = S.i (differenceLift S.neg x-u.1) at h
  rw [neg_neg,map_add,map_sub,S.iu] at h
  have hd := i_differenceLift S.neg x
  change S.i (differenceLift S.neg x) = x.1-(-S.a x.1) at hd
  rw [hd,sub_neg_eq_add] at h
  refine ⟨x.1-S.i v,?_⟩
  rw [map_sub]
  calc
    _ = (x.1+S.a x.1)-(S.a (S.i v)+S.i v) := by abel
    _ = S.i u.1 := by rw [h]; abel

end InvolutionSequence

namespace QuadraticUnitHerbrand
open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev UnitModule := Additive (𝓞 K)ˣ

/-- The integral rank of the full unit group is the Dirichlet unit rank. -/
theorem rank_units : Module.finrank ℤ (UnitModule K) = NumberField.Units.rank K := by
  letI := AddCommGroup.toIntModule (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
  let q : UnitModule K →ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    AddMonoidHom.toIntLinearMap (M := UnitModule K)
      (M₂ := Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K))
      (MonoidHom.toAdditive (QuotientGroup.mk' (NumberField.Units.torsion K)))
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion K) x.toMul
    exact ⟨Additive.ofMul u,congrArg Additive.ofMul hu⟩
  have hk : Finite q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    exact inferInstanceAs (Finite (NumberField.Units.torsion K))
  have hr := q.ker.finrank_quotient_add_finrank
  rw [(q.quotKerEquivOfSurjective hq).finrank_eq,NumberField.Units.rank_modTorsion] at hr
  have hz : Module.finrank ℤ q.ker = 0 :=
    Module.finrank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  exact (by simpa only [hz,add_zero] using hr.symm)

variable (E : Type*) [Field E] [NumberField E] [Algebra K E]

noncomputable def extend : (𝓞 K)ˣ →* (𝓞 E)ˣ :=
  Units.map (algebraMap (𝓞 K) (𝓞 E))

@[simp] theorem coe_extend (u : (𝓞 K)ˣ) : (extend K E u : E) = algebraMap K E (u : K) := rfl

theorem extend_injective : Function.Injective (extend K E) := by
  intro u v h
  exact NumberField.Units.coe_injective K ((algebraMap K E).injective
    (congrArg (fun u : (𝓞 E)ˣ => (u : E)) h))

/-- A unit upstairs whose value lies in the base field is already a unit
of the base ring of integers. -/
theorem unit_descends (u : (𝓞 E)ˣ) (hu : (u : E) ∈ Set.range (algebraMap K E)) :
    ∃ v : (𝓞 K)ˣ, extend K E v = u := by
  obtain ⟨x,hx⟩ := hu
  have hxi : IsIntegral ℤ x := (isIntegral_algebraMap_iff (R := ℤ)
    (algebraMap K E).injective).mp (hx ▸ (u : 𝓞 E).property)
  have hx0 : x ≠ 0 := by
    intro h
    have h0 := NumberField.Units.coe_ne_zero u
    exact h0 (hx.symm.trans (by simp [h]))
  have huinv : ((u⁻¹ : (𝓞 E)ˣ) : E) = (u : E)⁻¹ := by
    simpa using NumberField.Units.coe_zpow u (-1)
  have hxinv : algebraMap K E x⁻¹ = ((u⁻¹ : (𝓞 E)ˣ) : E) := by
    rw [map_inv₀,hx,huinv]
  have hxii : IsIntegral ℤ x⁻¹ := (isIntegral_algebraMap_iff (R := ℤ)
    (algebraMap K E).injective).mp (hxinv ▸ ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).property)
  let v : (𝓞 K)ˣ := Units.mkOfMulEqOne ⟨x,hxi⟩ ⟨x⁻¹,hxii⟩ (by
    apply RingOfIntegers.coe_injective
    exact mul_inv_cancel₀ hx0)
  refine ⟨v,NumberField.Units.coe_injective E ?_⟩
  exact hx

variable (σ : E ≃ₐ[K] E)

noncomputable def action : UnitModule E →ₗ[ℤ] UnitModule E :=
  (MonoidHom.toAdditive (Units.map (RingOfIntegers.mapRingHom σ.toRingHom))).toIntLinearMap

@[simp] theorem coe_action (u : UnitModule E) :
    ((action K E σ u).toMul : E) = σ (u.toMul : E) := rfl

@[simp] theorem action_extend (u : (𝓞 K)ˣ) :
    action K E σ (Additive.ofMul (extend K E u)) = Additive.ofMul (extend K E u) := by
  apply Additive.toMul.injective
  apply NumberField.Units.coe_injective E
  exact σ.commutes (u : K)

variable [FiniteDimensional K E] [IsGalois K E]
variable (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

include hdeg hne in
theorem aut_eq_one_or (τ : E ≃ₐ[K] E) : τ = 1 ∨ τ = σ := by
  obtain ⟨z,hz,huniq⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).mp
    ((IsGalois.card_aut_eq_finrank K E).trans hdeg)
  by_cases hτ : τ = 1
  · exact Or.inl hτ
  · exact Or.inr ((huniq τ hτ).trans (huniq σ hne).symm)

include hdeg in
theorem action_involutive :
    (action K E σ).comp (action K E σ) = LinearMap.id := by
  have hp : σ^2 = 1 := by
    rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
    exact pow_card_eq_one'
  apply LinearMap.ext
  intro u
  change action K E σ (action K E σ u) = u
  apply Additive.toMul.injective
  apply NumberField.Units.coe_injective E
  change σ (σ (u.toMul : E)) = (u.toMul : E)
  exact congrArg (fun τ : E ≃ₐ[K] E => τ (u.toMul : E)) (by simpa [pow_two] using hp)

include hdeg hne in
/-- The invariant unit group of a quadratic extension is precisely the
unit group of the base field. -/
noncomputable def fixedEquiv : UnitModule K ≃ₗ[ℤ] InvolutionHerbrand.plus (action K E σ) := by
  let f : UnitModule K →ₗ[ℤ] UnitModule E := (MonoidHom.toAdditive (extend K E)).toIntLinearMap
  let g := f.codRestrict (InvolutionHerbrand.plus (action K E σ)) (fun u =>
    (InvolutionHerbrand.mem_plus _ _).mpr (action_extend K E σ u.toMul))
  apply LinearEquiv.ofBijective g
  constructor
  · intro u v h
    exact extend_injective K E (congrArg (fun x : InvolutionHerbrand.plus (action K E σ) => x.1.toMul) h)
  · intro u
    have hfix := (InvolutionHerbrand.mem_plus _ _).mp u.2
    have hu : (u.1.toMul : E) ∈ Set.range (algebraMap K E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases aut_eq_one_or K E σ hdeg hne τ with rfl | rfl
      · rfl
      · exact congrArg (fun u : UnitModule E => (u.toMul : E)) hfix
    obtain ⟨v,hv⟩ := unit_descends K E u.1.toMul hu
    exact ⟨Additive.ofMul v,Subtype.ext hv⟩

include hdeg hne in
/-- The invariant units have the base-field Dirichlet rank. -/
theorem rank_fixed :
    Module.finrank ℤ (InvolutionHerbrand.plus (action K E σ)) = NumberField.Units.rank K := by
  rw [← (fixedEquiv K E σ hdeg hne).finrank_eq,rank_units]

include hdeg hne in
/-- The norm-one units have the complementary Dirichlet rank. -/
theorem rank_norm_one :
    Module.finrank ℤ (InvolutionHerbrand.minus (action K E σ)) + NumberField.Units.rank K =
      NumberField.Units.rank E := by
  have h := InvolutionHerbrand.rank_plus_add_minus (action K E σ) (action_involutive K E σ hdeg)
  rw [rank_fixed K E σ hdeg hne,rank_units] at h
  rwa [add_comm] at h

end QuadraticUnitHerbrand

namespace QuadraticUnitHerbrand
open NumberField
open scoped Classical

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

abbrev H0 := InvolutionHerbrand.plus (action K E σ) ⧸
  (InvolutionHerbrand.norm (action K E σ) (action_involutive K E σ hdeg)).range

abbrev H1 := InvolutionHerbrand.plus (-action K E σ) ⧸
  (InvolutionHerbrand.norm (-action K E σ)
    (InvolutionHerbrand.neg_involution (action K E σ) (action_involutive K E σ hdeg))).range

theorem finite_H0 : Finite (H0 K E σ hdeg) :=
  InvolutionHerbrand.finite_norm_quotient _ _

theorem finite_H1 : Finite (H1 K E σ hdeg) :=
  InvolutionHerbrand.finite_norm_quotient _ _

include hdeg in
theorem rank_twice_add_one [IsTotallyReal K] [IsTotallyReal E] :
    NumberField.Units.rank E = 2*NumberField.Units.rank K+1 := by
  have hK := IsTotallyReal.finrank K
  have hE := IsTotallyReal.finrank E
  have hzK := IsTotallyReal.nrComplexPlaces_eq_zero K
  have hzE := IsTotallyReal.nrComplexPlaces_eq_zero E
  have hd := Module.finrank_mul_finrank ℚ K E
  rw [hdeg] at hd
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [NumberField.Units.rank,NumberField.Units.rank,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

include hne in
/-- The unit Herbrand quotient of a totally real quadratic extension is
one half, expressed as an exact identity of finite cardinalities. -/
theorem herbrand [IsTotallyReal K] [IsTotallyReal E] :
    Nat.card (H1 K E σ hdeg) = 2*Nat.card (H0 K E σ hdeg) := by
  have h := InvolutionHerbrand.herbrand_identity_fg (action K E σ) (action_involutive K E σ hdeg)
  have hm := rank_norm_one K E σ hdeg hne
  rw [rank_twice_add_one K E hdeg] at hm
  have hmr : Module.finrank ℤ (InvolutionHerbrand.minus (action K E σ)) =
      NumberField.Units.rank K+1 := by omega
  rw [rank_fixed K E σ hdeg hne,hmr,pow_succ] at h
  change Nat.card (H0 K E σ hdeg) * (2^NumberField.Units.rank K*2) =
    Nat.card (H1 K E σ hdeg) * 2^NumberField.Units.rank K at h
  apply (Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^NumberField.Units.rank K))
  nlinarith [h]

include hdeg hne in
theorem norm_eq_mul (x : E) : algebraMap K E (Algebra.norm K x) = σ x*x := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  have he : (Finset.univ : Finset (E ≃ₐ[K] E)) = {σ,1} := by
    ext τ
    simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
    exact (aut_eq_one_or K E σ hdeg hne τ).symm
  rw [he,Finset.prod_pair hne]
  rfl

noncomputable def unitNorm : (𝓞 E)ˣ →* (𝓞 K)ˣ := Units.map (RingOfIntegers.norm K)

noncomputable def normLinear : UnitModule E →ₗ[ℤ] UnitModule K :=
  (MonoidHom.toAdditive (unitNorm K E)).toIntLinearMap

include hdeg hne in
theorem extend_unitNorm (u : (𝓞 E)ˣ) :
    extend K E (unitNorm K E u) = (action K E σ (Additive.ofMul u)).toMul*u := by
  apply NumberField.Units.coe_injective E
  exact norm_eq_mul K E σ hdeg hne (u : E)

include hne in
/-- Identify the fixed-unit norm map with the ordinary relative unit norm. -/
theorem fixedEquiv_norm (u : UnitModule E) :
    fixedEquiv K E σ hdeg hne (normLinear K E u) =
      InvolutionHerbrand.norm (action K E σ) (action_involutive K E σ hdeg) u := by
  apply Subtype.ext
  exact extend_unitNorm K E σ hdeg hne u.toMul

include hne in
noncomputable def normQuotientEquiv :
    (UnitModule K ⧸ (normLinear K E).range) ≃ₗ[ℤ] H0 K E σ hdeg :=
  Submodule.Quotient.equiv _ _ (fixedEquiv K E σ hdeg hne) (by
    rw [← LinearMap.range_comp]
    congr 1
    apply LinearMap.ext
    exact fixedEquiv_norm K E σ hdeg hne)

include hne in
theorem card_H1 [IsTotallyReal K] [IsTotallyReal E] :
    Nat.card (H1 K E σ hdeg) = 2*Nat.card (UnitModule K ⧸ (normLinear K E).range) := by
  rw [herbrand K E σ hdeg hne,Nat.card_congr (normQuotientEquiv K E σ hdeg hne).toEquiv]

end QuadraticUnitHerbrand

/-! Galois actions on fractional ideals and their principal subgroups. -/
namespace FractionalGalois
open NumberField
open scoped Classical nonZeroDivisors

variable (E : Type*) [Field E] [NumberField E]

abbrev Ideals := (FractionalIdeal (𝓞 E)⁰ E)ˣ

variable (σ : E ≃+* E)

noncomputable def actionHom : FractionalIdeal (𝓞 E)⁰ E →+* FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.extendedHom E
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (RingOfIntegers.mapRingEquiv σ).injective)

private theorem localization_map :
    IsLocalization.map (S := E) E (RingOfIntegers.mapRingHom σ.toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (RingOfIntegers.mapRingEquiv σ).injective) = σ.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := 𝓞 E)
  intro a
  exact IsLocalization.map_eq _ a

/-- The transported ideal is the ordinary image under the field automorphism. -/
theorem mem_actionHom (I : FractionalIdeal (𝓞 E)⁰ E) (x : E) :
    x ∈ actionHom E σ I ↔ σ.symm x ∈ I := by
  change x ∈ (I.extended E _) ↔ _
  rw [FractionalIdeal.mem_extended_iff]
  change x ∈ Submodule.span (𝓞 E)
    ((IsLocalization.map (S := E) E (RingOfIntegers.mapRingHom σ.toRingHom)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (RingOfIntegers.mapRingEquiv σ).injective)) '' (I : Set E)) ↔ _
  rw [localization_map E σ]
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => σ.symm x ∈ I) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a,ha,rfl⟩
      change σ.symm (σ a) ∈ I
      simpa only [RingEquiv.symm_apply_apply] using ha
    · simpa only [map_zero] using I.coeToSubmodule.zero_mem
    · intro a b ha hb h₁ h₂
      simpa only [map_add] using I.coeToSubmodule.add_mem h₁ h₂
    · intro a b hb h
      change σ.symm ((a : E)*b) ∈ I
      rw [map_mul]
      exact I.coeToSubmodule.smul_mem (RingOfIntegers.mapRingEquiv σ.symm a) h
  · intro hx
    exact Submodule.subset_span ⟨σ.symm x,hx,σ.apply_symm_apply x⟩

@[simp] theorem actionHom_symm (I : FractionalIdeal (𝓞 E)⁰ E) :
    actionHom E σ.symm (actionHom E σ I) = I := by
  ext x
  rw [mem_actionHom,mem_actionHom]
  simp

noncomputable def actionEquiv : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E :=
  RingEquiv.ofRingHom (actionHom E σ) (actionHom E σ.symm)
    (RingHom.ext (fun I => by simpa using actionHom_symm E σ.symm I))
    (RingHom.ext (actionHom_symm E σ))

noncomputable def action : Ideals E ≃* Ideals E := Units.mapEquiv (actionEquiv E σ).toMulEquiv

theorem actionHom_span (x : E) :
    actionHom E σ (FractionalIdeal.spanSingleton (𝓞 E)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (σ x) := by
  ext y
  rw [mem_actionHom,FractionalIdeal.mem_spanSingleton,FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨RingOfIntegers.mapRingEquiv σ a,?_⟩
    have h := congrArg σ ha
    simpa only [Algebra.smul_def,map_mul,RingEquiv.apply_symm_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨RingOfIntegers.mapRingEquiv σ.symm a,?_⟩
    have h := congrArg σ.symm ha
    simpa only [Algebra.smul_def,map_mul,RingEquiv.symm_apply_apply] using h

noncomputable def fieldAction : Eˣ ≃* Eˣ := Units.mapEquiv σ.toMulEquiv

@[simp] theorem action_principal (x : Eˣ) :
    action E σ (toPrincipalIdeal (𝓞 E) E x) = toPrincipalIdeal (𝓞 E) E (fieldAction E σ x) := by
  apply Units.ext
  change actionHom E σ (toPrincipalIdeal (𝓞 E) E x : FractionalIdeal (𝓞 E)⁰ E) = _
  rw [coe_toPrincipalIdeal,coe_toPrincipalIdeal]
  exact actionHom_span E σ x

noncomputable def integerUnits : (𝓞 E)ˣ →* Eˣ := Units.map (algebraMap (𝓞 E) E)

theorem integerUnits_injective : Function.Injective (integerUnits E) :=
  Units.map_injective RingOfIntegers.coe_injective

/-- A principal fractional ideal is trivial precisely when its generator
is an integral unit. -/
theorem principal_eq_one_iff (x : Eˣ) :
    toPrincipalIdeal (𝓞 E) E x = 1 ↔ x ∈ (integerUnits E).range := by
  rw [toPrincipalIdeal_eq_iff]
  simp only [Units.val_one]
  rw [← FractionalIdeal.spanSingleton_one (S := (𝓞 E)⁰)]
  rw [eq_comm,FractionalIdeal.spanSingleton_eq_spanSingleton]
  constructor
  · rintro ⟨u,hu⟩
    change (u : E)*1 = (x : E) at hu
    exact ⟨u,Units.ext (by simpa only [mul_one] using hu)⟩
  · rintro ⟨u,hu⟩
    refine ⟨u,?_⟩
    have h := congrArg Units.val hu
    change (u : E)*1 = (x : E)
    simpa only [mul_one] using h

end FractionalGalois

namespace FractionalGalois
open NumberField
open scoped Classical nonZeroDivisors

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

noncomputable def extend : Ideals K →* Ideals E :=
  Units.map (FractionalIdeal.extendedHomₐ E (𝓞 E)).toMonoidHom

noncomputable def fieldExtend : Kˣ →* Eˣ := Units.map (algebraMap K E).toMonoidHom

theorem extend_injective : Function.Injective (extend K E) :=
  Units.map_injective (FractionalIdeal.extendedHomₐ_injective (L := E) (B := 𝓞 E) (A := 𝓞 K) (K := K))

theorem extend_span (x : K) :
    FractionalIdeal.extendedHomₐ E (𝓞 E) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap K E x) := by
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHomₐ E (𝓞 E) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) :
    Submodule (𝓞 E) E) =
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap K E x) : Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHomₐ_eq_span,FractionalIdeal.coe_spanSingleton]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨y,hy,rfl⟩
    obtain ⟨r,hr⟩ := (FractionalIdeal.mem_spanSingleton (𝓞 K)⁰).mp hy
    rw [← hr]
    change algebraMap K E ((r : K)*x) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _ (algebraMap (𝓞 K) (𝓞 E) r)
      (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro _ ⟨rfl⟩
    exact Submodule.subset_span ⟨x,FractionalIdeal.mem_spanSingleton_self _ _,rfl⟩

@[simp] theorem extend_principal (x : Kˣ) :
    extend K E (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 E) E (fieldExtend K E x) := by
  apply Units.ext
  change FractionalIdeal.extendedHomₐ E (𝓞 E)
    (toPrincipalIdeal (𝓞 K) K x : FractionalIdeal (𝓞 K)⁰ K) = _
  rw [coe_toPrincipalIdeal,coe_toPrincipalIdeal]
  exact extend_span K E x

variable (σ : E ≃ₐ[K] E)

theorem extend_fixed (I : Ideals K) : action E σ.toRingEquiv (extend K E I) = extend K E I := by
  apply Units.ext
  change actionHom E σ.toRingEquiv (FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) =
    FractionalIdeal.extendedHomₐ E (𝓞 E) I.1
  have hstable (τ : E ≃ₐ[K] E) (x : E)
      (hx : x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) :
      τ x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) I.1 := by
    change x ∈ ((FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) : Submodule (𝓞 E) E) at hx
    change τ x ∈ ((FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hx ⊢
    refine Submodule.span_induction (p := fun x _ => τ x ∈
      Submodule.span (𝓞 E) (algebraMap K E '' (I.1 : Set K))) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨y,hy,rfl⟩
      rw [τ.commutes]
      exact Submodule.subset_span ⟨y,hy,rfl⟩
    · simpa only [map_zero] using Submodule.zero_mem _
    · intro a b ha hb h₁ h₂
      simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    · intro a b hb h
      change τ ((a : E)*b) ∈ _
      rw [map_mul]
      exact Submodule.smul_mem _ (RingOfIntegers.mapAlgEquiv τ a) h
  ext x
  rw [mem_actionHom]
  constructor
  · intro h
    change σ.symm x ∈ _ at h
    simpa only [AlgEquiv.apply_symm_apply] using hstable σ (σ.symm x) h
  · exact hstable σ.symm x

end FractionalGalois

namespace FractionalClasses
open NumberField FractionalGalois
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

abbrev Classes := Ideals K ⧸ (toPrincipalIdeal (𝓞 K) K).range

noncomputable def equiv : Classes K ≃* ClassGroup (𝓞 K) := (ClassGroup.equiv K).symm

instance : Finite (Classes K) := Finite.of_equiv (ClassGroup (𝓞 K)) (equiv K).symm.toEquiv

noncomputable def mk : Ideals K →* Classes K := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk K) := QuotientGroup.mk'_surjective _

@[simp] theorem mk_eq_one (I : Ideals K) : mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range :=
  QuotientGroup.eq_one_iff I

@[simp] theorem mk_principal (x : Kˣ) : mk K (toPrincipalIdeal (𝓞 K) K x) = 1 :=
  (mk_eq_one K _).mpr ⟨x,rfl⟩

variable (E : Type*) [Field E] [NumberField E] [Algebra K E]

noncomputable def extend : Classes K →* Classes E :=
  QuotientGroup.map _ _ (FractionalGalois.extend K E) (by
    rintro _ ⟨x,rfl⟩
    exact ⟨fieldExtend K E x,(extend_principal K E x).symm⟩)

@[simp] theorem extend_mk (I : Ideals K) :
    extend K E (mk K I) = mk E (FractionalGalois.extend K E I) := rfl

variable (σ : E ≃ₐ[K] E)

noncomputable def action : Classes E →* Classes E :=
  QuotientGroup.map _ _ (FractionalGalois.action E σ.toRingEquiv).toMonoidHom (by
    rintro _ ⟨x,rfl⟩
    exact ⟨fieldAction E σ.toRingEquiv x,(action_principal E σ.toRingEquiv x).symm⟩)

@[simp] theorem action_mk (I : Ideals E) :
    action K E σ (mk E I) = mk E (FractionalGalois.action E σ.toRingEquiv I) := rfl

@[simp] theorem extend_fixed (c : Classes K) : action K E σ (extend K E c) = extend K E c := by
  obtain ⟨I,rfl⟩ := mk_surjective K c
  rw [extend_mk,action_mk,FractionalGalois.extend_fixed]

end FractionalClasses

namespace PrincipalInvolutionSequences
open NumberField InvolutionHerbrand FractionalGalois
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2)

abbrev U := Additive (𝓞 E)ˣ
abbrev F := Additive Eˣ
abbrev P := Additive (toPrincipalIdeal (𝓞 E) E).range
abbrev D := Additive (Ideals E)
abbrev C := Additive (FractionalClasses.Classes E)

noncomputable instance : Module ℤ (C E) := AddCommGroup.toIntModule (C E)

noncomputable def fAction : F E →ₗ[ℤ] F E :=
  (MonoidHom.toAdditive (fieldAction E σ.toRingEquiv).toMonoidHom).toIntLinearMap

noncomputable def dAction : D E →ₗ[ℤ] D E :=
  (MonoidHom.toAdditive (FractionalGalois.action E σ.toRingEquiv).toMonoidHom).toIntLinearMap

noncomputable def pActionHom :
    (toPrincipalIdeal (𝓞 E) E).range →* (toPrincipalIdeal (𝓞 E) E).range :=
  (((FractionalGalois.action E σ.toRingEquiv).toMonoidHom).comp
    (toPrincipalIdeal (𝓞 E) E).range.subtype).codRestrict _ (fun p => by
      obtain ⟨x,hx⟩ := p.property
      refine ⟨fieldAction E σ.toRingEquiv x,?_⟩
      change toPrincipalIdeal (𝓞 E) E (fieldAction E σ.toRingEquiv x) =
        FractionalGalois.action E σ.toRingEquiv p.1
      rw [← action_principal,hx])

noncomputable def pAction : P E →ₗ[ℤ] P E :=
  (MonoidHom.toAdditive (pActionHom K E σ)).toIntLinearMap

noncomputable def cAction : C E →ₗ[ℤ] C E :=
  AddMonoidHom.toIntLinearMap (M := C E) (M₂ := C E)
    (MonoidHom.toAdditive (FractionalClasses.action K E σ))

noncomputable def inclusionUnits : U E →ₗ[ℤ] F E :=
  (MonoidHom.toAdditive (integerUnits E)).toIntLinearMap

noncomputable def principal : F E →ₗ[ℤ] P E :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 E) E).rangeRestrict).toIntLinearMap

noncomputable def inclusionPrincipal : P E →ₗ[ℤ] D E :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 E) E).range.subtype).toIntLinearMap

noncomputable def classMap : D E →ₗ[ℤ] C E :=
  AddMonoidHom.toIntLinearMap (M := D E) (M₂ := C E)
    (MonoidHom.toAdditive (FractionalClasses.mk E))

include hdeg in
theorem sigma_involutive (x : E) : σ (σ x) = x := by
  have hp : σ^2 = 1 := by
    rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
    exact pow_card_eq_one'
  exact congrArg (fun τ : E ≃ₐ[K] E => τ x) (by simpa [pow_two] using hp)

include hdeg in
theorem fAction_involutive : (fAction K E σ).comp (fAction K E σ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  exact sigma_involutive K E σ hdeg x.toMul

include hdeg in
theorem dAction_involutive : (dAction K E σ).comp (dAction K E σ) = LinearMap.id := by
  have hs : σ.toRingEquiv.symm = σ.toRingEquiv := by
    ext x
    have h := sigma_involutive K E σ hdeg (σ.symm x)
    simpa only [AlgEquiv.apply_symm_apply] using h.symm
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  change actionHom E σ.toRingEquiv (actionHom E σ.toRingEquiv x.toMul.1) = x.toMul.1
  simpa only [hs] using actionHom_symm E σ.toRingEquiv x.toMul.1

include hdeg in
theorem pAction_involutive : (pAction K E σ).comp (pAction K E σ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  have h := LinearMap.congr_fun (dAction_involutive K E σ hdeg) (Additive.ofMul x.toMul.1)
  exact congrArg Additive.toMul h

include hdeg in
theorem cAction_involutive : (cAction K E σ).comp (cAction K E σ) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨I,hI⟩ := FractionalClasses.mk_surjective E x.toMul
  have hi : classMap E (Additive.ofMul I) = x := congrArg Additive.ofMul hI
  rw [← hi]
  have h := LinearMap.congr_fun (dAction_involutive K E σ hdeg) (Additive.ofMul I)
  exact congrArg (classMap E) h

/-- Units, field elements and principal ideals form a short exact sequence
of involution modules. -/
noncomputable def unitsSequence : InvolutionSequence.Sequence (U E) (F E) (P E) where
  i := inclusionUnits E
  p := principal E
  hi := integerUnits_injective E
  hp x := by
    obtain ⟨a,ha⟩ := x.toMul.property
    exact ⟨Additive.ofMul a,congrArg Additive.ofMul (Subtype.ext ha)⟩
  exact := by
    ext x
    change (∃ u : U E, inclusionUnits E u = x) ↔ principal E x = 0
    change (∃ u : (𝓞 E)ˣ, integerUnits E u = x.toMul) ↔
      (toPrincipalIdeal (𝓞 E) E).rangeRestrict x.toMul = 1
    rw [Subtype.ext_iff]
    exact (principal_eq_one_iff E x.toMul).symm
  u := QuadraticUnitHerbrand.action K E σ
  a := fAction K E σ
  b := pAction K E σ
  hu := QuadraticUnitHerbrand.action_involutive K E σ hdeg
  ha := fAction_involutive K E σ hdeg
  hb := pAction_involutive K E σ hdeg
  iu x := by
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  pa x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (action_principal E σ.toRingEquiv x.toMul).symm

/-- Principal ideals, fractional ideals and ideal classes form the second
short exact sequence of involution modules. -/
noncomputable def idealsSequence : InvolutionSequence.Sequence (P E) (D E) (C E) where
  i := inclusionPrincipal E
  p := classMap E
  hi := fun x y h => congrArg Additive.ofMul (Subtype.ext (congrArg Additive.toMul h))
  hp x := by
    obtain ⟨I,hI⟩ := FractionalClasses.mk_surjective E x.toMul
    exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩
  exact := by
    ext x
    change (∃ p : P E, inclusionPrincipal E p = x) ↔ classMap E x = 0
    change (∃ p : (toPrincipalIdeal (𝓞 E) E).range, p.1 = x.toMul) ↔
      FractionalClasses.mk E x.toMul = 1
    rw [FractionalClasses.mk_eq_one]
    constructor
    · rintro ⟨p,hp⟩; exact hp ▸ p.property
    · intro hx; exact ⟨⟨x.toMul,hx⟩,rfl⟩
  u := pAction K E σ
  a := dAction K E σ
  b := cAction K E σ
  hu := pAction_involutive K E σ hdeg
  ha := dAction_involutive K E σ hdeg
  hb := cAction_involutive K E σ hdeg
  iu _ := rfl
  pa _ := rfl

include hdeg in
/-- Hilbert 90 in the explicit involution-module form needed by the
connecting-map lemmas. -/
theorem hilbert90 (hne : σ ≠ 1) (z : F E) (hz : -fAction K E σ z = z) :
    ∃ x : F E, x-fAction K E σ x = z := by
  have hprod : σ (z.toMul : E)*(z.toMul : E) = 1 := by
    change ((fieldAction E σ.toRingEquiv z.toMul)⁻¹ : Eˣ) = z.toMul at hz
    have h' := congrArg Units.val hz
    rw [Units.val_inv_eq_inv_val] at h'
    change (σ (z.toMul : E))⁻¹ = (z.toMul : E) at h'
    calc
      σ (z.toMul : E)*(z.toMul : E) = σ (z.toMul : E)*(σ (z.toMul : E))⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ (by simpa only [map_zero] using σ.injective.ne (Units.ne_zero z.toMul))
  have hn : Algebra.norm K (z.toMul : E) = 1 := by
    apply (algebraMap K E).injective
    rw [QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne,hprod,map_one]
  have hg : ∀ τ : E ≃ₐ[K] E, τ ∈ Subgroup.zpowers σ := by
    intro τ
    rcases QuadraticUnitHerbrand.aut_eq_one_or K E σ hdeg hne τ with ht | ht
    · rw [ht]; exact Subgroup.one_mem _
    · rw [ht]; exact Subgroup.mem_zpowers σ
  letI : Algebra.IsQuadraticExtension K E := ⟨hdeg⟩
  obtain ⟨x,hx⟩ := groupCohomology.exists_div_of_norm_eq_one (K := K) (L := E) (g := σ) hg hn
  refine ⟨Additive.ofMul x,?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((x / fieldAction E σ.toRingEquiv x : Eˣ) : E) = (z.toMul : E)
  rw [Units.val_div_eq_div_val]
  exact hx

end PrincipalInvolutionSequences

namespace PrincipalInvolutionSequences
open NumberField InvolutionHerbrand InvolutionSequence
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

include hne in
theorem units_connecting_surjective :
    Function.Surjective (connecting (unitsSequence K E σ hdeg)) :=
  connecting_surjective _ (hilbert90 K E σ hdeg hne)

theorem finite_opposite_units : Finite (InvolutionSequence.H1 (unitsSequence K E σ hdeg).neg) := by
  dsimp [InvolutionSequence.H1,Sequence.neg]
  exact InvolutionHerbrand.finite_norm_quotient _ _

noncomputable def oppositeUnitsEquiv :
    InvolutionSequence.H1 (unitsSequence K E σ hdeg).neg ≃ₗ[ℤ] QuadraticUnitHerbrand.H0 K E σ hdeg := by
  dsimp [InvolutionSequence.H1,Sequence.neg]
  exact LinearEquiv.refl _ _

include hne in
theorem principalH1_card_le :
    Nat.card (InvolutionSequence.H1 (idealsSequence K E σ hdeg)) ≤
      Nat.card (QuadraticUnitHerbrand.H0 K E σ hdeg) := by
  letI := finite_opposite_units K E σ hdeg
  have h := card_quotientH1_le (unitsSequence K E σ hdeg) (hilbert90 K E σ hdeg hne)
  rw [Nat.card_congr (oppositeUnitsEquiv K E σ hdeg).toEquiv] at h
  exact h

include hne in
theorem principalH1_finite : Finite (InvolutionSequence.H1 (idealsSequence K E σ hdeg)) := by
  letI := finite_opposite_units K E σ hdeg
  exact Finite.of_injective (oppositeEmbedding (unitsSequence K E σ hdeg) (hilbert90 K E σ hdeg hne))
    (oppositeEmbedding_injective _ _)

/-- Ambiguous classes modulo classes represented by invariant fractional
ideals. -/
abbrev ambiguousDefect := plus (A := C E) (cAction K E σ) ⧸
  (pOnFixed (idealsSequence K E σ hdeg)).range

noncomputable def ambiguousDefectEquiv :
    ambiguousDefect K E σ hdeg ≃ₗ[ℤ] (connecting (idealsSequence K E σ hdeg)).range :=
  (Submodule.quotEquivOfEq _ _ (ker_connecting (idealsSequence K E σ hdeg)).symm).trans
    (connecting (idealsSequence K E σ hdeg)).quotKerEquivRange

include hne in
/-- The ambiguous-class defect is bounded by the unit norm index. -/
theorem ambiguousDefect_card_le :
    Nat.card (ambiguousDefect K E σ hdeg) ≤ Nat.card (QuadraticUnitHerbrand.H0 K E σ hdeg) := by
  letI := principalH1_finite K E σ hdeg hne
  rw [Nat.card_congr (ambiguousDefectEquiv K E σ hdeg).toEquiv]
  exact (Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective).trans
    (principalH1_card_le K E σ hdeg hne)

end PrincipalInvolutionSequences

namespace PrincipalInvolutionSequences
open NumberField InvolutionHerbrand InvolutionSequence
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

/-- Relations among invariant fractional ideals that come from invariant
field elements. In the unramified case this presents the base class group. -/
noncomputable def baseRelations : Submodule ℤ (plus (dAction K E σ)) :=
  (pOnFixed (unitsSequence K E σ hdeg)).range.map (iOnFixed (idealsSequence K E σ hdeg))

abbrev baseQuotient := plus (dAction K E σ) ⧸ baseRelations K E σ hdeg

set_option maxHeartbeats 2000000 in
include hne in
/-- The first connecting map counts the kernel in the fixed-ideal class
presentation. -/
theorem baseQuotient_card :
    Nat.card (baseQuotient K E σ hdeg) = Nat.card (QuadraticUnitHerbrand.H1 K E σ hdeg) *
      Nat.card (pOnFixed (idealsSequence K E σ hdeg)).range := by
  change Nat.card (_ ⧸ (pOnFixed (unitsSequence K E σ hdeg)).range.map
    (iOnFixed (idealsSequence K E σ hdeg))) = _
  rw [card_quotient_map _ (iOnFixed_injective _) _]
  have e₁ : (plus (pAction K E σ) ⧸ (pOnFixed (unitsSequence K E σ hdeg)).range) ≃ₗ[ℤ]
      QuadraticUnitHerbrand.H1 K E σ hdeg :=
    (Submodule.quotEquivOfEq _ _ (ker_connecting (unitsSequence K E σ hdeg)).symm).trans
      ((connecting (unitsSequence K E σ hdeg)).quotKerEquivOfSurjective
        (units_connecting_surjective K E σ hdeg hne))
  have e₂ : (plus (dAction K E σ) ⧸ (iOnFixed (idealsSequence K E σ hdeg)).range) ≃ₗ[ℤ]
      (pOnFixed (idealsSequence K E σ hdeg)).range :=
    (Submodule.quotEquivOfEq _ _ (ker_pOnFixed (idealsSequence K E σ hdeg)).symm).trans
      (pOnFixed (idealsSequence K E σ hdeg)).quotKerEquivRange
  exact congrArg₂ (·*·) (Nat.card_congr e₁.toEquiv) (Nat.card_congr e₂.toEquiv)

set_option maxHeartbeats 2000000 in
include hne in
/-- The fixed-class group has at most half the order of the fixed-ideal
presentation, for a totally real quadratic extension. -/
theorem twice_fixedClasses_le_base [IsTotallyReal K] [IsTotallyReal E] :
    2*Nat.card (plus (A := C E) (cAction K E σ)) ≤ Nat.card (baseQuotient K E σ hdeg) := by
  have hc := (pOnFixed (idealsSequence K E σ hdeg)).range.card_eq_card_quotient_mul_card
  change Nat.card (plus (A := C E) (cAction K E σ)) =
    Nat.card (pOnFixed (idealsSequence K E σ hdeg)).range * Nat.card (ambiguousDefect K E σ hdeg) at hc
  rw [hc,baseQuotient_card K E σ hdeg hne,QuadraticUnitHerbrand.herbrand K E σ hdeg hne]
  have h := ambiguousDefect_card_le K E σ hdeg hne
  calc
    _ ≤ 2*(Nat.card (pOnFixed (idealsSequence K E σ hdeg)).range *
      Nat.card (QuadraticUnitHerbrand.H0 K E σ hdeg)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h)
    _ = _ := by ring

end PrincipalInvolutionSequences

/-! Rigidity of unramified embeddings into a noetherian domain. -/
namespace UnramifiedRigidity
open NumberField

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S]
  [Algebra R A] [Algebra R S] [IsNoetherianRing S] [IsDomain S]

/-- Two embeddings of a formally unramified algebra cannot agree modulo a
proper ideal unless they agree everywhere. -/
theorem hom_ext [Algebra.FormallyUnramified R A] (I : Ideal S) (hI : I ≠ ⊤)
    {f g : A →ₐ[R] S} (h : ∀ x, f x - g x ∈ I) : f = g := by
  apply Algebra.FormallyUnramified.ext_of_iInf I (I.iInf_pow_eq_bot_of_isDomain hI)
  intro x
  exact Ideal.Quotient.eq.mpr (h x)

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- Trivial relative different gives the global formally-unramified property. -/
theorem formallyUnramified (h : differentIdeal (𝓞 K) (𝓞 L) = ⊤) :
    Algebra.FormallyUnramified (𝓞 K) (𝓞 L) := by
  apply Algebra.unramifiedLocus_eq_univ_iff.mp
  apply Set.eq_univ_of_forall
  intro P
  apply not_dvd_differentIdeal_iff.mp
  rw [h,Ideal.dvd_iff_le]
  intro hh
  exact P.isPrime.ne_top (top_unique hh)

variable {K L} {M : Type*} [Field M] [NumberField M] [Algebra K M]

/-- Distinct field embeddings of an everywhere-unramified number field
remain distinct modulo every proper ideal in the target integers. -/
theorem fieldHom_ext (hL : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (I : Ideal (𝓞 M)) (hI : I ≠ ⊤) {f g : L →ₐ[K] M}
    (h : ∀ x : 𝓞 L, RingOfIntegers.mapAlgHom f x - RingOfIntegers.mapAlgHom g x ∈ I) :
    f = g := by
  letI := formallyUnramified K L hL
  have he := hom_ext I hI h
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := 𝓞 L)
  intro x
  exact congrArg (fun x : 𝓞 M => (x : M)) (AlgHom.congr_fun he x)

/-- Inertia in any finite normal overfield fixes the image of every
unramified subextension. -/
theorem inertia_fixes (hL : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (I : Ideal (𝓞 M)) (hI : I ≠ ⊤) (σ : Gal(M/K))
    (hσ : σ ∈ I.toAddSubgroup.inertia Gal(M/K)) (f : L →ₐ[K] M) (x : L) :
    σ (f x) = f x := by
  have he : σ.toAlgHom.comp f = f := by
    apply fieldHom_ext hL I hI
    intro y
    exact hσ (RingOfIntegers.mapAlgHom f y)
  exact AlgHom.congr_fun he x

end UnramifiedRigidity

namespace UnramifiedIdealDescent
open NumberField
open scoped Classical

section Algebra
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (τ : S ≃ₐ[R] S)

/-- An ideal stable under an involution descends when the fixed ring is the
base and the differences of conjugates generate the unit ideal. -/
theorem map_comap_eq (hτ : ∀ x, τ (τ x) = x)
    (hfixed : ∀ x, τ x = x → ∃ r : R, algebraMap R S r = x)
    (hdiff : Ideal.span (Set.range (fun a : S => τ a-a)) = ⊤)
    (J : Ideal S) (hJ : ∀ x ∈ J, τ x ∈ J) :
    Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J := by
  let I := Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J)
  have htrace (x : S) (hx : x ∈ J) : τ x+x ∈ I := by
    obtain ⟨r,hr⟩ := hfixed (τ x+x) (by rw [map_add,hτ]; ac_rfl)
    rw [← hr]
    exact Ideal.mem_map_of_mem _ (by change algebraMap R S r ∈ J; rw [hr]; exact J.add_mem (hJ x hx) hx)
  have hmul : Ideal.span (Set.range (fun a : S => τ a-a))*J ≤ I := by
    rw [Ideal.mul_le]
    intro y hy x hx
    refine Submodule.span_induction (p := fun y _ => y*x ∈ I) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a,rfl⟩
      have h₁ := I.mul_mem_left (τ a) (htrace x hx)
      have h₂ := htrace (a*x) (J.mul_mem_left a hx)
      convert I.sub_mem h₁ h₂ using 1
      rw [map_mul]
      ring
    · simpa using I.zero_mem
    · intro a b ha hb h₁ h₂
      simpa only [add_mul] using I.add_mem h₁ h₂
    · intro a b hb h
      simpa only [smul_eq_mul,mul_assoc] using I.mul_mem_left a h
  rw [hdiff,Ideal.top_mul] at hmul
  exact le_antisymm Ideal.map_comap_le hmul

end Algebra

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

include hdeg hne in
theorem fixed_integer (x : 𝓞 E) (hx : RingOfIntegers.mapAlgEquiv σ x = x) :
    ∃ r : 𝓞 K, algebraMap (𝓞 K) (𝓞 E) r = x := by
  have hf : (x : E) ∈ Set.range (algebraMap K E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    rcases QuadraticUnitHerbrand.aut_eq_one_or K E σ hdeg hne τ with rfl | rfl
    · rfl
    · exact congrArg (fun x : 𝓞 E => (x : E)) hx
  obtain ⟨r,hr⟩ := hf
  have hi : IsIntegral ℤ r := (isIntegral_algebraMap_iff (R := ℤ)
    (algebraMap K E).injective).mp (hr ▸ x.property)
  exact ⟨⟨r,hi⟩,RingOfIntegers.coe_injective hr⟩

include hne in
/-- In an unramified quadratic extension the differences of integral
conjugates generate the unit ideal. -/
theorem difference_span_top (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Ideal.span (Set.range (fun a : 𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)) = ⊤ := by
  by_contra h
  apply hne
  apply AlgEquiv.coe_algHom_injective
  apply UnramifiedRigidity.fieldHom_ext hunram _ h
  intro a
  exact Ideal.subset_span (Set.mem_range_self a)

include hdeg hne in
/-- Every invariant integral ideal in an unramified quadratic extension
is extended from its contraction. -/
theorem invariant_ideal_descends (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (J : Ideal (𝓞 E)) (hJ : ∀ x ∈ J, RingOfIntegers.mapAlgEquiv σ x ∈ J) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 E)) (Ideal.comap (algebraMap (𝓞 K) (𝓞 E)) J) = J := by
  apply map_comap_eq (RingOfIntegers.mapAlgEquiv σ) _ (fixed_integer K E σ hdeg hne)
    (difference_span_top K E σ hne hunram) J hJ
  intro x
  apply RingOfIntegers.coe_injective
  have hp : σ^2 = 1 := by
    rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
    exact pow_card_eq_one'
  exact congrArg (fun τ : E ≃ₐ[K] E => τ (x : E)) (by simpa [pow_two] using hp)

end UnramifiedIdealDescent

namespace UnramifiedIdealDescent
open NumberField
open scoped Classical nonZeroDivisors

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

noncomputable def contractionModule (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 K) K :=
  (J.coeToSubmodule.restrictScalars (𝓞 K)).comap
    (IsScalarTower.toAlgHom (𝓞 K) K E).toLinearMap

@[simp] theorem mem_contractionModule (J : FractionalIdeal (𝓞 E)⁰ E) (x : K) :
    x ∈ contractionModule K E J ↔ algebraMap K E x ∈ J := Iff.rfl

include hdeg hne in
theorem contraction_fractional (J : FractionalIdeal (𝓞 E)⁰ E) :
    IsFractional (𝓞 K)⁰ (contractionModule K E J) := by
  obtain ⟨d,hd,hJ⟩ := J.isFractional
  let r : 𝓞 K := RingOfIntegers.norm K d
  have hd0 : (d : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr
    (mem_nonZeroDivisors_iff_ne_zero.mp hd)
  have hr0 : r ≠ 0 := by
    apply RingOfIntegers.coe_ne_zero_iff.mp
    change Algebra.norm K (d : E) ≠ 0
    exact Algebra.norm_ne_zero_iff.mpr hd0
  refine ⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr hr0,?_⟩
  intro x hx
  obtain ⟨b,hb⟩ := hJ (algebraMap K E x) hx
  have hr : algebraMap K E (r : K) = σ (d : E)*(d : E) :=
    QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne (d : E)
  have he : algebraMap K E ((r : K)*x) =
      ((RingOfIntegers.mapAlgEquiv σ d*b : 𝓞 E) : E) := by
    change algebraMap K E ((r : K)*x) = σ (d : E)*(b : E)
    change (b : E) = (d : E)*algebraMap K E x at hb
    rw [map_mul,hr,hb,mul_assoc]
  have hi : IsIntegral ℤ ((r : K)*x) :=
    (isIntegral_algebraMap_iff (R := ℤ) (algebraMap K E).injective).mp
      (he ▸ (RingOfIntegers.mapAlgEquiv σ d*b).property)
  exact ⟨⟨(r : K)*x,hi⟩,rfl⟩

noncomputable def contraction (J : FractionalIdeal (𝓞 E)⁰ E) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨contractionModule K E J,contraction_fractional K E σ hdeg hne J⟩

@[simp] theorem mem_contraction (J : FractionalIdeal (𝓞 E)⁰ E) (x : K) :
    x ∈ contraction K E σ hdeg hne J ↔ algebraMap K E x ∈ J := Iff.rfl

include hdeg hne in
/-- Fractional ideals fixed by the nontrivial automorphism of an
unramified quadratic extension are extended from the base field. -/
theorem invariant_fractional_ideal_descends
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (J : FractionalIdeal (𝓞 E)⁰ E) (hJ : ∀ x ∈ J, σ x ∈ J) :
    FractionalIdeal.extendedHomₐ E (𝓞 E) (contraction K E σ hdeg hne J) = J := by
  let I := contraction K E σ hdeg hne J
  let V : Submodule (𝓞 E) E := Submodule.span (𝓞 E) (algebraMap K E '' (I : Set K))
  have hVJ : V ≤ J.coeToSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact hx
  have hσ (x : E) : σ (σ x) = x := by
    have hp : σ^2 = 1 := by
      rw [← hdeg,← IsGalois.card_aut_eq_finrank K E]
      exact pow_card_eq_one'
    exact congrArg (fun τ : E ≃ₐ[K] E => τ x) (by simpa [pow_two] using hp)
  have htrace (x : E) (hx : x ∈ J) : σ x+x ∈ V := by
    have hf : σ x+x ∈ Set.range (algebraMap K E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases QuadraticUnitHerbrand.aut_eq_one_or K E σ hdeg hne τ with rfl | rfl
      · rfl
      · rw [map_add,hσ]; ac_rfl
    obtain ⟨r,hr⟩ := hf
    apply Submodule.subset_span
    refine ⟨r,?_,hr⟩
    change algebraMap K E r ∈ J
    rw [hr]
    exact J.coeToSubmodule.add_mem (hJ x hx) hx
  have hJV : J.coeToSubmodule ≤ V := by
    intro x hx
    have hmem : (1 : 𝓞 E) ∈ Ideal.span
        (Set.range (fun a : 𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)) := by
      rw [difference_span_top K E σ hne hunram]
      trivial
    have hh : ∀ a ∈ Ideal.span
        (Set.range (fun a : 𝓞 E => RingOfIntegers.mapAlgEquiv σ a-a)), a • x ∈ V := by
      intro a ha
      refine Submodule.span_induction (p := fun a _ => a • x ∈ V) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨b,rfl⟩
        have h₁ := V.smul_mem (RingOfIntegers.mapAlgEquiv σ b) (htrace x hx)
        have h₂ := htrace (b • x) (J.coeToSubmodule.smul_mem b hx)
        convert V.sub_mem h₁ h₂ using 1
        change ((σ (b : E))-(b : E))*x = σ (b : E)*(σ x+x)-(σ ((b : E)*x)+(b : E)*x)
        rw [map_mul]
        ring
      · simpa only [zero_smul] using V.zero_mem
      · intro a b ha hb h₁ h₂
        simpa only [add_smul] using V.add_mem h₁ h₂
      · intro a b hb h
        simpa only [smul_eq_mul,mul_smul] using V.smul_mem a h
    simpa only [one_smul] using hh 1 hmem
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHomₐ E (𝓞 E) I) : Submodule (𝓞 E) E) = J.coeToSubmodule
  rw [FractionalIdeal.coe_extendedHomₐ_eq_span]
  exact le_antisymm hVJ hJV

end UnramifiedIdealDescent

namespace UnramifiedAmbiguousClasses
open NumberField InvolutionHerbrand InvolutionSequence PrincipalInvolutionSequences FractionalGalois
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

noncomputable def fieldFixed : F K ≃ₗ[ℤ] plus (fAction K E σ) := by
  let f : F K →ₗ[ℤ] F E := (MonoidHom.toAdditive (fieldExtend K E)).toIntLinearMap
  let g : F K →ₗ[ℤ] plus (fAction K E σ) := f.codRestrict _ (fun x => by
    rw [mem_plus]
    apply Additive.toMul.injective
    apply Units.ext
    exact σ.commutes x.toMul)
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    apply Additive.toMul.injective
    exact Units.map_injective (algebraMap K E).injective (congrArg (fun z : plus (fAction K E σ) => z.1.toMul) h)
  · intro y
    have hy := (mem_plus (fAction K E σ) _).mp y.property
    have hr : (y.1.toMul : E) ∈ Set.range (algebraMap K E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro τ
      rcases QuadraticUnitHerbrand.aut_eq_one_or K E σ hdeg hne τ with ht | ht
      · rw [ht]; rfl
      · rw [ht]; exact congrArg (fun z : F E => (z.toMul : E)) hy
    obtain ⟨x,hx⟩ := hr
    have hx0 : x ≠ 0 := by
      intro h0
      apply Units.ne_zero y.1.toMul
      rw [← hx,h0,map_zero]
    refine ⟨Additive.ofMul (Units.mk0 x hx0),Subtype.ext ?_⟩
    apply Additive.toMul.injective
    exact Units.ext hx

@[simp] theorem fieldFixed_coe (x : F K) :
    (fieldFixed K E σ hdeg hne x).1 = Additive.ofMul (fieldExtend K E x.toMul) := rfl

variable (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)

noncomputable def idealFixed : D K ≃ₗ[ℤ] plus (dAction K E σ) := by
  let f : D K →ₗ[ℤ] D E := (MonoidHom.toAdditive (FractionalGalois.extend K E)).toIntLinearMap
  let g : D K →ₗ[ℤ] plus (dAction K E σ) := f.codRestrict _ (fun x =>
    (mem_plus _ _).mpr (FractionalGalois.extend_fixed K E σ x.toMul))
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y h
    exact FractionalGalois.extend_injective K E (congrArg (fun z : plus (dAction K E σ) => z.1.toMul) h)
  · intro J
    have hfix := (mem_plus (dAction K E σ) _).mp J.property
    have hfi : actionHom E σ.toRingEquiv J.1.toMul.1 = J.1.toMul.1 :=
      congrArg (fun z : D E => z.toMul.1) hfix
    have hs (x : E) (hx : x ∈ J.1.toMul.1) : σ x ∈ J.1.toMul.1 := by
      rw [← hfi,mem_actionHom]
      change σ.symm (σ x) ∈ _
      simpa only [AlgEquiv.symm_apply_apply] using hx
    let I := UnramifiedIdealDescent.contraction K E σ hdeg hne J.1.toMul.1
    have he : FractionalIdeal.extendedHomₐ E (𝓞 E) I = J.1.toMul.1 :=
      UnramifiedIdealDescent.invariant_fractional_ideal_descends K E σ hdeg hne hunram J.1.toMul.1 hs
    have hi : I ≠ 0 := by
      intro hi
      have hz := he.symm
      rw [hi,map_zero] at hz
      exact J.1.toMul.ne_zero hz
    refine ⟨Additive.ofMul (Units.mk0 I hi),Subtype.ext ?_⟩
    apply Additive.toMul.injective
    exact Units.ext he

@[simp] theorem idealFixed_coe (x : D K) :
    (idealFixed K E σ hdeg hne hunram x).1 = Additive.ofMul (FractionalGalois.extend K E x.toMul) := rfl

noncomputable def principalWhole (K : Type) [Field K] [NumberField K] : F K →ₗ[ℤ] D K :=
  (MonoidHom.toAdditive (toPrincipalIdeal (𝓞 K) K)).toIntLinearMap

/-- The fixed-field and fixed-ideal identifications commute with taking
principal ideals. -/
theorem principal_commutes (x : F K) :
    iOnFixed (idealsSequence K E σ hdeg)
      (pOnFixed (unitsSequence K E σ hdeg) (fieldFixed K E σ hdeg hne x)) =
        idealFixed K E σ hdeg hne hunram (principalWhole K x) := by
  apply Subtype.ext
  exact (extend_principal K E x.toMul).symm

set_option maxHeartbeats 2000000 in
theorem map_relations :
    (principalWhole K).range.map (idealFixed K E σ hdeg hne hunram).toLinearMap =
      baseRelations K E σ hdeg := by
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    refine ⟨pOnFixed (unitsSequence K E σ hdeg) (fieldFixed K E σ hdeg hne x),⟨_,rfl⟩,?_⟩
    exact principal_commutes K E σ hdeg hne hunram x
  · rintro ⟨z,⟨x,rfl⟩,hx⟩
    obtain ⟨a,rfl⟩ := (fieldFixed K E σ hdeg hne).surjective x
    refine ⟨principalWhole K a,⟨a,rfl⟩,?_⟩
    exact (principal_commutes K E σ hdeg hne hunram a).symm.trans hx

noncomputable def basePresentationEquiv :
    (D K ⧸ (principalWhole K).range) ≃ₗ[ℤ] baseQuotient K E σ hdeg :=
  Submodule.Quotient.equiv _ _ (idealFixed K E σ hdeg hne hunram)
    (map_relations K E σ hdeg hne hunram)

theorem ker_classMap : (classMap K).ker = (principalWhole K).range := by
  ext x
  change FractionalClasses.mk K x.toMul = 1 ↔ _
  rw [FractionalClasses.mk_eq_one]
  rfl

noncomputable def classPresentationEquiv : (D K ⧸ (principalWhole K).range) ≃ₗ[ℤ] C K :=
  (Submodule.quotEquivOfEq _ _ (ker_classMap K).symm).trans
    ((classMap K).quotKerEquivOfSurjective (by
      intro x
      obtain ⟨I,hI⟩ := FractionalClasses.mk_surjective K x.toMul
      exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩))

/-- The fixed-ideal presentation is the ordinary class group of the base
field when the quadratic extension is unramified. -/
noncomputable def baseEquiv : baseQuotient K E σ hdeg ≃ₗ[ℤ] C K :=
  (basePresentationEquiv K E σ hdeg hne hunram).symm.trans (classPresentationEquiv K)

include hdeg hne hunram in
/-- The elementary unramified quadratic ambiguous-class upper bound. -/
theorem twice_fixedClasses_le [IsTotallyReal K] [IsTotallyReal E] :
    2*Nat.card (plus (A := C E) (cAction K E σ)) ≤ Nat.card (ClassGroup (𝓞 K)) := by
  have h := twice_fixedClasses_le_base K E σ hdeg hne
  rw [Nat.card_congr (baseEquiv K E σ hdeg hne hunram).toEquiv] at h
  exact h.trans_eq (Nat.card_congr (Additive.toMul.trans (FractionalClasses.equiv K).toEquiv))

end UnramifiedAmbiguousClasses

/-! Norms and bounded fibers for the map of prime ideals in a number-field extension. -/
namespace IdealPrimeMap
open NumberField Ideal Module
open scoped Classical nonZeroDivisors

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

abbrev Primes (F : Type*) [Field F] [NumberField F] := {p : Ideal (𝓞 F) // Prime p}

noncomputable def below (P : Primes E) : Primes K := by
  letI : P.1.IsPrime := (Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
  exact ⟨P.1.under (𝓞 K), Ideal.prime_of_isPrime (Ideal.under_ne_bot (𝓞 K) P.property.ne_zero) inferInstance⟩

@[simp] theorem below_val (P : Primes E) : (below K E P).1 = P.1.under (𝓞 K) := rfl

noncomputable def degree (P : Primes E) : ℕ := (below K E P).1.inertiaDeg P.1

theorem degree_pos (P : Primes E) : 0 < degree K E P := by
  let p := below K E P
  letI : p.1.IsPrime := (Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI : p.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  haveI : P.1.LiesOver p.1 := inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
  exact Ideal.inertiaDeg_pos p.1 P.1

noncomputable def norm : (Ideal (𝓞 E))⁰ →* (Ideal (𝓞 K))⁰ where
  toFun I := ⟨Ideal.relNorm (𝓞 K) I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    change Ideal.relNorm (𝓞 K) I.1 ≠ ⊥
    exact Ideal.relNorm_eq_bot_iff.not.mpr (nonZeroDivisors.coe_ne_zero I))⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' I J := by apply Subtype.ext; exact map_mul _ _ _

@[simp] theorem norm_val (I : (Ideal (𝓞 E))⁰) : (norm K E I).1 = Ideal.relNorm (𝓞 K) I.1 := rfl

theorem relNorm_prime (P : Primes E) :
    Ideal.relNorm (𝓞 K) P.1 = (below K E P).1 ^ degree K E P := by
  let p := below K E P
  letI : p.1.IsPrime := (Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI : p.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  letI : P.1.IsPrime := (Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
  letI : P.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  haveI : P.1.LiesOver p.1 := inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
  exact Ideal.relNorm_eq_pow_of_isMaximal P.1 p.1

/-- The absolute norm of a prime is the norm downstairs raised to its residue degree. -/
theorem absNorm_prime (P : Primes E) :
    Ideal.absNorm P.1 = Ideal.absNorm (below K E P).1 ^ degree K E P := by
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 E) P.1, relNorm_prime, map_pow]

/-- Every finite fiber of prime ideals has size at most the extension degree. -/
theorem card_fiber_le (s : Finset (Primes E)) (p : Primes K) :
    (s.filter (fun P => below K E P = p)).card ≤ Module.finrank K E := by
  letI : NoZeroSMulDivisors (𝓞 K) (𝓞 E) := ⟨fun h => smul_eq_zero.mp h⟩
  let t := s.filter (fun P => below K E P = p)
  letI : p.1.IsPrime := (Ideal.prime_iff_isPrime p.property.ne_zero).mp p.property
  letI : p.1.IsMaximal := Ideal.IsPrime.isMaximal inferInstance p.property.ne_zero
  have hsubset : t.image Subtype.val ⊆ primesOverFinset p.1 (𝓞 E) := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    have he := congrArg Subtype.val (Finset.mem_filter.mp hP).2
    letI : P.1.IsPrime := (Ideal.prime_iff_isPrime P.property.ne_zero).mp P.property
    haveI : P.1.LiesOver p.1 := by
      rw [← he]
      exact inferInstanceAs (P.1.LiesOver (P.1.under (𝓞 K)))
    exact (mem_primesOverFinset_iff p.property.ne_zero (𝓞 E)).mpr ⟨inferInstance,inferInstance⟩
  calc
    _ = (t.image Subtype.val).card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (primesOverFinset p.1 (𝓞 E)).card := Finset.card_le_card hsubset
    _ ≤ _ := Ideal.card_primesOverFinset_le_finrank (𝓞 E) K E p.property.ne_zero

end IdealPrimeMap

namespace NormClassHom
open NumberField
open scoped Classical nonZeroDivisors

noncomputable def descend {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
    (q : A →* B) (hq : Function.Surjective q) (f : A →* C)
    (hf : ∀ a b, q a = q b → f a = f b) : B →* C where
  toFun b := f (Classical.choose (hq b))
  map_one' := (hf _ 1 (by rw [Classical.choose_spec (hq 1),map_one])).trans f.map_one
  map_mul' b c := by
    rw [← map_mul]
    apply hf
    rw [Classical.choose_spec (hq (b*c)),map_mul,Classical.choose_spec (hq b),Classical.choose_spec (hq c)]

@[simp] theorem descend_apply {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
    (q : A →* B) (hq : Function.Surjective q) (f : A →* C)
    (hf : ∀ a b, q a = q b → f a = f b) (a : A) :
    descend q hq f hf (q a) = f a :=
  hf _ _ (Classical.choose_spec (hq (q a)))

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

theorem norm_respects_classes (I J : (Ideal (𝓞 E))⁰) (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (IdealPrimeMap.norm K E I) = ClassGroup.mk0 (IdealPrimeMap.norm K E J) := by
  obtain ⟨a,b,ha,hb,hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
  apply ClassGroup.mk0_eq_mk0_iff.mpr
  letI := FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 E))
  refine ⟨Algebra.intNorm (𝓞 K) (𝓞 E) a,Algebra.intNorm (𝓞 K) (𝓞 E) b,
    Algebra.intNorm_ne_zero.mpr ha,Algebra.intNorm_ne_zero.mpr hb,?_⟩
  have h := congrArg (Ideal.relNorm (𝓞 K)) hab
  simpa only [map_mul,Ideal.relNorm_singleton] using h

/-- Relative ideal norm on the ordinary ideal class group. -/
noncomputable def norm : ClassGroup (𝓞 E) →* ClassGroup (𝓞 K) :=
  descend ClassGroup.mk0 ClassGroup.mk0_surjective (ClassGroup.mk0.comp (IdealPrimeMap.norm K E))
    (norm_respects_classes K E)

@[simp] theorem norm_mk0 (I : (Ideal (𝓞 E))⁰) :
    norm K E (ClassGroup.mk0 I) = ClassGroup.mk0 (IdealPrimeMap.norm K E I) :=
  descend_apply _ _ _ _ I

end NormClassHom

namespace FractionalClasses
open NumberField FractionalGalois
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def mkIdeal : (Ideal (𝓞 K))⁰ →* Classes K := (mk K).comp (FractionalIdeal.mk0 K)

@[simp] theorem equiv_mkIdeal (I : (Ideal (𝓞 K))⁰) : equiv K (mkIdeal K I) = ClassGroup.mk0 I := by
  change (ClassGroup.equiv K).symm (mk K (FractionalIdeal.mk0 K I)) = _
  change (ClassGroup.equiv K).symm (QuotientGroup.mk' _ (FractionalIdeal.mk0 K I)) = _
  rw [← ClassGroup.equiv_mk0, MulEquiv.symm_apply_apply]

theorem mkIdeal_surjective : Function.Surjective (mkIdeal K) := by
  intro c
  obtain ⟨I,hI⟩ := ClassGroup.mk0_surjective (equiv K c)
  exact ⟨I,(equiv K).injective ((equiv_mkIdeal K I).trans hI)⟩

variable (E : Type*) [Field E] [NumberField E] [Algebra K E]

noncomputable def norm : Classes E →* Classes K :=
  ((equiv K).symm.toMonoidHom.comp (NormClassHom.norm K E)).comp (equiv E).toMonoidHom

@[simp] theorem norm_mkIdeal (I : (Ideal (𝓞 E))⁰) :
    norm K E (mkIdeal E I) = mkIdeal K (IdealPrimeMap.norm K E I) := by
  apply (equiv K).injective
  change equiv K ((equiv K).symm (NormClassHom.norm K E (equiv E (mkIdeal E I)))) = _
  rw [MulEquiv.apply_symm_apply,equiv_mkIdeal,NormClassHom.norm_mk0,equiv_mkIdeal]

variable (σ : E ≃ₐ[K] E)

noncomputable def mapIdeal (I : (Ideal (𝓞 E))⁰) : (Ideal (𝓞 E))⁰ :=
  ⟨Ideal.map (RingOfIntegers.mapAlgEquiv σ) I.1,mem_nonZeroDivisors_iff_ne_zero.mpr
    ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapAlgEquiv σ).injective).not.mpr
      (nonZeroDivisors.coe_ne_zero I))⟩

theorem action_mkIdeal (I : (Ideal (𝓞 E))⁰) :
    action K E σ (mkIdeal E I) = mkIdeal E (mapIdeal K E σ I) := by
  change mk E (FractionalGalois.action E σ.toRingEquiv (FractionalIdeal.mk0 E I)) =
    mk E (FractionalIdeal.mk0 E (mapIdeal K E σ I))
  apply congrArg (mk E)
  apply Units.ext
  change FractionalGalois.actionHom E σ.toRingEquiv (FractionalIdeal.mk0 E I).1 =
    (FractionalIdeal.mk0 E (mapIdeal K E σ I)).1
  rw [FractionalIdeal.coe_mk0,FractionalIdeal.coe_mk0]
  exact FractionalIdeal.extended_coeIdeal_eq_map E _ I.1

/-- Relative ideal-class norm is invariant under all base automorphisms. -/
theorem norm_action (c : Classes E) : norm K E (action K E σ c) = norm K E c := by
  obtain ⟨I,rfl⟩ := mkIdeal_surjective E c
  rw [action_mkIdeal,norm_mkIdeal,norm_mkIdeal]
  congr 1
  apply Subtype.ext
  exact Ideal.relNorm_map_algEquiv (RingOfIntegers.mapAlgEquiv σ) I.1

end FractionalClasses

namespace FiniteEndomorphism
open scoped Classical
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- For an endomorphism of a finite abelian group, kernel and cokernel
have equal cardinality. -/
theorem card_coker_eq_ker [Finite A] (f : A →ₗ[ℤ] A) :
    Nat.card (A ⧸ f.range) = Nat.card f.ker := by
  have h₁ := f.range.card_eq_card_quotient_mul_card
  have h₂ := f.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv,mul_comm] at h₂
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h₁.symm.trans h₂)

/-- An invariant homomorphism from a finite group has image bounded by
the fixed subgroup of the acting endomorphism. -/
theorem range_card_le_fixed [Finite A] [Finite B] (σ : A →ₗ[ℤ] A) (f : A →ₗ[ℤ] B)
    (hf : ∀ x, f (σ x) = f x) : Nat.card f.range ≤ Nat.card (InvolutionHerbrand.plus σ) := by
  have hle : (σ-LinearMap.id).range ≤ f.ker := by
    rintro _ ⟨x,rfl⟩
    change f (σ x-x) = 0
    rw [map_sub,hf,sub_self]
  let q := (σ-LinearMap.id).range.liftQ f hle
  have he : q.range = f.range := Submodule.range_liftQ _ _ _
  rw [← he]
  letI : Finite (A ⧸ (σ-LinearMap.id).range) :=
    Finite.of_surjective _ (σ-LinearMap.id).range.mkQ_surjective
  calc
    Nat.card q.range ≤ Nat.card (A ⧸ (σ-LinearMap.id).range) :=
      Nat.card_le_card_of_surjective q.rangeRestrict (by rintro ⟨y,x,rfl⟩; exact ⟨x,rfl⟩)
    _ = Nat.card (InvolutionHerbrand.plus σ) := card_coker_eq_ker _

end FiniteEndomorphism

namespace ClassNormInvariance
open NumberField PrincipalInvolutionSequences InvolutionHerbrand
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E)

noncomputable def normLinear : C E →ₗ[ℤ] C K :=
  AddMonoidHom.toIntLinearMap (M := C E) (M₂ := C K) (MonoidHom.toAdditive (FractionalClasses.norm K E))

theorem normLinear_action (c : C E) : normLinear K E (cAction K E σ c) = normLinear K E c :=
  FractionalClasses.norm_action K E σ c.toMul

set_option maxHeartbeats 2000000 in
/-- The norm-class image has order at most the number of ambiguous classes. -/
theorem range_card_le_fixed :
    Nat.card (normLinear K E).range ≤ Nat.card (plus (A := C E) (cAction K E σ)) := by
  letI : Finite (C E) := Finite.of_equiv (FractionalClasses.Classes E) Additive.ofMul
  letI : Finite (C K) := Finite.of_equiv (FractionalClasses.Classes K) Additive.ofMul
  exact @FiniteEndomorphism.range_card_le_fixed (C E) (C K) inferInstance inferInstance
    inferInstance inferInstance (cAction K E σ) (normLinear K E) (normLinear_action K E σ)

end ClassNormInvariance


/-! Integer-grid counting with an explicit boundary-cover error. -/
namespace GridBoundaryCount
open MeasureTheory Set Metric
open scoped ENNReal Classical BigOperators

variable {ι : Type*} [Fintype ι]

def cast (z : ι → ℤ) : ι → ℝ := fun i => z i

def cell (z : ι → ℤ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Ico (z i : ℝ) (z i+1)

noncomputable def floor (x : ι → ℝ) : ι → ℤ := fun i => ⌊x i⌋

@[simp] theorem mem_cell_iff (z : ι → ℤ) (x : ι → ℝ) :
    x ∈ cell z ↔ floor x = z := by
  simp only [cell,Set.mem_pi,Set.mem_univ,forall_const,Set.mem_Ico,floor,funext_iff]
  exact forall_congr' fun i => Int.floor_eq_iff.symm

theorem mem_cell_floor (x : ι → ℝ) : x ∈ cell (floor x) := by simp

theorem cell_disjoint : Pairwise (fun z w : ι → ℤ => Disjoint (cell z) (cell w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hzw ((mem_cell_iff z x).mp hx |>.symm.trans ((mem_cell_iff w x).mp hy))

theorem measurableSet_cell (z : ι → ℤ) : MeasurableSet (cell z) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

@[simp] theorem volume_cell (z : ι → ℤ) : volume (cell z) = 1 := by
  simp [cell,volume_pi_pi,Real.volume_Ico]

theorem dist_cast_lt_one {z : ι → ℤ} {x : ι → ℝ} (hx : x ∈ cell z) :
    dist x (cast z) < 1 := by
  apply (dist_pi_lt_iff zero_lt_one).mpr
  intro i
  have hi := Set.mem_pi.mp hx i (Set.mem_univ i)
  rw [Real.dist_eq]
  apply abs_lt.mpr
  dsimp [cast]
  constructor <;> linarith [hi.1,hi.2]

def tiles (s : Finset (ι → ℤ)) : Set (ι → ℝ) := ⋃ z ∈ s, cell z

theorem measurableSet_tiles (s : Finset (ι → ℤ)) : MeasurableSet (tiles s) := by
  exact s.measurableSet_biUnion (fun z _ => measurableSet_cell z)

@[simp] theorem volume_tiles (s : Finset (ι → ℤ)) : volume (tiles s) = s.card := by
  rw [tiles,measure_biUnion_finset]
  · simp
  · exact cell_disjoint.set_pairwise _
  · intro z _
    exact measurableSet_cell z

/-- If two points lie on opposite sides of a set, one of its frontier
points is at most their distance from the first point. -/
theorem exists_frontier_dist_le {S : Set (ι → ℝ)} {x y : ι → ℝ}
    (hx : x ∈ S) (hy : y ∉ S) : ∃ z ∈ frontier S, dist x z ≤ dist x y := by
  obtain ⟨z,hz,he⟩ := exists_mem_frontier_infDist_compl_eq_dist hx
    (show S ≠ Set.univ from fun h => hy (h ▸ Set.mem_univ y))
  exact ⟨z,hz,he ▸ infDist_le_dist_of_mem (show y ∈ Sᶜ from hy)⟩

def cover (t : Finset (ι → ℝ)) (r : ℝ) : Set (ι → ℝ) := ⋃ y ∈ t, closedBall y r

/-- A finite radius-two cover has an elementary volume bound in the sup norm. -/
theorem volume_cover (t : Finset (ι → ℝ)) :
    volume (cover t 2) ≤ (t.card : ℝ≥0∞)*4^Fintype.card ι := by
  calc
    volume (cover t 2) ≤ ∑ y ∈ t, volume (closedBall y 2) := measure_biUnion_finset_le _ _
    _ = _ := by norm_num [Real.volume_pi_closedBall _ (by norm_num : (0 : ℝ) ≤ 2)]

/-- The tiled approximation to a set differs from it only within one unit
of the frontier; a radius-one frontier cover therefore gives a radius-two
cover for both errors. -/
theorem tiles_subset_union_cover (S : Set (ι → ℝ)) (s : Finset (ι → ℤ))
    (hs : ∀ z, z ∈ s ↔ cast z ∈ S) (t : Finset (ι → ℝ))
    (ht : ∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    tiles s ⊆ S ∪ cover t 2 := by
  intro x hx
  by_cases hxS : x ∈ S
  · exact Or.inl hxS
  · right
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
    have hzS := (hs z).mp hz
    obtain ⟨w,hw,hd⟩ := exists_frontier_dist_le (S := Sᶜ) hxS (by simpa using hzS)
    rw [frontier_compl] at hw
    obtain ⟨y,hy,hwy⟩ := ht w hw
    refine Set.mem_iUnion₂.mpr ⟨y,hy,?_⟩
    apply mem_closedBall.mpr
    have hdx := dist_cast_lt_one hxz
    have htri := dist_triangle x w y
    linarith

theorem subset_tiles_union_cover (S : Set (ι → ℝ)) (s : Finset (ι → ℤ))
    (hs : ∀ z, z ∈ s ↔ cast z ∈ S) (t : Finset (ι → ℝ))
    (ht : ∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    S ⊆ tiles s ∪ cover t 2 := by
  intro x hx
  by_cases hz : floor x ∈ s
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨floor x,hz,mem_cell_floor x⟩)
  · right
    have hzS : cast (floor x) ∉ S := fun h => hz ((hs _).mpr h)
    obtain ⟨w,hw,hd⟩ := exists_frontier_dist_le hx hzS
    obtain ⟨y,hy,hwy⟩ := ht w hw
    refine Set.mem_iUnion₂.mpr ⟨y,hy,?_⟩
    apply mem_closedBall.mpr
    have hdx := dist_cast_lt_one (mem_cell_floor x)
    have htri := dist_triangle x w y
    linarith

/-- Quantitative grid counting: each radius-one frontier-cover ball contributes
at most the volume of a radius-two cube to the counting error. -/
theorem count_error (S : Set (ι → ℝ)) (hS : volume S ≠ ⊤)
    (s : Finset (ι → ℤ)) (hs : ∀ z, z ∈ s ↔ cast z ∈ S)
    (t : Finset (ι → ℝ)) (ht : ∀ x ∈ frontier S, ∃ y ∈ t, dist x y ≤ 1) :
    |(s.card : ℝ)-volume.real S| ≤ (t.card : ℝ)*4^Fintype.card ι := by
  have hc : volume (cover t 2) ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) (volume_cover t)
  have htiles : volume (tiles s) ≠ ⊤ := by simp
  have h₁ := (measureReal_mono (μ := volume) (tiles_subset_union_cover S s hs t ht)
    (measure_union_lt_top hS.lt_top hc.lt_top).ne).trans (measureReal_union_le S (cover t 2))
  have h₂ := (measureReal_mono (μ := volume) (subset_tiles_union_cover S s hs t ht)
    (measure_union_lt_top htiles.lt_top hc.lt_top).ne).trans (measureReal_union_le (tiles s) (cover t 2))
  have he : volume.real (tiles s) = s.card := by simp [measureReal_def]
  have hb : volume.real (cover t 2) ≤ (t.card : ℝ)*4^Fintype.card ι := by
    have hh := ENNReal.toReal_mono (by finiteness) (volume_cover t)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
      ENNReal.toReal_ofNat] using hh
  rw [he] at h₁ h₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end GridBoundaryCount



/- Finite meshes for dilates of Lipschitz images of unit cubes. -/
namespace LipschitzMesh
open Set Metric
open scoped Classical NNReal

variable {ι : Type*} [Fintype ι]

def cube (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

noncomputable def point (n : ℕ) (v : ι → Fin (n+1)) : ι → ℝ := fun i => (v i : ℝ)/(n : ℝ)

theorem point_mem {n : ℕ} (hn : 0 < n) (v : ι → Fin (n+1)) : point n v ∈ cube ι := by
  intro i _
  constructor
  · dsimp [point]; positivity
  · dsimp [point]
    apply (div_le_one (by exact_mod_cast hn)).mpr
    exact_mod_cast Nat.le_of_lt_succ (v i).isLt

/-- A cube is covered by its mesh with coordinate spacing 1/n. -/
theorem exists_point {n : ℕ} (hn : 0 < n) (x : ι → ℝ) (hx : x ∈ cube ι) :
    ∃ v : ι → Fin (n+1), dist x (point n v) ≤ (n : ℝ)⁻¹ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hxn (i : ι) : (n : ℝ)*x i ≤ n := by
    have hi := hx i (Set.mem_univ i)
    nlinarith [hi.2]
  let v : ι → Fin (n+1) := fun i => ⟨⌊(n : ℝ)*x i⌋₊,Nat.lt_succ_of_le (Nat.floor_le_of_le (hxn i))⟩
  refine ⟨v,(dist_pi_le_iff (inv_nonneg.mpr hnr.le)).mpr fun i => ?_⟩
  rw [Real.dist_eq]
  change |x i-(⌊(n : ℝ)*x i⌋₊ : ℝ)/(n : ℝ)| ≤ (n : ℝ)⁻¹
  have hi := hx i (Set.mem_univ i)
  have hfloor := Nat.floor_le (show 0 ≤ (n : ℝ)*x i from mul_nonneg hnr.le hi.1)
  have hlt := Nat.lt_floor_add_one ((n : ℝ)*x i)
  have hnonneg : 0 ≤ x i-(⌊(n : ℝ)*x i⌋₊ : ℝ)/(n : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hnr).mpr
    nlinarith
  rw [abs_of_nonneg hnonneg,← one_div,sub_le_iff_le_add,← add_div]
  apply (le_div_iff₀ hnr).mpr
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A dilated Lipschitz chart admits a radius-one cover of polynomial size
in the dilation parameter, with exponent equal to the chart dimension. -/
theorem exists_cover (f : (ι → ℝ) → E) (K : ℝ≥0) (hf : LipschitzOnWith K f (cube ι))
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ s : Finset E, s.card ≤ (⌈t*(K : ℝ)⌉₊+2)^Fintype.card ι ∧
      ∀ x ∈ cube ι, ∃ y ∈ s, dist (t • f x) y ≤ 1 := by
  let n := ⌈t*(K : ℝ)⌉₊+1
  have hn : 0 < n := Nat.succ_pos _
  let s := Finset.univ.image (fun v : ι → Fin (n+1) => t • f (point n v))
  refine ⟨s,?_,?_⟩
  · have hc := Finset.card_image_le (s := (Finset.univ : Finset (ι → Fin (n+1))))
      (f := fun v => t • f (point n v))
    simpa [s,n,Fintype.card_fun] using hc
  · intro x hx
    obtain ⟨v,hv⟩ := exists_point hn x hx
    refine ⟨t • f (point n v),Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,?_⟩
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_nonneg ht]
    have hdist := hf.dist_le_mul x hx (point n v) (point_mem hn v)
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    have hnK : t*(K : ℝ) ≤ n := by
      have hh := Nat.le_ceil (t*(K : ℝ))
      dsimp [n]
      push_cast
      linarith
    calc
      t*dist (f x) (f (point n v)) ≤ t*((K : ℝ)*dist x (point n v)) := mul_le_mul_of_nonneg_left hdist ht
      _ ≤ t*((K : ℝ)*(n : ℝ)⁻¹) := by gcongr
      _ = (t*(K : ℝ))/(n : ℝ) := by rw [div_eq_mul_inv]; ring
      _ ≤ 1 := (div_le_one hnr).mpr hnK

/-- A convenient real-valued version with a fixed chart-dependent constant. -/
theorem exists_cover_real (f : (ι → ℝ) → E) (K : ℝ≥0) (hf : LipschitzOnWith K f (cube ι))
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ s : Finset E, (s.card : ℝ) ≤ ((K : ℝ)+3)^Fintype.card ι*(t+1)^Fintype.card ι ∧
      ∀ x ∈ cube ι, ∃ y ∈ s, dist (t • f x) y ≤ 1 := by
  obtain ⟨s,hs,hcover⟩ := exists_cover f K hf t ht
  refine ⟨s,?_,hcover⟩
  have hc : (⌈t*(K : ℝ)⌉₊ : ℝ) < t*(K : ℝ)+1 := Nat.ceil_lt_add_one (mul_nonneg ht K.2)
  have hbound : (⌈t*(K : ℝ)⌉₊+2 : ℝ) ≤ ((K : ℝ)+3)*(t+1) := by
    calc
      _ ≤ t*(K : ℝ)+3 := by linarith
      _ ≤ t*(K : ℝ)+3+((K : ℝ)+3*t) := le_add_of_nonneg_right (by positivity)
      _ = _ := by ring
  have hs' : (s.card : ℝ) ≤ (⌈t*(K : ℝ)⌉₊+2 : ℝ)^Fintype.card ι := by exact_mod_cast hs
  calc
    _ ≤ (⌈t*(K : ℝ)⌉₊+2 : ℝ)^Fintype.card ι := hs'
    _ ≤ (((K : ℝ)+3)*(t+1))^Fintype.card ι := pow_le_pow_left₀ (by positivity) hbound _
    _ = _ := mul_pow _ _ _

end LipschitzMesh

namespace LipschitzBoundaryCount
open MeasureTheory Set Metric
open scoped Classical Pointwise NNReal BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (S : Set (ι → ℝ)) (r : ℕ)
  (f : κ → (Fin r → ℝ) → (ι → ℝ)) (K : κ → ℝ≥0)
  (hf : ∀ j, LipschitzOnWith (K j) (f j) (LipschitzMesh.cube (Fin r)))
  (hfront : ∀ x ∈ frontier S, ∃ j y, y ∈ LipschitzMesh.cube (Fin r) ∧ f j y = x)

include hf hfront

/-- A boundary covered by finitely many r-dimensional Lipschitz charts has
radius-one covers of its dilates growing polynomially with exponent r. -/
theorem exists_cover_dilate (t : ℝ) (ht : 0 < t) :
    ∃ T : Finset (ι → ℝ), (T.card : ℝ) ≤
      (∑ j, ((K j : ℝ)+3)^r)*(t+1)^r ∧
      ∀ x ∈ frontier (t • S), ∃ y ∈ T, dist x y ≤ 1 := by
  have hex : ∀ j, ∃ T : Finset (ι → ℝ), (T.card : ℝ) ≤
      ((K j : ℝ)+3)^r*(t+1)^r ∧
      ∀ x ∈ LipschitzMesh.cube (Fin r), ∃ y ∈ T, dist (t • f j x) y ≤ 1 := by
    intro j
    simpa using LipschitzMesh.exists_cover_real (f j) (K j) (hf j) t ht.le
  choose T hT hcov using hex
  refine ⟨Finset.univ.biUnion T,?_,?_⟩
  · have hc : ((Finset.univ.biUnion T).card : ℝ) ≤ ∑ j, ((T j).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := T))
    refine hc.trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hT j
  · intro x hx
    have he : frontier (t • S) = t • frontier S := by
      have hh := (Homeomorph.smul (α := ι → ℝ) (Units.mk0 t ht.ne')).image_frontier S
      change (fun x : ι → ℝ => t • x) '' frontier S =
        frontier ((fun x : ι → ℝ => t • x) '' S) at hh
      simpa only [Set.image_smul] using hh.symm
    rw [he] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    obtain ⟨j,y,hy,hyz⟩ := hfront z hz
    obtain ⟨w,hw,hd⟩ := hcov j y hy
    refine ⟨w,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hw⟩,?_⟩
    simpa only [hyz] using hd

/-- Effective counting for finite integer-grid sections of a dilated set
with a finite Lipschitz boundary parametrization. -/
theorem count_error_dilate (hS : volume S ≠ ⊤) (t : ℝ) (ht : 0 < t)
    (s : Finset (ι → ℤ)) (hs : ∀ z, z ∈ s ↔ GridBoundaryCount.cast z ∈ t • S) :
    |(s.card : ℝ)-t^Fintype.card ι*volume.real S| ≤
      4^Fintype.card ι*(∑ j, ((K j : ℝ)+3)^r)*(t+1)^r := by
  obtain ⟨T,hT,hcov⟩ := exists_cover_dilate S r f K hf hfront t ht
  have hvol : volume (t • S) ≠ ⊤ := by
    rw [volume.addHaar_smul_of_nonneg ht.le]
    exact ENNReal.mul_ne_top (by finiteness) hS
  have he : volume.real (t • S) = t^Fintype.card ι*volume.real S := by
    rw [measureReal_def,volume.addHaar_smul_of_nonneg ht.le,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ht.le _),Module.finrank_pi]
    rfl
  have hcount := GridBoundaryCount.count_error (t • S) hvol s hs T hcov
  rw [he] at hcount
  calc
    _ ≤ (T.card : ℝ)*4^Fintype.card ι := hcount
    _ ≤ ((∑ j, ((K j : ℝ)+3)^r)*(t+1)^r)*4^Fintype.card ι := by gcongr
    _ = _ := by ring

/-- For t>=1 the bound has the usual C*t^r form. -/
theorem exists_error_constant (hS : volume S ≠ ⊤) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t → ∀ s : Finset (ι → ℤ),
      (∀ z, z ∈ s ↔ GridBoundaryCount.cast z ∈ t • S) →
      |(s.card : ℝ)-t^Fintype.card ι*volume.real S| ≤ C*t^r := by
  let C := 4^Fintype.card ι*(∑ j, ((K j : ℝ)+3)^r)*2^r+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht s hs
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hh := count_error_dilate S r f K hf hfront hS t ht0 s hs
  have hp : (t+1)^r ≤ 2^r*t^r := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    _ ≤ 4^Fintype.card ι*(∑ j, ((K j : ℝ)+3)^r)*(t+1)^r := hh
    _ ≤ 4^Fintype.card ι*(∑ j, ((K j : ℝ)+3)^r)*(2^r*t^r) := by gcongr
    _ ≤ C*t^r := by dsimp [C]; nlinarith [pow_nonneg ht0.le r]

end LipschitzBoundaryCount



/- Bounded subsets contain only finitely many integer-grid points. -/
namespace GridFinite
open Set
open scoped Classical

variable {ι : Type*} [Fintype ι]

theorem finite_points (S : Set (ι → ℝ)) (hS : Bornology.IsBounded S) :
    {z : ι → ℤ | (fun i => (z i : ℝ)) ∈ S}.Finite := by
  obtain ⟨C,hC⟩ := hS.exists_norm_le
  let m : ℤ := ⌈|C|⌉
  have hfin : (Set.univ.pi fun _ : ι => Set.Icc (-m) m).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  apply hfin.subset
  intro z hz i _
  have hi : |(z i : ℝ)| ≤ C := by
    have hh := norm_le_pi_norm (fun i => (z i : ℝ)) i
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (hC _ hz)
  have hm : C ≤ (m : ℝ) := (le_abs_self C).trans (Int.le_ceil _)
  have hle : |(z i : ℝ)| ≤ (m : ℝ) := hi.trans hm
  have hh := abs_le.mp hle
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

/-- A finite list representing exactly the integer points in a bounded set. -/
theorem exists_finset (S : Set (ι → ℝ)) (hS : Bornology.IsBounded S) :
    ∃ s : Finset (ι → ℤ), ∀ z, z ∈ s ↔ (fun i => (z i : ℝ)) ∈ S := by
  exact ⟨(finite_points S hS).toFinset,fun z => Set.Finite.mem_toFinset _⟩

end GridFinite

namespace LatticeBoundaryCount
open MeasureTheory Set Metric
open scoped Classical Pointwise NNReal BigOperators

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Effective lattice counting in arbitrary linear coordinates follows
from a finite Lipschitz boundary parametrization. -/
theorem exists_error_constant (S : Set E) (hS : Bornology.IsBounded S)
    (r : ℕ) (g : κ → (Fin r → ℝ) → E) (K : κ → ℝ≥0)
    (hg : ∀ j, LipschitzOnWith (K j) (g j) (LipschitzMesh.cube (Fin r)))
    (hfront : ∀ x ∈ frontier S, ∃ j y, y ∈ LipschitzMesh.cube (Fin r) ∧ g j y = x)
    (b : (ι → ℝ) ≃L[ℝ] E) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {z : ι → ℤ | b (fun i => (z i : ℝ)) ∈ t • S} : ℝ)-
        t^Fintype.card ι*volume.real (b ⁻¹' S)| ≤ C*t^r := by
  let T : Set (ι → ℝ) := b ⁻¹' S
  let f : κ → (Fin r → ℝ) → (ι → ℝ) := fun j y => b.symm (g j y)
  let K' : κ → ℝ≥0 := fun j => ‖b.symm.toContinuousLinearMap‖₊ * K j
  have hf : ∀ j, LipschitzOnWith (K' j) (f j) (LipschitzMesh.cube (Fin r)) := by
    intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hb := b.symm.toContinuousLinearMap.lipschitz.dist_le_mul (g j x) (g j y)
    have hh := (hg j).dist_le_mul x hx y hy
    calc
      dist (f j x) (f j y) ≤ ‖b.symm.toContinuousLinearMap‖*dist (g j x) (g j y) := hb
      _ ≤ ‖b.symm.toContinuousLinearMap‖*((K j : ℝ)*dist x y) := by gcongr
      _ = (K' j : ℝ)*dist x y := by simp only [K',NNReal.coe_mul,coe_nnnorm]; ring
  have hfr : ∀ x ∈ frontier T, ∃ j y, y ∈ LipschitzMesh.cube (Fin r) ∧ f j y = x := by
    intro x hx
    have hx' : b x ∈ frontier S := by
      change x ∈ b ⁻¹' frontier S
      change x ∈ b.toHomeomorph ⁻¹' frontier S
      rw [b.toHomeomorph.preimage_frontier]
      exact hx
    obtain ⟨j,y,hy,he⟩ := hfront (b x) hx'
    exact ⟨j,y,hy,by dsimp [f]; rw [he,b.symm_apply_apply]⟩
  have hT : Bornology.IsBounded T := b.antilipschitz.isBounded_preimage hS
  obtain ⟨C,hC,hcount⟩ := LipschitzBoundaryCount.exists_error_constant T r f K' hf hfr hT.measure_lt_top.ne
  refine ⟨C,hC,?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hset : b ⁻¹' (t • S) = t • T := by
    ext x
    constructor
    · rintro ⟨y,hy,he⟩
      refine ⟨b.symm y,by simpa [T] using hy,?_⟩
      have hh := congrArg b.symm he
      simpa only [map_smul,b.symm_apply_apply] using hh
    · rintro ⟨y,hy,rfl⟩
      exact ⟨b y,hy,(map_smul b t y).symm⟩
  have htT : Bornology.IsBounded (t • T) := by
    rw [← Set.image_smul]
    exact (lipschitzWith_smul t).isBounded_image hT
  obtain ⟨s,hs⟩ := GridFinite.exists_finset (t • T) htT
  have hcard : Nat.card {z : ι → ℤ | b (fun i => (z i : ℝ)) ∈ t • S} = s.card := by
    calc
      _ = Nat.card {z : ι → ℤ | z ∈ s} := Nat.card_congr (Equiv.setCongr (by
        ext z
        simp only [Set.mem_setOf_eq]
        rw [hs z]
        change (fun i => (z i : ℝ)) ∈ b ⁻¹' (t • S) ↔ _
        rw [hset]))
      _ = s.card := Nat.card_eq_finsetCard s
  rw [hcard]
  exact hcount t ht s hs

end LatticeBoundaryCount



/- Finite Lipschitz charts for boundaries parameterized by closed cubes. -/
namespace CubeBoundaryCharts
open Set Metric
open scoped Classical NNReal

variable {n : ℕ}

abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

@[simp] theorem interior_cube : interior (cube n) = Set.univ.pi (fun _ => Set.Ioo (0 : ℝ) 1) := by
  change interior (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) = _
  rw [interior_pi_set Set.finite_univ]
  simp only [interior_Icc]

theorem insert_mem (i : Fin (n+1)) (ε : Fin 2) {y : Fin n → ℝ} (hy : y ∈ cube n) :
    i.insertNth (α := fun _ => ℝ) (ε : ℝ) y ∈ cube (n+1) := by
  intro j _
  refine i.succAboveCases ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same]
    constructor
    · positivity
    · exact_mod_cast Nat.le_of_lt_succ ε.isLt
  · simpa only [Fin.insertNth_apply_succAbove] using hy k (Set.mem_univ k)

theorem insert_dist (i : Fin (n+1)) (ε : Fin 2) (x y : Fin n → ℝ) :
    dist (i.insertNth (α := fun _ => ℝ) (ε : ℝ) x) (i.insertNth (α := fun _ => ℝ) (ε : ℝ) y) = dist x y := by
  rw [Fin.dist_insertNth_insertNth,dist_self,max_eq_right dist_nonneg]

/-- Every point of a closed cube outside its interior lies on a face. -/
theorem exists_face (y : Fin (n+1) → ℝ) (hy : y ∈ cube (n+1))
    (hyi : y ∉ interior (cube (n+1))) :
    ∃ i : Fin (n+1), ∃ ε : Fin 2, ∃ x : Fin n → ℝ,
      x ∈ cube n ∧ i.insertNth (α := fun _ => ℝ) (ε : ℝ) x = y := by
  have hh : ¬ ∀ i, 0 < y i ∧ y i < 1 := by
    intro h
    apply hyi
    rw [interior_cube]
    exact fun i _ => h i
  push_neg at hh
  obtain ⟨i,hi⟩ := hh
  have hib := hy i (Set.mem_univ i)
  have he : y i = 0 ∨ y i = 1 := by
    by_cases h : 0 < y i
    · exact Or.inr (le_antisymm hib.2 (hi h))
    · exact Or.inl (le_antisymm (le_of_not_gt h) hib.1)
  have hx : i.removeNth y ∈ cube n := fun k _ => hy (i.succAbove k) (Set.mem_univ _)
  rcases he with he | he
  · refine ⟨i,0,i.removeNth y,hx,?_⟩
    simpa only [Fin.val_zero,Nat.cast_zero,he] using Fin.insertNth_self_removeNth i y
  · refine ⟨i,1,i.removeNth y,hx,?_⟩
    simpa only [Fin.val_one,Nat.cast_one,he] using Fin.insertNth_self_removeNth i y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ]

/-- Parametrizations whose closed-cube images cover the closure and whose
open-cube images lie in the interior automatically provide lower-dimensional
boundary charts. -/
theorem exists_charts (S : Set E) (f : κ → (Fin (n+1) → ℝ) → E)
    (K : κ → ℝ≥0) (hf : ∀ j, LipschitzOnWith (K j) (f j) (cube (n+1)))
    (hclosure : ∀ z ∈ closure S, ∃ j y, y ∈ cube (n+1) ∧ f j y = z)
    (hinterior : ∀ j y, y ∈ interior (cube (n+1)) → f j y ∈ interior S) :
    ∃ g : (κ × Fin (n+1) × Fin 2) → (Fin n → ℝ) → E,
      (∀ j, LipschitzOnWith (K j.1) (g j) (cube n)) ∧
      ∀ z ∈ frontier S, ∃ j y, y ∈ cube n ∧ g j y = z := by
  let g : (κ × Fin (n+1) × Fin 2) → (Fin n → ℝ) → E :=
    fun j x => f j.1 (j.2.1.insertNth (α := fun _ => ℝ) (j.2.2 : ℝ) x)
  refine ⟨g,?_,?_⟩
  · intro j
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact (hf j.1).dist_le_mul _ (insert_mem _ _ hx) _ (insert_mem _ _ hy) |>.trans_eq
      (congrArg ((K j.1 : ℝ)*·) (insert_dist _ _ x y))
  · intro z hz
    obtain ⟨j,y,hy,he⟩ := hclosure z hz.1
    have hyi : y ∉ interior (cube (n+1)) := by
      intro h
      exact hz.2 (he ▸ hinterior j y h)
    obtain ⟨i,ε,x,hx,hxy⟩ := exists_face y hy hyi
    exact ⟨(j,i,ε),x,hx,by simpa only [g,hxy] using he⟩

/-- Smooth parametrizations on a closed cube satisfy the Lipschitz hypothesis. -/
theorem exists_lipschitz (f : (Fin n → ℝ) → E) (hf : ContDiffOn ℝ 1 f (cube n)) :
    ∃ K : ℝ≥0, LipschitzOnWith K f (cube n) :=
  hf.exists_lipschitzOnWith (by norm_num) (convex_pi fun _ _ => convex_Icc 0 1)
    (isCompact_univ_pi fun _ => isCompact_Icc)

end CubeBoundaryCharts



/- Smooth cube parametrizations of the signed real logarithmic fundamental cone. -/
namespace RealConeParametrization
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units.dirichletUnitTheorem
open Set MeasureTheory
open scoped Classical Pointwise

variable (K : Type*) [Field K] [NumberField K]

abbrev space := InfinitePlace K → ℝ

def absMap (x : space K) : space K := fun w => |x w|

def region : Set (space K) := absMap K ⁻¹' (expMapBasis '' paramSet K)

abbrev cube : Set (space K) := Set.univ.pi fun _ => Set.Icc 0 1

noncomputable def zeroRadial (x : space K) : space K := fun w => if w = w₀ then 0 else x w

noncomputable def chart (ε : InfinitePlace K → Fin 2) (x : space K) : space K :=
  fun w => (-1 : ℝ)^(ε w).val * x w₀ * expMapBasis (zeroRadial K x) w

theorem contDiff_expMapBasis : ContDiff ℝ 1 (expMapBasis : space K → space K) := by
  apply contDiff_pi.mpr
  intro w
  simp only [expMapBasis_apply,expMap_apply]
  change ContDiff ℝ 1 (fun x : space K => Real.exp ((w.mult : ℝ)⁻¹ *
    (completeBasis K).equivFunL.symm x w))
  fun_prop

theorem contDiff_zeroRadial : ContDiff ℝ 1 (zeroRadial K) := by
  apply contDiff_pi.mpr
  intro w
  dsimp only [zeroRadial]
  split_ifs <;> fun_prop

theorem contDiff_chart (ε : InfinitePlace K → Fin 2) : ContDiff ℝ 1 (chart K ε) := by
  apply contDiff_pi.mpr
  intro w
  dsimp only [chart]
  have hh := (contDiff_expMapBasis K).comp (contDiff_zeroRadial K)
  have hc : ContDiff ℝ 1 (fun x : space K => expMapBasis (zeroRadial K x) w) :=
    (contDiff_pi.mp hh) w
  fun_prop

theorem abs_chart (ε : InfinitePlace K → Fin 2) (x : space K) (hx : 0 ≤ x w₀) :
    absMap K (chart K ε x) = x w₀ • expMapBasis (zeroRadial K x) := by
  ext w
  simp only [absMap,chart,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg hx,abs_of_nonneg (expMapBasis_nonneg _ _),Pi.smul_apply,smul_eq_mul]

theorem continuous_absMap : Continuous (absMap K) := by unfold absMap; fun_prop

theorem closure_region_subset : closure (region K) ⊆ absMap K ⁻¹' compactSet K := by
  refine ((continuous_absMap K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  apply (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K)

/-- The closure is covered by signed smooth images of the closed cube. -/
theorem closure_covered (x : space K) (hx : x ∈ closure (region K)) :
    ∃ ε : InfinitePlace K → Fin 2, ∃ y : space K, y ∈ cube K ∧ chart K ε y = x := by
  have hh := closure_region_subset K hx
  obtain ⟨r,hr,_,⟨z,hz,rfl⟩,he⟩ := hh
  let y : space K := fun w => if w = w₀ then r else z w
  have hy : y ∈ cube K := by
    intro w _
    dsimp only [y]
    split_ifs with hw
    · exact hr
    · simpa only [if_neg hw] using hz w (Set.mem_univ _)
  have hyr : y w₀ = r := by simp [y]
  have hyz : zeroRadial K y = z := by
    ext w
    dsimp only [zeroRadial,y]
    split_ifs with hw
    · subst w
      exact (Set.mem_singleton_iff.mp (by simpa using hz w₀ (Set.mem_univ _))).symm
    · rfl
  let ε : InfinitePlace K → Fin 2 := fun w => if x w < 0 then 1 else 0
  refine ⟨ε,y,hy,?_⟩
  ext w
  have hew := congrFun he w
  change r * expMapBasis z w = |x w| at hew
  simp only [chart,hyr,hyz]
  rw [mul_assoc,hew]
  dsimp only [ε]
  split_ifs with hw
  · simp [abs_of_neg hw]
  · simp [abs_of_nonneg (le_of_not_gt hw)]

theorem preimage_interior_subset :
    absMap K ⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (region K) := by
  have hO : IsOpen (expMapBasis '' interior (paramSet K)) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  apply interior_maximal (Set.preimage_mono (Set.image_mono interior_subset))
  exact hO.preimage (continuous_absMap K)

/-- The open cube maps into the interior. -/
theorem interior_maps (ε : InfinitePlace K → Fin 2) (y : space K)
    (hy : y ∈ interior (cube K)) : chart K ε y ∈ interior (region K) := by
  have hy' : ∀ w, 0 < y w ∧ y w < 1 := by
    rw [show interior (cube K) = Set.univ.pi (fun _ => Set.Ioo (0 : ℝ) 1) by
      change interior (Set.univ.pi fun _ : InfinitePlace K => Set.Icc (0 : ℝ) 1) = _
      rw [interior_pi_set Set.finite_univ]
      simp only [interior_Icc]] at hy
    exact fun w => hy w (Set.mem_univ w)
  let z : space K := fun w => if w = w₀ then Real.log (y w₀) else y w
  apply preimage_interior_subset K
  refine ⟨z,?_,?_⟩
  · rw [interior_paramSet]
    intro w _
    dsimp only [z]
    split_ifs with hw
    · exact Real.log_neg (hy' w₀).1 (hy' w₀).2
    · exact hy' w
  · rw [expMapBasis_apply'',show z w₀ = Real.log (y w₀) by simp [z],Real.exp_log (hy' w₀).1,
      abs_chart K ε y (hy' w₀).1.le]
    congr 2
    ext w
    dsimp only [z,zeroRadial]
    split_ifs <;> rfl

end RealConeParametrization

namespace RealConeParametrization
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone NumberField.Units.dirichletUnitTheorem
open Set MeasureTheory
open scoped Classical Pointwise NNReal

variable (K : Type*) [Field K] [NumberField K]

theorem norm_absMap (x : space K) : ‖absMap K x‖ = ‖x‖ := by
  simp [absMap,Pi.norm_def,Real.norm_eq_abs]

theorem isBounded_region : Bornology.IsBounded (region K) := by
  obtain ⟨C,hC⟩ := (isCompact_compactSet K).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C,fun x hx => ?_⟩
  rw [← norm_absMap K x]
  exact hC _ (closure_region_subset K (subset_closure hx))

theorem volume_region_ne_top : volume (region K) ≠ ⊤ :=
  (isBounded_region K).measure_lt_top.ne

variable (n : ℕ) (e : Fin (n+1) ≃ InfinitePlace K)

def reindex (x : Fin (n+1) → ℝ) : space K := fun w => x (e.symm w)

theorem reindex_mem_cube {x : Fin (n+1) → ℝ} (hx : x ∈ CubeBoundaryCharts.cube (n+1)) :
    reindex K n e x ∈ cube K := fun w _ => hx (e.symm w) (Set.mem_univ _)

theorem reindex_mem_interior {x : Fin (n+1) → ℝ}
    (hx : x ∈ interior (CubeBoundaryCharts.cube (n+1))) :
    reindex K n e x ∈ interior (cube K) := by
  rw [CubeBoundaryCharts.interior_cube] at hx
  change reindex K n e x ∈ interior (Set.univ.pi fun _ : InfinitePlace K => Set.Icc (0 : ℝ) 1)
  rw [interior_pi_set Set.finite_univ]
  simp only [interior_Icc]
  exact fun w _ => hx (e.symm w) (Set.mem_univ _)

include e in
/-- The signed logarithmic fundamental cone has a finite Lipschitz boundary
parametrization of dimension one less than the number of infinite places. -/
theorem exists_boundary_charts :
    ∃ g : ((InfinitePlace K → Fin 2) × Fin (n+1) × Fin 2) → (Fin n → ℝ) → space K,
    ∃ C : ((InfinitePlace K → Fin 2) × Fin (n+1) × Fin 2) → ℝ≥0,
      (∀ j, LipschitzOnWith (C j) (g j) (CubeBoundaryCharts.cube n)) ∧
      ∀ z ∈ frontier (region K), ∃ j y, y ∈ CubeBoundaryCharts.cube n ∧ g j y = z := by
  let f : (InfinitePlace K → Fin 2) → (Fin (n+1) → ℝ) → space K :=
    fun ε x => chart K ε (reindex K n e x)
  have hfd (ε : InfinitePlace K → Fin 2) : ContDiff ℝ 1 (f ε) := by
    apply (contDiff_chart K ε).comp
    unfold reindex
    fun_prop
  have hf : ∀ ε, ∃ C : ℝ≥0, LipschitzOnWith C (f ε) (CubeBoundaryCharts.cube (n+1)) :=
    fun ε => CubeBoundaryCharts.exists_lipschitz _ (hfd ε).contDiffOn
  choose C hC using hf
  have hclosure : ∀ z ∈ closure (region K), ∃ ε y,
      y ∈ CubeBoundaryCharts.cube (n+1) ∧ f ε y = z := by
    intro z hz
    obtain ⟨ε,y,hy,he⟩ := closure_covered K z hz
    refine ⟨ε,fun i => y (e i),fun i _ => hy (e i) (Set.mem_univ _),?_⟩
    have hey : reindex K n e (fun i => y (e i)) = y := by
      ext w
      exact congrArg y (e.apply_symm_apply w)
    change chart K ε (reindex K n e (fun i => y (e i))) = z
    rw [hey]
    exact he
  have hi : ∀ ε y, y ∈ interior (CubeBoundaryCharts.cube (n+1)) →
      f ε y ∈ interior (region K) := by
    intro ε y hy
    exact interior_maps K ε _ (reindex_mem_interior K n e hy)
  obtain ⟨g,hg,hfront⟩ := CubeBoundaryCharts.exists_charts (region K) f C hC hclosure hi
  exact ⟨g,fun j => C j.1,hg,hfront⟩

end RealConeParametrization

namespace RealConeParametrization
open NumberField MeasureTheory
open scoped Pointwise Classical

variable (K : Type*) [Field K] [NumberField K]

/-- An effective lattice-point estimate in the signed logarithmic fundamental
cone, with the expected one-dimensional boundary saving. -/
theorem effective_lattice_count (n : ℕ) (e : Fin (n+1) ≃ InfinitePlace K)
    (b : (Fin (n+1) → ℝ) ≃L[ℝ] space K) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {z : Fin (n+1) → ℤ | b (fun i => (z i : ℝ)) ∈ t • region K} : ℝ)-
        t^(n+1)*volume.real (b ⁻¹' region K)| ≤ C*t^n := by
  obtain ⟨g,D,hg,hfront⟩ := exists_boundary_charts K n e
  simpa using LatticeBoundaryCount.exists_error_constant (region K) (isBounded_region K)
    n g D hg hfront b

end RealConeParametrization

namespace TotallyRealCoordinates
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

/-- In a totally real field, the real-place coordinates and mixed coordinates
are continuously linearly equivalent. -/
noncomputable def equiv : realSpace K ≃L[ℝ] mixedSpace K :=
  (LinearEquiv.ofBijective (mixedSpaceOfRealSpace (K := K)).toLinearMap ⟨injective_mixedSpaceOfRealSpace K,by
    intro x
    refine ⟨fun w => x.1 ⟨w,IsTotallyReal.isReal w⟩,?_⟩
    apply Prod.ext
    · rfl
    · funext w
      exact (not_isReal_iff_isComplex.mpr w.property (IsTotallyReal.isReal w.1)).elim⟩).toContinuousLinearEquiv

@[simp] theorem equiv_apply (x : realSpace K) : equiv K x = mixedSpaceOfRealSpace x := rfl

@[simp] theorem normAtAllPlaces_equiv (x : realSpace K) :
    normAtAllPlaces (equiv K x) = RealConeParametrization.absMap K x := by
  ext w
  change normAtPlace w (mixedSpaceOfRealSpace x) = |x w|
  rw [normAtPlace_apply_of_isReal (IsTotallyReal.isReal w)]
  rfl

/-- The signed real region is exactly the familiar norm<=1 fundamental cone
in mixed coordinates. -/
theorem preimage_normLeOne : (equiv K) ⁻¹' normLeOne K = RealConeParametrization.region K := by
  ext x
  rw [Set.mem_preimage,normLeOne_eq_preimage]
  change normAtAllPlaces (equiv K x) ∈ expMapBasis '' paramSet K ↔ _
  rw [normAtAllPlaces_equiv]
  rfl

end TotallyRealCoordinates



/- Integer coordinate points for a real basis. -/
namespace IntegerBasisGrid
open Module
open scoped Classical
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]

noncomputable def map (b : Basis ι ℝ E) (z : ι → ℤ) : E :=
  b.equivFunL.symm (fun i => (z i : ℝ))

theorem map_injective (b : Basis ι ℝ E) : Function.Injective (map b) := by
  intro z w h
  have h' := b.equivFunL.symm.injective h
  funext i
  exact_mod_cast congrFun h' i

theorem range_map (b : Basis ι ℝ E) :
    Set.range (map b) = (Submodule.span ℤ (Set.range b) : Set E) := by
  ext x
  rw [SetLike.mem_coe, b.mem_span_iff_repr_mem ℤ]
  constructor
  · rintro ⟨z,rfl⟩ i
    refine ⟨z i,?_⟩
    change (z i : ℝ) = b.equivFun (b.equivFun.symm (fun j => (z j : ℝ))) i
    rw [LinearEquiv.apply_symm_apply]
  · intro h
    choose z hz using h
    refine ⟨z, b.equivFunL.injective ?_⟩
    ext i
    simpa [map, Basis.equivFunL, Basis.equivFun_apply] using hz i

noncomputable def equiv (b : Basis ι ℝ E) :
    (ι → ℤ) ≃ Submodule.span ℤ (Set.range b) :=
  (Equiv.ofInjective (map b) (map_injective b)).trans
    (Equiv.setCongr (range_map b))

@[simp] theorem equiv_apply (b : Basis ι ℝ E) (z : ι → ℤ) :
    (equiv b z : E) = map b z := rfl

theorem card_grid (b : Basis ι ℝ E) (S : Set E) :
    Nat.card {z : ι → ℤ | map b z ∈ S} =
      Nat.card {x : Submodule.span ℤ (Set.range b) | (x : E) ∈ S} := by
  exact Nat.card_congr ((equiv b).subtypeEquiv (fun _ => Iff.rfl))

end IntegerBasisGrid

namespace TotallyRealCoordinates
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory
open scoped Classical Pointwise
variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

theorem mem_smul_normLeOne {t : ℝ} (ht : 0 < t) (x : mixedSpace K) :
    x ∈ t • normLeOne K ↔
      x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t ^ Module.finrank ℚ K := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero ht.ne'), mixedEmbedding.norm_smul,
    abs_of_pos (inv_pos.mpr ht), inv_pow]
  congr 1
  rw [← div_eq_inv_mul, div_le_iff₀ (pow_pos ht _), one_mul]

theorem effective_mixed_count (n : ℕ) (e : Fin (n+1) ≃ InfinitePlace K)
    (b : (Fin (n+1) → ℝ) ≃L[ℝ] mixedSpace K) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {z : Fin (n+1) → ℤ | b (fun i => (z i : ℝ)) ∈ t • normLeOne K} : ℝ)-
        t^(n+1)*volume.real (b ⁻¹' normLeOne K)| ≤ C*t^n := by
  let b' := b.trans (equiv K).symm
  have hpre : b' ⁻¹' RealConeParametrization.region K = b ⁻¹' normLeOne K := by
    rw [← preimage_normLeOne]
    ext x
    change equiv K ((equiv K).symm (b x)) ∈ normLeOne K ↔ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have hmem (t : ℝ) (x : Fin (n+1) → ℝ) :
      b' x ∈ t • RealConeParametrization.region K ↔ b x ∈ t • normLeOne K := by
    rw [← preimage_normLeOne]
    constructor
    · rintro ⟨y,hy,h⟩
      refine ⟨equiv K y,hy,?_⟩
      have hh := congrArg (equiv K) h
      simpa [b',map_smul] using hh
    · rintro ⟨y,hy,h⟩
      refine ⟨(equiv K).symm y,?_,?_⟩
      · change equiv K ((equiv K).symm y) ∈ normLeOne K
        rwa [ContinuousLinearEquiv.apply_symm_apply]
      · simpa [b',map_smul] using congrArg (equiv K).symm h
  obtain ⟨C,hC,h⟩ := RealConeParametrization.effective_lattice_count K n e b'
  refine ⟨C,hC,?_⟩
  intro t ht
  simpa only [hpre,hmem] using h t ht

/-- Effective count for an arbitrary integer span, in the norm fundamental cone. -/
theorem effective_span_count (n : ℕ) (e : Fin (n+1) ≃ InfinitePlace K)
    (b : Module.Basis (Fin (n+1)) ℝ (mixedSpace K)) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {x : Submodule.span ℤ (Set.range b) | (x : mixedSpace K) ∈ t • normLeOne K} : ℝ)-
        t^(n+1)*volume.real (b.equivFunL.symm ⁻¹' normLeOne K)| ≤ C*t^n := by
  obtain ⟨C,hC,h⟩ := effective_mixed_count K n e b.equivFunL.symm
  refine ⟨C,hC,?_⟩
  intro t ht
  simpa only [← IntegerBasisGrid.card_grid, IntegerBasisGrid.map] using h t ht

end TotallyRealCoordinates

namespace TotallyRealCoordinates
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone MeasureTheory Module
open scoped Classical Pointwise nonZeroDivisors
variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

theorem card_places : Fintype.card (InfinitePlace K) = Module.finrank ℚ K := by
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  simpa only [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] using
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K

theorem card_idealLattice_cone (J : (Ideal (𝓞 K))⁰) {t : ℝ} (ht : 0 < t) :
    Nat.card {x : idealLattice K (FractionalIdeal.mk0 K J) | (x : mixedSpace K) ∈ t • normLeOne K} =
      Nat.card {a : idealSet K J | mixedEmbedding.norm (a : mixedSpace K) ≤ t^Module.finrank ℚ K} := by
  have hset : {x : mixedSpace K | x ∈ idealLattice K (FractionalIdeal.mk0 K J) ∧
      x ∈ t • normLeOne K} =
      {x : mixedSpace K | x ∈ idealSet K J ∧ mixedEmbedding.norm x ≤ t^Module.finrank ℚ K} := by
    ext x
    simp only [Set.mem_setOf_eq, mem_smul_normLeOne K ht, mem_idealSet,
      mem_idealLattice, FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨⟨y,⟨a,ha,rfl⟩,hy⟩,hx,hn⟩
      exact ⟨⟨hx,a,ha,hy⟩,hn⟩
    · rintro ⟨⟨hx,a,ha,hy⟩,hn⟩
      exact ⟨⟨(a : K),⟨a,ha,rfl⟩,hy⟩,hx,hn⟩
  exact Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    ((Equiv.setCongr hset).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm))

/-- The effective cone estimate specialized to the lattice of any integral ideal. -/
theorem effective_idealSet_count (n : ℕ) (hd : Module.finrank ℚ K = n+1)
    (J : (Ideal (𝓞 K))⁰) :
    ∃ A : ℝ, ∃ C > (0 : ℝ), ∀ t : ℝ, 1 ≤ t →
      |(Nat.card {a : idealSet K J | mixedEmbedding.norm (a : mixedSpace K) ≤ t^(n+1)} : ℝ)-
        t^(n+1)*A| ≤ C*t^n := by
  let b₀ := fractionalIdealLatticeBasis K (FractionalIdeal.mk0 K J)
  let f : Free.ChooseBasisIndex ℤ ((FractionalIdeal.mk0 K J) : FractionalIdeal (𝓞 K)⁰ K) ≃ Fin (n+1) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, ← finrank_eq_card_basis b₀,
      mixedEmbedding.finrank,hd])
  let b := b₀.reindex f
  have hspan : Submodule.span ℤ (Set.range b) = idealLattice K (FractionalIdeal.mk0 K J) := by
    rw [show Set.range b = Set.range b₀ by
      simpa only [b, Basis.coe_reindex] using f.symm.surjective.range_comp (b₀ : _ → mixedSpace K)]
    exact span_idealLatticeBasis K _
  let e : Fin (n+1) ≃ InfinitePlace K :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin,card_places K,hd])
  obtain ⟨C,hC,h⟩ := effective_span_count K n e b
  refine ⟨volume.real (b.equivFunL.symm ⁻¹' normLeOne K),C,hC,?_⟩
  intro t ht
  have hh := h t ht
  rw [hspan,card_idealLattice_cone K J (lt_of_lt_of_le zero_lt_one ht),hd] at hh
  exact hh

end TotallyRealCoordinates



/- Extracting the leading constant and power saving from radial counts. -/
namespace PowerCountingAnalysis
open Filter Topology

theorem coefficient_eq (f : ℝ → ℝ) (n : ℕ) (a b C k : ℝ) (ha : 0 < a)
    (hf : Tendsto (fun x => f x/x) atTop (𝓝 k))
    (hbound : ∀ t : ℝ, 1 ≤ t → |f (a*t^(n+1))-b*t^(n+1)| ≤ C*t^n) : b = a*k := by
  have hp : Tendsto (fun t : ℝ => t^(n+1)) atTop atTop := tendsto_pow_atTop (by omega)
  have harg : Tendsto (fun t : ℝ => a*t^(n+1)) atTop atTop := hp.const_mul_atTop ha
  have hratio : Tendsto (fun t : ℝ => f (a*t^(n+1))/t^(n+1)) atTop (𝓝 (a*k)) := by
    apply ((hf.comp harg).const_mul a).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp
    field_simp
  have herror : Tendsto (fun t : ℝ => |f (a*t^(n+1))/t^(n+1)-b|) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => C/t) atTop (𝓝 0) := by
      have hh := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul C
      simpa only [div_eq_mul_inv,mul_zero] using hh
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun t : ℝ => C/t) ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    calc
      _ = |f (a*t^(n+1))-b*t^(n+1)| / t^(n+1) := by
        calc
          _ = |(f (a*t^(n+1))-b*t^(n+1))/t^(n+1)| := by
            congr 1
            field_simp
          _ = _ := by rw [abs_div,abs_of_pos (pow_pos ht0 _)]
      _ ≤ C*t^n/t^(n+1) := div_le_div_of_nonneg_right (hbound t ht) (pow_nonneg ht0.le _)
      _ = C/t := by rw [pow_succ]; field_simp
  have hb : Tendsto (fun t : ℝ => f (a*t^(n+1))/t^(n+1)) atTop (𝓝 b) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using herror)
  exact tendsto_nhds_unique hb hratio

/-- A radial error of degree n in dimension n+1 gives a fixed power saving. -/
theorem radial_bound_rpow (f : ℝ → ℝ) (n : ℕ) (a C k : ℝ) (ha : 0 < a)
    (hbound : ∀ t : ℝ, 1 ≤ t → |f (a*t^(n+1))-k*(a*t^(n+1))| ≤ C*t^n)
    (x : ℝ) (hx : a ≤ x) :
    |f x-k*x| ≤ (C/a^((n : ℝ)/(n+1)))*x^((n : ℝ)/(n+1)) := by
  have hx0 : 0 < x := ha.trans_le hx
  let t := (x/a)^((n+1 : ℕ) : ℝ)⁻¹
  have ht : 1 ≤ t := Real.one_le_rpow ((le_div_iff₀ ha).mpr (by simpa using hx)) (by positivity)
  have htd : t^(n+1) = x/a := Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have he : a*t^(n+1) = x := by rw [htd]; field_simp
  have htn : t^n = (x/a)^((n : ℝ)/(n+1)) := by
    rw [show t^n = t^(n : ℝ) from (Real.rpow_natCast t n).symm]
    dsimp [t]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hh := hbound t ht
  rw [he,htn,Real.div_rpow hx0.le ha.le] at hh
  convert hh using 1 <;> ring

end PowerCountingAnalysis

namespace EffectiveIdealClass
open NumberField Ideal Module Filter Topology
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open scoped Classical nonZeroDivisors Real
variable (K : Type*) [Field K] [NumberField K]

noncomputable def count (c : ClassGroup (𝓞 K)) (s : ℝ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s ∧ ClassGroup.mk0 I = c}

noncomputable def mainCoefficient : ℝ :=
  (2 ^ InfinitePlace.nrRealPlaces K * (2 * π) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K) /
    (Units.torsionOrder K * Real.sqrt |NumberField.discr K|)

/-- Multiplication by an ideal in the inverse class converts a class count
into a principal-ideal divisibility count. -/
theorem count_eq_principal {c : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰}
    (hJ : ClassGroup.mk0 J = c⁻¹) (s : ℝ) :
    count K c s = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧
      Submodule.IsPrincipal (I : Ideal (𝓞 K)) ∧ (absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ s*absNorm (J : Ideal (𝓞 K))} := by
  unfold count
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I ↦ ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ ↦ J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ ↦
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

/-- Power-saving error for each ordinary ideal class in a totally real field. -/
theorem exists_power_error [IsTotallyReal K] (n : ℕ) (hd : finrank ℚ K = n+1)
    (c : ClassGroup (𝓞 K)) :
    ∃ D > (0 : ℝ), ∀ᶠ s : ℝ in atTop,
      |(count K c s : ℝ)-mainCoefficient K*s| ≤ D*s^((n : ℝ)/(n+1)) := by
  obtain ⟨J,hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  let N : ℝ := absNorm (J : Ideal (𝓞 K))
  let w : ℝ := Units.torsionOrder K
  have hN : 0 < N := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)
  have hw : 0 < w := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Units.torsionOrder_ne_zero K))
  let a := N⁻¹
  have ha : 0 < a := inv_pos.mpr hN
  have hcard (t : ℝ) :
      Nat.card {x : idealSet K J | mixedEmbedding.norm (x : mixedSpace K) ≤ t^(n+1)} =
        count K c (a*t^(n+1)) * Units.torsionOrder K := by
    change Nat.card {x : idealSet K J // mixedEmbedding.norm (x : mixedSpace K) ≤ t^(n+1)} = _
    rw [← card_isPrincipal_dvd_norm_le K J, count_eq_principal K hJ]
    congr 1
    have he : a*t^(n+1)*(absNorm (J : Ideal (𝓞 K)) : ℝ) = t^(n+1) := by
      change N⁻¹*t^(n+1)*N = _
      field_simp
    rw [he]
  obtain ⟨A,C,hC,h⟩ := TotallyRealCoordinates.effective_idealSet_count K n hd J
  let f : ℝ → ℝ := fun s => count K c s
  have hb : ∀ t : ℝ, 1 ≤ t → |f (a*t^(n+1))-(A/w)*t^(n+1)| ≤ (C/w)*t^n := by
    intro t ht
    have hh := h t ht
    rw [hcard,Nat.cast_mul] at hh
    apply (mul_le_mul_iff_right₀ hw).mp
    calc
      w*|f (a*t^(n+1))-(A/w)*t^(n+1)| = |f (a*t^(n+1))*w-t^(n+1)*A| := by
        calc
          _ = |w*(f (a*t^(n+1))-(A/w)*t^(n+1))| := by rw [abs_mul,abs_of_pos hw]
          _ = _ := by congr 1; field_simp
      _ ≤ C*t^n := hh
      _ = w*((C/w)*t^n) := by field_simp
  have hcoef : A/w = a*mainCoefficient K := PowerCountingAnalysis.coefficient_eq f n a (A/w) (C/w)
    (mainCoefficient K) ha (NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c) hb
  have hb' : ∀ t : ℝ, 1 ≤ t → |f (a*t^(n+1))-mainCoefficient K*(a*t^(n+1))| ≤ (C/w)*t^n := by
    intro t ht
    have hh := hb t ht
    rw [hcoef] at hh
    convert hh using 1 <;> ring
  refine ⟨(C/w)/a^((n : ℝ)/(n+1)),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop a] with s hs
  exact PowerCountingAnalysis.radial_bound_rpow f n a (C/w) (mainCoefficient K) ha hb' s hs

/-- Weights with zero total have power-saving cancellation in their ideal counts. -/
theorem exists_weighted_power_error [IsTotallyReal K] (n : ℕ) (hd : finrank ℚ K = n+1)
    (χ : ClassGroup (𝓞 K) → ℝ) (hχ : ∑ c, χ c = 0) :
    ∃ D > (0 : ℝ), ∀ᶠ s : ℝ in atTop,
      |∑ c, χ c*(count K c s : ℝ)| ≤ D*s^((n : ℝ)/(n+1)) := by
  have h := fun c => exists_power_error K n hd c
  choose D hD hbound using h
  let C := ∑ c, |χ c| *D c
  have hC : 0 ≤ C := Finset.sum_nonneg (fun c _ => mul_nonneg (abs_nonneg _) (hD c).le)
  refine ⟨C+1,by positivity,?_⟩
  have hevent : ∀ᶠ s : ℝ in atTop, ∀ c, |(count K c s : ℝ)-mainCoefficient K*s| ≤ D c*s^((n : ℝ)/(n+1)) :=
    Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_ge_atTop (0 : ℝ)] with s hs hs0
  have he : (∑ c, χ c*((count K c s : ℝ)-mainCoefficient K*s)) =
      ∑ c, χ c*(count K c s : ℝ) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hχ,zero_mul,sub_zero]
  rw [← he]
  calc
    _ ≤ ∑ c, |χ c*((count K c s : ℝ)-mainCoefficient K*s)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, |χ c| *(D c*s^((n : ℝ)/(n+1))) := by
      apply Finset.sum_le_sum
      intro c _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs c) (abs_nonneg _)
    _ = C*s^((n : ℝ)/(n+1)) := by dsimp [C]; simp only [Finset.sum_mul,mul_assoc]
    _ ≤ (C+1)*s^((n : ℝ)/(n+1)) := by gcongr; linarith

end EffectiveIdealClass



/- Finite sums grouped by a positive, finite-fiber integer norm. -/
namespace NormCounting
open scoped Classical BigOperators

structure Data (α : Type*) where
  norm : α → ℕ
  pos : ∀ x, 0 < norm x
  finite_le : ∀ N, {x | norm x ≤ N}.Finite

namespace Data
variable {α : Type*} (D : Data α)
noncomputable def sectionLe (N : ℕ) : Finset α := (D.finite_le N).toFinset

@[simp] theorem mem_sectionLe (N : ℕ) (x : α) : x ∈ D.sectionLe N ↔ D.norm x ≤ N :=
  Set.Finite.mem_toFinset _

noncomputable def fiber (N : ℕ) : Finset α := (D.sectionLe N).filter (fun x => D.norm x = N)

@[simp] theorem mem_fiber (N : ℕ) (x : α) : x ∈ D.fiber N ↔ D.norm x = N := by
  simp [fiber]
  exact fun h => h ▸ Nat.le_refl N

variable {M : Type*} [AddCommMonoid M]
noncomputable def coeff (W : α → M) (n : ℕ) : M := ∑ x ∈ D.fiber n, W x

@[simp] theorem coeff_zero (W : α → M) : D.coeff W 0 = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  exact ((D.pos x).ne' ((D.mem_fiber 0 x).mp hx)).elim

/-- The summatory coefficients are precisely the weighted norm-bounded count. -/
theorem sum_coeff (W : α → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, D.coeff W n = ∑ x ∈ D.sectionLe N, W x := by
  have hf (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      D.fiber n = (D.sectionLe N).filter (fun x => D.norm x = n) := by
    ext x
    simp only [mem_fiber,Finset.mem_filter,mem_sectionLe]
    exact ⟨fun h => ⟨h ▸ (Finset.mem_Icc.mp hn).2,h⟩,And.right⟩
  simp_rw [coeff]
  rw [Finset.sum_congr rfl (fun n hn => congrArg (fun s : Finset α => ∑ x ∈ s, W x) (hf n hn))]
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_Icc.mpr
    ⟨D.pos x,(D.mem_sectionLe N x).mp hx⟩) W

/-- Taking norms before grouping only increases the summatory count. -/
theorem sum_norm_coeff_le {E : Type*} [SeminormedAddCommGroup E] (W : α → E) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖D.coeff W n‖ ≤ ∑ x ∈ D.sectionLe N, ‖W x‖ := by
  rw [← D.sum_coeff (fun x => ‖W x‖) N]
  apply Finset.sum_le_sum
  intro n _
  exact norm_sum_le _ _

/-- A finite class decomposition of a weighted count. -/
theorem sum_class {β : Type*} [Fintype β] (cl : α → β) (χ : β → ℝ) (N : ℕ) :
    ∑ x ∈ D.sectionLe N, χ (cl x) =
      ∑ c, χ c*(Nat.card {x : α // D.norm x ≤ N ∧ cl x = c} : ℝ) := by
  rw [← Finset.sum_fiberwise (D.sectionLe N) cl (fun x => χ (cl x))]
  apply Finset.sum_congr rfl
  intro c _
  have hc : Nat.card {x : α // D.norm x ≤ N ∧ cl x = c} =
      ((D.sectionLe N).filter (fun x => cl x = c)).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.setCongr (by ext x; simp; rfl))
  rw [hc]
  calc
    _ = ∑ x ∈ (D.sectionLe N).filter (fun x => cl x = c), χ c :=
      Finset.sum_congr rfl (fun x hx => congrArg χ (Finset.mem_filter.mp hx).2)
    _ = _ := by simp [mul_comm]

end Data
end NormCounting



/- A power-saving summatory estimate bounds a Dirichlet series near one. -/
namespace LSeriesPowerBound
open Filter Topology MeasureTheory Asymptotics Finset

/-- Finite initial segments can be absorbed in a polynomial bound. -/
theorem global_bound {E : Type*} [NormedAddCommGroup E] (S : ℕ → E) (q C : ℝ)
    (hq : 0 ≤ q) (hC : 0 < C)
    (h : ∀ᶠ n : ℕ in atTop, ‖S n‖ ≤ C*(n : ℝ)^q) :
    ∃ D > (0 : ℝ), ∀ n : ℕ, 1 ≤ n → ‖S n‖ ≤ D*(n : ℝ)^q := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B := ∑ k ∈ Finset.range N, ‖S k‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨C+B+1,by positivity,?_⟩
  intro n hn
  have hpow : 1 ≤ (n : ℝ)^q := Real.one_le_rpow (by exact_mod_cast hn) hq
  by_cases hnN : N ≤ n
  · calc
      _ ≤ C*(n : ℝ)^q := hN n hnN
      _ ≤ (C+B+1)*(n : ℝ)^q := by gcongr; linarith
  · have hh : ‖S n‖ ≤ B := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ B := hh
      _ ≤ (C+B+1)*(n : ℝ)^q := by nlinarith

/-- Uniform boundedness on the real interval (1,2] follows from cancellation
of order x^q with q<1, wherever the original L-series converges absolutely. -/
theorem norm_le (f : ℕ → ℂ) (q C : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C*(n : ℝ)^q)
    (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) (hconv : LSeriesSummable f (s : ℂ)) :
    ‖LSeries f (s : ℂ)‖ ≤ 2*C/(1-q) := by
  have hqpos : 0 < 1-q := sub_pos.mpr hq
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] (fun n : ℕ => (n : ℝ)^q) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) q)] using hbound n hn
  rw [LSeries_eq_mul_integral f hq0 (by simpa using hq.trans hs) hconv hO,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (lt_trans zero_lt_one hs)]
  have hmajor : IntegrableOn (fun t : ℝ => C*t^(q-2)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : q-2 < -1) zero_lt_one).const_mul C
  have hint : ‖∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) *
      (t : ℂ)^(-((s : ℂ)+1))‖ ≤ ∫ t in Set.Ioi (1 : ℝ), C*t^(q-2) := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hn : 1 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht0.le).mpr (by simpa using ht1)
    have hp : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ C*t^q :=
      (hbound _ hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht0.le) hq0) hC)
    have hc : ‖(t : ℂ)^(-((s : ℂ)+1))‖ = t^(-s-1) := by
      rw [show -((s : ℂ)+1) = ((-s-1 : ℝ) : ℂ) by push_cast; ring,Complex.norm_cpow_real]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht0]
    rw [norm_mul,hc]
    calc
      _ ≤ (C*t^q)*t^(-s-1) := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg ht0.le _)
      _ = C*t^(q+(-s-1)) := by rw [Real.rpow_add ht0]; ring
      _ ≤ C*t^(q-2) := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) hC
  have he : (∫ t in Set.Ioi (1 : ℝ), C*t^(q-2)) = C/(1-q) := by
    rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : q-2 < -1) zero_lt_one,Real.one_rpow]
    rw [show q-2+1 = -(1-q) by ring,div_neg,neg_div,neg_neg]
    ring
  rw [he] at hint
  calc
    _ ≤ s*(C/(1-q)) := mul_le_mul_of_nonneg_left hint (le_of_lt (lt_trans zero_lt_one hs))
    _ ≤ 2*(C/(1-q)) := mul_le_mul_of_nonneg_right hs2 (by positivity)
    _ = _ := by ring

end LSeriesPowerBound

namespace IdealClassSeries
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K : Type*) [Field K] [NumberField K]

noncomputable def data : NormCounting.Data (Ideal (𝓞 K))⁰ where
  norm I := absNorm (I : Ideal (𝓞 K))
  pos I := absNorm_pos_of_nonZeroDivisors I
  finite_le := finite_setOf_absNorm_le₀

noncomputable def coeff (χ : ClassGroup (𝓞 K) → ℝ) (n : ℕ) : ℝ :=
  (data K).coeff (fun I => χ (ClassGroup.mk0 I)) n

/-- Summing ideal-norm coefficients gives the class-weighted ideal count. -/
theorem sum_coeff (χ : ClassGroup (𝓞 K) → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, coeff K χ n =
      ∑ c, χ c*(EffectiveIdealClass.count K c N : ℝ) := by
  unfold coeff
  rw [NormCounting.Data.sum_coeff,NormCounting.Data.sum_class]
  congr 1
  ext c
  congr 2
  simp only [EffectiveIdealClass.count,data,Nat.cast_le]

/-- The norm-sum of coefficients is dominated by counting absolute class weights. -/
theorem sum_norm_coeff_le (χ : ClassGroup (𝓞 K) → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖(coeff K χ n : ℂ)‖ ≤
      ∑ c, |χ c| *(EffectiveIdealClass.count K c N : ℝ) := by
  have h := (data K).sum_norm_coeff_le (fun I => χ (ClassGroup.mk0 I)) N
  have he := (data K).sum_class ClassGroup.mk0 (fun c => |χ c|) N
  simp only [Real.norm_eq_abs] at h
  rw [he] at h
  simpa only [coeff,Complex.norm_real,Real.norm_eq_abs,EffectiveIdealClass.count,data,Nat.cast_le] using h

/-- Any bounded class weight gives an absolutely convergent ideal series for Re(s)>1. -/
theorem summable (χ : ClassGroup (𝓞 K) → ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff K χ n : ℂ)) s := by
  let B : ℕ → ℝ := fun n => ∑ c, |χ c| *(EffectiveIdealClass.count K c n : ℝ)
  have hB0 (n : ℕ) : 0 ≤ B n := Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hlim : Tendsto (fun n : ℕ => B n/(n : ℝ)) atTop
      (𝓝 (∑ c, |χ c| *EffectiveIdealClass.mainCoefficient K)) := by
    have hh := tendsto_finset_sum Finset.univ (fun c _ =>
      ((NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c).comp
        tendsto_natCast_atTop_atTop).const_mul |χ c|)
    simpa only [B,EffectiveIdealClass.count,EffectiveIdealClass.mainCoefficient,
      Finset.sum_div,mul_div_assoc,Function.comp_apply] using hh
  have hBO : B =O[atTop] (fun n : ℕ => (n : ℝ)^(1 : ℝ)) :=
    isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa only [Real.rpow_one] using hlim)
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(coeff K χ k : ℂ)‖) =O[atTop] B := by
    apply IsBigO.of_bound 1
    exact Filter.Eventually.of_forall (fun n => by
      simpa only [one_mul,Real.norm_eq_abs,abs_of_nonneg (hB0 n),
        abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] using sum_norm_coeff_le K χ n)
  exact LSeriesSummable_of_sum_norm_bigO (hO.trans hBO) (by norm_num) hs

/-- Nontrivial real class weights of total zero have uniformly bounded
Dirichlet series as the real argument tends to one from above. -/
theorem bounded_near_one [IsTotallyReal K] (n : ℕ) (hd : finrank ℚ K = n+1)
    (χ : ClassGroup (𝓞 K) → ℝ) (hχ : ∑ c, χ c = 0) :
    ∃ B > (0 : ℝ), ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun k => (coeff K χ k : ℂ)) (s : ℂ)‖ ≤ B := by
  let q : ℝ := (n : ℝ)/(n+1)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q < 1 := by dsimp [q]; apply (div_lt_one (by positivity)).mpr; linarith
  obtain ⟨C,hC,h⟩ := EffectiveIdealClass.exists_weighted_power_error K n hd χ hχ
  have hn : ∀ᶠ N : ℕ in atTop,
      ‖∑ k ∈ Finset.Icc 1 N, (coeff K χ k : ℂ)‖ ≤ C*(N : ℝ)^q := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually h
    filter_upwards [hh] with N hN
    simpa only [← Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,sum_coeff] using hN
  obtain ⟨D,hD,hbound⟩ := LSeriesPowerBound.global_bound
    (fun N => ∑ k ∈ Finset.Icc 1 N, (coeff K χ k : ℂ)) q C hq0 hC hn
  have hp : 0 < 1-q := sub_pos.mpr hq
  refine ⟨2*D/(1-q),by positivity,?_⟩
  intro s hs hs2
  exact LSeriesPowerBound.norm_le _ q D hq0 hq hD.le hbound s hs hs2
    (summable K χ (by simpa using hs))

end IdealClassSeries

namespace NormCounting.Data
open scoped Classical BigOperators
variable {α : Type*} (D : NormCounting.Data α)

/-- The series over one norm fiber is a finite sum. -/
theorem tsum_fiber (W : α → ℝ) (n : ℕ) :
    (∑' x : {x : α // D.norm x = n}, W x.1) = D.coeff W n := by
  let e : {x : α // x ∈ D.fiber n} ≃ {x : α // D.norm x = n} :=
    Equiv.subtypeEquivRight (fun x => D.mem_fiber n x)
  rw [← e.tsum_eq (fun x => W x.1)]
  change (∑' x : {x : α // x ∈ D.fiber n}, W x.1) = _
  exact Finset.tsum_subtype (D.fiber n) W

/-- Grouping a nonnegative series by finite norm fibers preserves summability. -/
theorem summable_iff_coeff (W : α → ℝ) (hW : ∀ x, 0 ≤ W x) :
    Summable W ↔ Summable (D.coeff W) := by
  have hpart : ∀ x : α, ∃! n : ℕ, x ∈ {x : α | D.norm x = n} :=
    fun x => ⟨D.norm x,rfl,fun n hn => hn.symm⟩
  have hfinite (n : ℕ) : Summable (fun x : {x : α // D.norm x = n} => W x.1) := by
    have hfin : {x : α | D.norm x = n}.Finite := (D.finite_le n).subset (fun x hx => hx.le)
    exact hfin.summable W
  rw [summable_partition hW hpart]
  change ((∀ n, Summable (fun x : {x : α // D.norm x = n} => W x.1)) ∧
    Summable (fun n => ∑' x : {x : α // D.norm x = n}, W x.1)) ↔ _
  simp only [D.tsum_fiber]
  exact and_iff_right hfinite

/-- Grouping an absolutely convergent real series by norm does not change its sum. -/
theorem tsum_coeff (W : α → ℝ) (hW : Summable W) :
    (∑' n, D.coeff W n) = ∑' x, W x := by
  let e := Equiv.sigmaFiberEquiv D.norm
  have hs := e.summable_iff.mpr hW
  calc
    _ = ∑' n, ∑' x : {x : α // D.norm x = n}, W x.1 :=
      tsum_congr (fun n => (D.tsum_fiber W n).symm)
    _ = ∑' p : (n : ℕ) × {x : α // D.norm x = n}, W p.2.1 := hs.tsum_sigma.symm
    _ = _ := e.tsum_eq W

/-- A factor depending only on the norm pulls out of each coefficient. -/
theorem coeff_mul_norm (W : α → ℝ) (g : ℕ → ℝ) (n : ℕ) :
    D.coeff (fun x => W x*g (D.norm x)) n = D.coeff W n*g n := by
  unfold coeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  change W x*g (D.norm x) = _
  rw [(D.mem_fiber n x).mp hx]

end NormCounting.Data



/- Real-coefficient L-series and norm-power weighted sums. -/
namespace RealLSeries

theorem term_eq (f : ℕ → ℝ) (hf : f 0 = 0) (s : ℝ) (n : ℕ) :
    LSeries.term (fun k => (f k : ℂ)) (s : ℂ) n =
      ((f n*(n : ℝ)^(-s) : ℝ) : ℂ) := by
  rw [LSeries.term_def₀ (by simp only [hf,Complex.ofReal_zero])]
  simp only [Complex.ofReal_mul,Complex.ofReal_cpow (Nat.cast_nonneg n),Complex.ofReal_neg,
    Complex.ofReal_natCast]

theorem summable (f : ℕ → ℝ) (hf : f 0 = 0) (s : ℝ)
    (hs : LSeriesSummable (fun k => (f k : ℂ)) (s : ℂ)) :
    Summable (fun n => f n*(n : ℝ)^(-s)) := by
  unfold LSeriesSummable at hs
  change Summable (fun n => LSeries.term (fun k => (f k : ℂ)) (s : ℂ) n) at hs
  simpa only [term_eq f hf s,Complex.summable_ofReal] using hs

theorem eq_tsum (f : ℕ → ℝ) (hf : f 0 = 0) (s : ℝ) :
    LSeries (fun k => (f k : ℂ)) (s : ℂ) = ((∑' n, f n*(n : ℝ)^(-s) : ℝ) : ℂ) := by
  simp only [LSeries,term_eq f hf s,Complex.ofReal_tsum]

end RealLSeries



/- Products of finitely many absolutely convergent series. -/
namespace FiniteProductSeries
set_option maxHeartbeats 2000000
open scoped Classical BigOperators

def Property (ι : Type*) [Fintype ι] : Prop :=
  ∀ f : ι → ℕ → ℝ, (∀ i, Summable (fun n => ‖f i n‖)) →
    Summable (fun z : ι → ℕ => ‖∏ i, f i (z i)‖) ∧
      HasSum (fun z : ι → ℕ => ∏ i, f i (z i)) (∏ i, ∑' n, f i n)

theorem summable_hasSum (ι : Type*) [Fintype ι] : Property ι := by
  refine Fintype.induction_empty_option (P := Property) ?_ ?_ ?_ ι
  · intro α β _ e ih f hf
    letI := Fintype.ofEquiv β e.symm
    have h := ih (fun a => f (e a)) (fun a => hf (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he (z : β → ℕ) : (∏ a, f (e a) (E z a)) = ∏ b, f b (z b) := by
      change (∏ a, f (e a) (z (e a))) = _
      exact e.prod_comp (fun b => f b (z b))
    constructor
    · simpa only [Function.comp_def,he] using E.summable_iff.mpr h.1
    · have hh := E.hasSum_iff.mpr h.2
      have hc := e.prod_comp (fun b => ∑' n, f b n)
      simpa only [Function.comp_def,he,hc] using hh
  · intro f hf
    constructor
    · exact summable_of_finite_support (Set.toFinite _)
    · simpa using hasSum_unique (fun z : PEmpty → ℕ => ∏ i, f i (z i))
  · intro α _ ih f hf
    have h := ih (fun a => f (some a)) (fun a => hf (some a))
    let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    have he (z : Option α → ℕ) :
        f none (E z).1 * (∏ a, f (some a) ((E z).2 a)) = ∏ a, f a (z a) := by
      change f none (z none)*(∏ a, f (some a) (z (some a))) = _
      exact (Fintype.prod_option (fun a : Option α => f a (z a))).symm
    constructor
    · have hh := (hf none).mul_norm h.1
      simpa only [Function.comp_def,he] using E.summable_iff.mpr hh
    · have hh := (hf none).of_norm.hasSum.mul h.2 (summable_mul_of_summable_norm (hf none) h.1)
      have hh' := E.hasSum_iff.mpr hh
      simpa only [Function.comp_def,he,Fintype.prod_option] using hh'

end FiniteProductSeries
namespace MultisetEuler
open scoped Classical BigOperators
open Filter Topology

variable {ι : Type*}

theorem prod_eq_count [Fintype ι] (w : ι → ℝ) (m : Multiset ι) :
    (m.map w).prod = ∏ i, w i ^ m.count i := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,ih,Multiset.count_cons,pow_add,Finset.prod_mul_distrib]
    simp [mul_comm]

noncomputable def countEquiv [Fintype ι] : Multiset ι ≃ (ι → ℕ) :=
  Multiset.toFinsupp.toEquiv.trans Finsupp.equivFunOnFinite

@[simp] theorem countEquiv_apply [Fintype ι] (m : Multiset ι) (i : ι) :
    countEquiv m i = m.count i := rfl

theorem finite_hasSum [Fintype ι] (w : ι → ℝ) (hw : ∀ i, ‖w i‖ < 1) :
    HasSum (fun m : Multiset ι => (m.map w).prod) (∏ i, (1-w i)⁻¹) := by
  obtain ⟨_,hh⟩ := FiniteProductSeries.summable_hasSum ι (fun i n => w i ^ n)
    (fun i => by
      have hi : Summable (fun n : ℕ => ‖w i‖^n) :=
        summable_geometric_of_norm_lt_one (by simpa only [norm_norm] using hw i)
      simpa only [norm_pow] using hi)
  have he := (countEquiv (ι := ι)).hasSum_iff.mpr hh
  simpa only [Function.comp_def,countEquiv_apply,← prod_eq_count,
    tsum_geometric_of_norm_lt_one (hw _)] using he

theorem mem_range_map_subtype (s : Finset ι) (m : Multiset ι)
    (hm : ∀ x ∈ m, x ∈ s) :
    m ∈ Set.range (Multiset.map (Subtype.val : s → ι)) := by
  lift m to Multiset s using hm with a ha
  exact ⟨a,rfl⟩

noncomputable def restricted (w : ι → ℝ) (s : Finset ι) (m : Multiset ι) : ℝ :=
  if m ∈ Set.range (Multiset.map (Subtype.val : s → ι)) then (m.map w).prod else 0

theorem restricted_hasSum (w : ι → ℝ) (hw : ∀ i, ‖w i‖ < 1) (s : Finset ι) :
    HasSum (restricted w s) (∏ i ∈ s, (1-w i)⁻¹) := by
  apply (Multiset.map_injective (f := (Subtype.val : s → ι)) Subtype.val_injective).hasSum_iff
    (fun m hm => by simp [restricted,hm]) |>.mp
  have hh := finite_hasSum (fun i : s => w i) (fun i => hw i)
  simpa only [Function.comp_def,restricted,Set.mem_range_self,if_true,Multiset.map_map,
    Finset.prod_coe_sort s (fun i => (1-w i)⁻¹)] using hh

/-- The Euler product for a free commutative monoid, represented as multisets. -/
theorem hasProd (w : ι → ℝ) (hw : ∀ i, ‖w i‖ < 1)
    (hsum : Summable (fun m : Multiset ι => ‖(m.map w).prod‖)) :
    HasProd (fun i => (1-w i)⁻¹) (∑' m : Multiset ι, (m.map w).prod) := by
  have hpoint (m : Multiset ι) : Tendsto (fun s : Finset ι => restricted w s m) atTop
      (𝓝 ((m.map w).prod)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop m.toFinset] with s hs
    have hm : m ∈ Set.range (Multiset.map (Subtype.val : s → ι)) :=
      mem_range_map_subtype s m (fun x hx => hs (Multiset.mem_toFinset.mpr hx))
    simp [restricted,hm]
  have hbound : ∀ᶠ s : Finset ι in atTop, ∀ m : Multiset ι,
      ‖restricted w s m‖ ≤ ‖(m.map w).prod‖ := by
    apply Filter.Eventually.of_forall
    intro s m
    unfold restricted
    split_ifs <;> simp
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  change Tendsto (fun s : Finset ι => ∏ i ∈ s, (1-w i)⁻¹) atTop _
  simpa only [(restricted_hasSum w hw _).tsum_eq] using hlim

end MultisetEuler



/- Nonzero elements of a factorial monoid with trivial units are multisets of primes. -/
namespace PrimeFactorEquiv
open UniqueFactorizationMonoid
open scoped Classical nonZeroDivisors
variable {α : Type*} [CommMonoidWithZero α] [Nontrivial α] [IsCancelMulZero α] [UniqueFactorizationMonoid α]
  [NormalizationMonoid α] [Subsingleton αˣ]

noncomputable def factors (a : α) : Multiset {p : α // Prime p} :=
  (normalizedFactors a).pmap (fun p hp => ⟨p,hp⟩) (fun p hp => prime_of_normalized_factor p hp)

@[simp] theorem map_factors (a : α) : (factors a).map Subtype.val = normalizedFactors a := by
  rw [factors,Multiset.map_pmap,Multiset.pmap_eq_map]
  exact Multiset.map_id _

def prime (p : {p : α // Prime p}) : α⁰ :=
  ⟨p.1,mem_nonZeroDivisors_iff_ne_zero.mpr p.property.ne_zero⟩

noncomputable def prod (m : Multiset {p : α // Prime p}) : α⁰ := (m.map prime).prod

@[simp] theorem coe_prod (m : Multiset {p : α // Prime p}) :
    (prod m : α) = (m.map Subtype.val).prod := by
  induction m using Multiset.induction_on with
  | empty => rfl
  | @cons p m ih =>
    simpa only [prod,Multiset.map_cons,Multiset.prod_cons,Submonoid.coe_mul,prime] using
      congrArg (p.1 * ·) ih

@[simp] theorem prod_factors (a : α⁰) : prod (factors (a : α)) = a := by
  apply Subtype.ext
  rw [coe_prod,map_factors]
  simpa only [associated_eq_eq] using prod_normalizedFactors (nonZeroDivisors.coe_ne_zero a)

@[simp] theorem factors_prod (m : Multiset {p : α // Prime p}) :
    factors (prod m : α) = m := by
  apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
  rw [map_factors,coe_prod]
  apply normalizedFactors_prod_of_prime
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Multiset.mem_map.mp hp
  exact q.property

noncomputable def equiv : α⁰ ≃ Multiset {p : α // Prime p} where
  toFun a := factors (a : α)
  invFun := prod
  left_inv := prod_factors
  right_inv := factors_prod

@[simp] theorem equiv_symm_apply (m : Multiset {p : α // Prime p}) : equiv.symm m = prod m := rfl

@[simp] theorem map_prod {R : Type*} [CommMonoid R] (f : α⁰ →* R)
    (m : Multiset {p : α // Prime p}) : f (prod m) = (m.map (fun p => f (prime p))).prod := by
  rw [prod,← Multiset.prod_hom,Multiset.map_map]
  rfl

end PrimeFactorEquiv

namespace PrimeFactorEquiv
open scoped Classical nonZeroDivisors
variable {α : Type*} [CommMonoidWithZero α] [Nontrivial α] [IsCancelMulZero α]
  [UniqueFactorizationMonoid α] [NormalizationMonoid α] [Subsingleton αˣ]

/-- Euler product over the prime elements of a factorial monoid with trivial units. -/
theorem hasProd (f : α⁰ →* ℝ) (hf : Summable (fun a => ‖f a‖))
    (hp : ∀ p : {p : α // Prime p}, ‖f (prime p)‖ < 1) :
    HasProd (fun p : {p : α // Prime p} => (1-f (prime p))⁻¹) (∑' a, f a) := by
  have hs : Summable (fun m : Multiset {p : α // Prime p} =>
      ‖(m.map (fun p => f (prime p))).prod‖) := by
    have hh := (equiv (α := α)).symm.summable_iff.mpr hf
    simpa only [Function.comp_def,equiv_symm_apply,map_prod] using hh
  have hh := MultisetEuler.hasProd (fun p => f (prime p)) hp hs
  have he : (∑' m : Multiset {p : α // Prime p}, (m.map (fun p => f (prime p))).prod) = ∑' a, f a := by
    simpa only [equiv_symm_apply,map_prod] using (equiv (α := α)).symm.tsum_eq f
  rwa [he] at hh

end PrimeFactorEquiv

namespace IdealClassSeries
set_option maxHeartbeats 2000000
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K : Type*) [Field K] [NumberField K]

noncomputable def weight (χ : ClassGroup (𝓞 K) → ℝ) (s : ℝ) (I : (Ideal (𝓞 K))⁰) : ℝ :=
  χ (ClassGroup.mk0 I) * (absNorm (I : Ideal (𝓞 K)) : ℝ)^(-s)

@[simp] theorem coeff_zero (χ : ClassGroup (𝓞 K) → ℝ) : coeff K χ 0 = 0 :=
  NormCounting.Data.coeff_zero _ _

theorem coeff_weight (χ : ClassGroup (𝓞 K) → ℝ) (s : ℝ) (n : ℕ) :
    (data K).coeff (weight K χ s) n = coeff K χ n * (n : ℝ)^(-s) :=
  (data K).coeff_mul_norm (fun I => χ (ClassGroup.mk0 I)) (fun n => (n : ℝ)^(-s)) n

theorem summable_weight_nonneg (χ : ClassGroup (𝓞 K) → ℝ) (hχ : ∀ c, 0 ≤ χ c)
    (s : ℝ) (hs : 1 < s) : Summable (weight K χ s) := by
  apply ((data K).summable_iff_coeff (weight K χ s) (fun I =>
    mul_nonneg (hχ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))).mpr
  have hh := RealLSeries.summable (coeff K χ) (coeff_zero K χ) s (summable K χ (by simpa using hs))
  change Summable (fun n => (data K).coeff (weight K χ s) n)
  simpa only [coeff_weight] using hh

theorem summable_norm_weight (χ : ClassGroup (𝓞 K) → ℝ) (s : ℝ) (hs : 1 < s) :
    Summable (fun I => ‖weight K χ s I‖) := by
  have hh := summable_weight_nonneg K (fun c => |χ c|) (fun _ => abs_nonneg _) s hs
  simpa only [weight,Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hh

theorem lseries_eq_weight (χ : ClassGroup (𝓞 K) → ℝ) (s : ℝ) (hs : 1 < s) :
    LSeries (fun k => (coeff K χ k : ℂ)) (s : ℂ) = ((∑' I, weight K χ s I : ℝ) : ℂ) := by
  rw [RealLSeries.eq_tsum _ (coeff_zero K χ)]
  congr 1
  have hh := (data K).tsum_coeff (weight K χ s) (summable_norm_weight K χ s hs).of_norm
  simpa only [coeff_weight] using hh

noncomputable def weightHom (χ : ClassGroup (𝓞 K) →* ℝ) (s : ℝ) : (Ideal (𝓞 K))⁰ →* ℝ where
  toFun := weight K χ s
  map_one' := by simp [weight]
  map_mul' I J := by
    simp only [weight,map_mul,Submonoid.coe_mul,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

@[simp] theorem weightHom_apply (χ : ClassGroup (𝓞 K) →* ℝ) (s : ℝ) (I : (Ideal (𝓞 K))⁰) :
    weightHom K χ s I = weight K χ s I := rfl

theorem norm_character (χ : ClassGroup (𝓞 K) →* ℝ) (c : ClassGroup (𝓞 K)) : ‖χ c‖ = 1 :=
  (χ.isOfFinOrder (isOfFinOrder_of_finite c)).norm_eq_one

theorem prime_norm_gt_one (p : {p : Ideal (𝓞 K) // Prime p}) : 1 < absNorm p.1 := by
  have hp : 0 < absNorm p.1 := absNorm_pos_of_nonZeroDivisors (S := 𝓞 K) (PrimeFactorEquiv.prime p)
  have hn : absNorm p.1 ≠ 1 := by
    intro h
    apply p.property.2.1
    rw [absNorm_eq_one_iff.mp h]
    rw [← Ideal.one_eq_top]
    exact isUnit_one
  change 0 < absNorm p.1 at hp
  omega

theorem prime_weight_norm_lt_one (χ : ClassGroup (𝓞 K) →* ℝ) (s : ℝ) (hs : 0 < s)
    (p : {p : Ideal (𝓞 K) // Prime p}) :
    ‖weightHom K χ s (PrimeFactorEquiv.prime p)‖ < 1 := by
  change ‖χ (ClassGroup.mk0 (PrimeFactorEquiv.prime p)) * (absNorm p.1 : ℝ)^(-s)‖ < 1
  rw [norm_mul,norm_character,one_mul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast prime_norm_gt_one K p) (neg_neg_of_pos hs)

/-- Euler product for an ordinary real ideal-class character. -/
theorem euler_hasProd (χ : ClassGroup (𝓞 K) →* ℝ) (s : ℝ) (hs : 1 < s) :
    HasProd (fun p : {p : Ideal (𝓞 K) // Prime p} =>
      (1-weight K χ s (PrimeFactorEquiv.prime p))⁻¹) (∑' I, weight K χ s I) := by
  exact PrimeFactorEquiv.hasProd (weightHom K χ s) (summable_norm_weight K χ s hs)
    (prime_weight_norm_lt_one K χ s (zero_lt_one.trans hs))

end IdealClassSeries

namespace IdealClassSeries
open NumberField Ideal Module Filter Topology Asymptotics
open scoped Classical nonZeroDivisors BigOperators
variable (K : Type*) [Field K] [NumberField K]

/-- The leading summatory constant for arbitrary finite class weights. -/
theorem summatory_tendsto (χ : ClassGroup (𝓞 K) → ℝ) :
    Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, coeff K χ k)/(N : ℝ)) atTop
      (𝓝 (∑ c, χ c*EffectiveIdealClass.mainCoefficient K)) := by
  have hh := tendsto_finset_sum Finset.univ (fun c _ =>
    ((NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K c).comp
      tendsto_natCast_atTop_atTop).const_mul (χ c))
  simpa only [sum_coeff,EffectiveIdealClass.count,EffectiveIdealClass.mainCoefficient,
    Finset.sum_div,mul_div_assoc,Function.comp_apply] using hh

noncomputable def zeta (s : ℝ) : ℝ := ∑' I, weight K (fun _ => 1) s I

noncomputable def residue : ℝ := (Fintype.card (ClassGroup (𝓞 K)) : ℝ)*EffectiveIdealClass.mainCoefficient K

theorem mainCoefficient_pos : 0 < EffectiveIdealClass.mainCoefficient K := by
  have hreg := Units.regulator_pos K
  have htor : (0 : ℝ) < Units.torsionOrder K := Nat.cast_pos.mpr (Units.torsionOrder_pos K)
  have hd : (NumberField.discr K : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
  unfold EffectiveIdealClass.mainCoefficient
  positivity

theorem residue_pos : 0 < residue K := by
  unfold residue
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (mainCoefficient_pos K)

/-- The ordinary Dedekind zeta function has a positive simple-pole residue. -/
theorem zeta_residue : Tendsto (fun s : ℝ => (s-1)*zeta K s)
    (𝓝[Set.Ioi 1] 1) (𝓝 (residue K)) := by
  have hlim := (summatory_tendsto K (fun _ => 1)).ofReal
  have hlim' : Tendsto (fun N : ℕ => (∑ k ∈ Finset.Icc 1 N, (coeff K (fun _ => 1) k : ℂ))/(N : ℂ))
      atTop (𝓝 ((residue K : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast,one_mul,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,residue] using hlim
  have hh := LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div hlim'
    (fun s hs => summable K (fun _ => 1) (by simpa using hs))
  have hr := (Complex.continuous_re.tendsto _).comp hh
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  dsimp only [Function.comp_apply]
  rw [lseries_eq_weight K _ s hs]
  change (((s : ℂ)-1)*((zeta K s : ℝ) : ℂ)).re = _
  simp

end IdealClassSeries



/- Real characters of finite elementary abelian two-groups. -/
namespace ElementaryCharacters
open scoped Classical BigOperators
variable (G : Type*) [CommGroup G] [Fintype G]
variable (hs : ∀ g : G, g^2 = 1)

abbrev Index := AddChar (Additive G) ℂ

include hs in
theorem value_sign (χ : Index G) (g : G) :
    χ (Additive.ofMul g) = 1 ∨ χ (Additive.ofMul g) = -1 := by
  apply mul_self_eq_one_iff.mp
  rw [← χ.map_add_eq_mul]
  have he : Additive.ofMul g + Additive.ofMul g = 0 := by
    change Additive.ofMul (g*g) = Additive.ofMul (1 : G)
    exact congrArg Additive.ofMul (by simpa only [pow_two] using hs g)
  rw [he,χ.map_zero_eq_one]

include hs in
theorem ofReal_re (χ : Index G) (g : G) :
    ((χ (Additive.ofMul g)).re : ℂ) = χ (Additive.ofMul g) := by
  rcases value_sign G hs χ g with h | h <;> simp [h]

noncomputable def realHom (χ : Index G) : G →* ℝ where
  toFun g := (χ (Additive.ofMul g)).re
  map_one' := by change (χ 0).re = 1; simp
  map_mul' g h := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_mul,ofReal_re G hs,ofReal_re G hs,ofReal_re G hs]
    exact χ.map_add_eq_mul _ _

@[simp] theorem realHom_apply (χ : Index G) (g : G) :
    realHom G hs χ g = (χ (Additive.ofMul g)).re := rfl

@[simp] theorem realHom_one (g : G) : realHom G hs 1 g = 1 := by simp

include hs in
theorem realHom_sign (χ : Index G) (g : G) : realHom G hs χ g = 1 ∨ realHom G hs χ g = -1 := by
  rcases value_sign G hs χ g with h | h <;> simp [h]

include hs in
theorem realHom_mul (χ ψ : Index G) (g : G) :
    realHom G hs (χ*ψ) g = realHom G hs χ g * realHom G hs ψ g := by
  apply Complex.ofReal_injective
  simp only [realHom_apply,Complex.ofReal_mul]
  rw [ofReal_re G hs (χ*ψ) g,ofReal_re G hs χ g,ofReal_re G hs ψ g,AddChar.mul_apply]

include hs in
theorem exists_neg {g : G} (hg : g ≠ 1) : ∃ χ : Index G, realHom G hs χ g = -1 := by
  have hg' : Additive.ofMul g ≠ 0 := hg
  obtain ⟨χ,hχ⟩ := AddChar.exists_apply_ne_zero.mpr hg'
  rcases value_sign G hs χ g with h | h
  · exact (hχ h).elim
  · exact ⟨χ,by simp [h]⟩

include hs in
theorem sum_eq_zero {χ : Index G} (hχ : χ ≠ 1) : ∑ g : G, realHom G hs χ g = 0 := by
  have hh := AddChar.sum_eq_zero_of_ne_one hχ
  have he := Additive.ofMul.sum_comp (fun x : Additive G => χ x)
  have hsum : (∑ g : G, χ (Additive.ofMul g)) = 0 := he.trans hh
  have hr := congrArg Complex.re hsum
  change Complex.reAddGroupHom (∑ g : G, χ (Additive.ofMul g)) = 0 at hr
  rw [map_sum] at hr
  exact hr

include hs in
theorem realHom_injective : Function.Injective (realHom G hs) := by
  intro χ ψ h
  ext x
  have hh := congrArg (fun f : G →* ℝ => ((f x.toMul : ℝ) : ℂ)) h
  simpa only [realHom_apply,ofReal_re G hs] using hh

theorem hom_sum_zero {H : Type*} [Group H] [Fintype H] (f : H →* ℝ) (hf : f ≠ 1) :
    ∑ h : H, f h = 0 := by
  obtain ⟨a,ha⟩ : ∃ a, f a ≠ 1 := by
    by_contra! h
    exact hf (DFunLike.ext _ _ h)
  have he := Equiv.sum_comp (Equiv.mulLeft a) (fun h : H => f h)
  change (∑ h : H, f (a*h)) = ∑ h : H, f h at he
  simp only [map_mul,← Finset.mul_sum] at he
  have hz : (f a-1)*(∑ h : H, f h) = 0 := by nlinarith [he]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

include hs in
theorem sum_pullback_zero {H : Type*} [Group H] [Fintype H]
    (q : H →* G) (hq : Function.Surjective q) {χ : Index G} (hχ : χ ≠ 1) :
    ∑ h : H, realHom G hs χ (q h) = 0 := by
  apply hom_sum_zero ((realHom G hs χ).comp q)
  intro hh
  apply hχ
  apply realHom_injective G hs
  ext g
  obtain ⟨h,rfl⟩ := hq g
  have he := DFunLike.congr_fun hh h
  simpa only [MonoidHom.comp_apply,MonoidHom.one_apply,realHom_one] using he

@[simp] theorem card_index : Fintype.card (Index G) = Fintype.card G := by
  rw [AddChar.card_eq]
  exact Fintype.card_congr Additive.toMul

end ElementaryCharacters

namespace ElementaryCharacters
open scoped Classical BigOperators
variable (G : Type*) [CommGroup G] [Fintype G]
variable (hs : ∀ g : G, g^2 = 1)

noncomputable def factorProduct (g : G) (x : ℝ) : ℝ :=
  ∏ χ : Index G, (1-realHom G hs χ g*x)⁻¹

theorem factorProduct_one (x : ℝ) : factorProduct G hs 1 x = ((1-x)⁻¹)^Fintype.card G := by
  simp only [factorProduct,map_one,one_mul,Finset.prod_const,Finset.card_univ,card_index]

theorem factorProduct_pos (g : G) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    0 < factorProduct G hs g x := by
  apply Finset.prod_pos
  intro χ _
  apply inv_pos.mpr
  rcases realHom_sign G hs χ g with h | h
  · rw [h,one_mul]; linarith
  · rw [h,neg_one_mul]; linarith

/-- At a nontrivial element, pairing characters of opposite sign makes the
local Euler product at least one. -/
theorem factorProduct_ge_one {g : G} (hg : g ≠ 1) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    1 ≤ factorProduct G hs g x := by
  obtain ⟨ψ,hψ⟩ := exists_neg G hs hg
  let P := factorProduct G hs g x
  have hflip : (∏ χ : Index G, (1+realHom G hs χ g*x)⁻¹) = P := by
    have hh := Equiv.prod_comp (Equiv.mulRight ψ) (fun χ : Index G => (1-realHom G hs χ g*x)⁻¹)
    change (∏ χ : Index G, (1-realHom G hs (χ*ψ) g*x)⁻¹) = P at hh
    simpa only [realHom_mul,hψ,mul_neg_one,neg_mul,sub_neg_eq_add] using hh
  have hp : P*P = ((1-x^2)⁻¹)^Fintype.card G := by
    change factorProduct G hs g x*P = _
    rw [← hflip,factorProduct,← Finset.prod_mul_distrib]
    have he (χ : Index G) : (1-realHom G hs χ g*x)⁻¹*(1+realHom G hs χ g*x)⁻¹ = (1-x^2)⁻¹ := by
      rw [← mul_inv]
      congr 1
      rcases realHom_sign G hs χ g with h | h <;> rw [h] <;> ring
    simp only [he,Finset.prod_const,Finset.card_univ,card_index]
  have hb0 : 0 < 1-x^2 := by nlinarith
  have hb1 : 1 ≤ (1-x^2)⁻¹ := (one_le_inv₀ hb0).mpr (by nlinarith [sq_nonneg x])
  have hpow : 1 ≤ ((1-x^2)⁻¹)^Fintype.card G := one_le_pow₀ hb1
  have hP : 0 < P := factorProduct_pos G hs g hx0 hx
  rw [← hp] at hpow
  nlinarith

/-- Finite Euler-product comparison for an exponent-two quotient. -/
theorem finite_product_bound {P : Type*} (g : P → G) (x : P → ℝ)
    (s : Finset P) (hx0 : ∀ p ∈ s, 0 ≤ x p) (hx : ∀ p ∈ s, x p < 1) :
    (∏ p ∈ s, if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G ≤
      ∏ χ : Index G, ∏ p ∈ s, (1-realHom G hs χ (g p)*x p)⁻¹ := by
  rw [← Finset.prod_pow,Finset.prod_comm]
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs
    · exact pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (hx p hp).le)) _
    · positivity
  · intro p hp
    change (if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G ≤ factorProduct G hs (g p) (x p)
    by_cases hg : g p = 1
    · rw [if_pos hg,hg,factorProduct_one]
    · rw [if_neg hg,one_pow]
      exact factorProduct_ge_one G hs hg (hx0 p hp) (hx p hp)

end ElementaryCharacters

namespace KernelEuler
open Filter Topology
open scoped Classical BigOperators
variable {P : Type*}

theorem norm_prod_mono (w x : P → ℝ) (h : ∀ p, ‖w p‖ ≤ ‖x p‖) (m : Multiset P) :
    ‖(m.map w).prod‖ ≤ ‖(m.map x).prod‖ := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons p m ih =>
    simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
    exact mul_le_mul (h p) ih (norm_nonneg _) (norm_nonneg _)

variable (G : Type*) [CommGroup G] [Fintype G] (hs : ∀ g : G, g^2 = 1)

noncomputable def value (g : P → G) (x : P → ℝ) (p : P) : ℝ := if g p = 1 then x p else (x p)^2

theorem value_bounds (g : P → G) (x : P → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx : ∀ p, x p < 1) (p : P) :
    0 ≤ value G g x p ∧ value G g x p ≤ x p := by
  unfold value
  split_ifs
  · exact ⟨hx0 p,le_rfl⟩
  · constructor
    · positivity
    · nlinarith [hx0 p,hx p]

/-- The degree-one versus degree-at-least-two prime kernel has a convergent Euler product. -/
theorem exists_hasProd (g : P → G) (x : P → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx : ∀ p, x p < 1)
    (hsum : Summable (fun m : Multiset P => ‖(m.map x).prod‖)) :
    ∃ a : ℝ, 1 ≤ a ∧ HasProd (fun p => (1-value G g x p)⁻¹) a := by
  have hw0 (p : P) := (value_bounds G g x hx0 hx p).1
  have hw (p : P) : value G g x p < 1 := (value_bounds G g x hx0 hx p).2.trans_lt (hx p)
  have hnorm (p : P) : ‖value G g x p‖ ≤ ‖x p‖ := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hw0 p),abs_of_nonneg (hx0 p)] using
      (value_bounds G g x hx0 hx p).2
  have hsumw : Summable (fun m : Multiset P => ‖(m.map (value G g x)).prod‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_prod_mono _ _ hnorm) hsum
  have hp := MultisetEuler.hasProd (value G g x)
    (fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hw0 p)] using hw p) hsumw
  refine ⟨_,?_,hp⟩
  apply ge_of_tendsto hp
  apply Filter.Eventually.of_forall
  intro s
  apply Finset.one_le_prod
  intro p
  apply (one_le_inv₀ (sub_pos.mpr (hw p))).mpr
  linarith [hw0 p]

/-- The kernel product is controlled by norm-squared Euler factors and all
characters of the finite elementary quotient. -/
theorem character_bound (g : P → G) (x : P → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx : ∀ p, x p < 1)
    (a z : ℝ) (L : ElementaryCharacters.Index G → ℝ)
    (ha : HasProd (fun p => (1-value G g x p)⁻¹) a)
    (hz : HasProd (fun p => (1-(x p)^2)⁻¹) z)
    (hL : ∀ χ, HasProd (fun p => (1-ElementaryCharacters.realHom G hs χ (g p)*x p)⁻¹) (L χ)) :
    a^Fintype.card G ≤ z^Fintype.card G * ∏ χ, L χ := by
  have hr := (hz.pow (Fintype.card G)).mul (tendsto_finset_prod Finset.univ (fun χ _ => hL χ))
  apply le_of_tendsto_of_tendsto (ha.pow (Fintype.card G)) hr
  apply Filter.Eventually.of_forall
  intro s
  have hsq0 (p : P) : 0 < 1-(x p)^2 := by nlinarith [hx0 p,hx p]
  have hsq1 (p : P) : 1 ≤ (1-(x p)^2)⁻¹ := (one_le_inv₀ (hsq0 p)).mpr (by nlinarith [sq_nonneg (x p)])
  have hsplit0 (p : P) : 0 ≤ (if g p = 1 then (1-x p)⁻¹ else 1) := by
    split_ifs
    · exact (inv_pos.mpr (sub_pos.mpr (hx p))).le
    · norm_num
  have hker (p : P) : (1-value G g x p)⁻¹ ≤
      (1-(x p)^2)⁻¹*(if g p = 1 then (1-x p)⁻¹ else 1) := by
    unfold value
    split_ifs with h
    · exact le_mul_of_one_le_left (inv_nonneg.mpr (sub_nonneg.mpr (hx p).le)) (hsq1 p)
    · simp
  have hfinite := ElementaryCharacters.finite_product_bound G hs g x s (fun p _ => hx0 p) (fun p _ => hx p)
  have hk0 : 0 ≤ ∏ p ∈ s, (1-value G g x p)⁻¹ := by
    apply Finset.prod_nonneg
    intro p _
    exact (inv_pos.mpr (sub_pos.mpr ((value_bounds G g x hx0 hx p).2.trans_lt (hx p)))).le
  calc
    _ ≤ (∏ p ∈ s, (1-(x p)^2)⁻¹*(if g p = 1 then (1-x p)⁻¹ else 1))^Fintype.card G := by
      apply pow_le_pow_left₀ hk0
      exact Finset.prod_le_prod (fun p _ => (inv_pos.mpr
        (sub_pos.mpr ((value_bounds G g x hx0 hx p).2.trans_lt (hx p)))).le) (fun p _ => hker p)
    _ = (∏ p ∈ s, (1-(x p)^2)⁻¹)^Fintype.card G *
        (∏ p ∈ s, if g p = 1 then (1-x p)⁻¹ else 1)^Fintype.card G := by
      rw [Finset.prod_mul_distrib,mul_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hfinite (pow_nonneg
      (Finset.prod_nonneg (fun p _ => (inv_pos.mpr (hsq0 p)).le)) _)

end KernelEuler



/- Comparisons of positive Euler products with bounded prime fibers. -/
namespace OrderedEuler
open Filter Topology
open scoped Classical BigOperators

variable {P Q : Type*}

theorem finite_prod_le_limit (A : P → ℝ) (hA : ∀ p, 1 ≤ A p) (a : ℝ)
    (ha : HasProd A a) (s : Finset P) : ∏ p ∈ s, A p ≤ a := by
  apply ge_of_tendsto ha
  filter_upwards [eventually_ge_atTop s] with t ht
  rw [← Finset.prod_sdiff ht]
  have hs := Finset.one_le_prod s hA
  have hdiff := Finset.one_le_prod (t \ s) hA
  nlinarith

/-- Bounded fibers of a map on primes turn pointwise domination into an
Euler-product power bound. -/
theorem fiber_bound (g : P → Q) (A : Q → ℝ) (B : P → ℝ) (d : ℕ)
    (hA : ∀ q, 1 ≤ A q) (hB : ∀ p, 0 ≤ B p) (hBA : ∀ p, B p ≤ A (g p))
    (hfib : ∀ s : Finset P, ∀ q : Q, (s.filter (fun p => g p = q)).card ≤ d)
    (a b : ℝ) (ha : HasProd A a) (hb : HasProd B b) : b ≤ a^d := by
  apply le_of_tendsto' hb
  intro s
  have hmid : (∏ p ∈ s, A (g p)) = ∏ q ∈ s.image g, A q ^ (s.filter (fun p => g p = q)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := s) (t := s.image g) (g := g) (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) (fun p => A (g p))]
    apply Finset.prod_congr rfl
    intro q hq
    calc
      _ = ∏ p ∈ s.filter (fun p => g p = q), A q :=
        Finset.prod_congr rfl (fun p hp => congrArg A (Finset.mem_filter.mp hp).2)
      _ = _ := Finset.prod_const _
  calc
    _ ≤ ∏ p ∈ s, A (g p) := Finset.prod_le_prod (fun p _ => hB p) (fun p _ => hBA p)
    _ = ∏ q ∈ s.image g, A q ^ (s.filter (fun p => g p = q)).card := hmid
    _ ≤ ∏ q ∈ s.image g, A q^d := Finset.prod_le_prod
      (fun q _ => pow_nonneg (zero_le_one.trans (hA q)) _)
      (fun q _ => pow_le_pow_right₀ (hA q) (hfib s q))
    _ = (∏ q ∈ s.image g, A q)^d := Finset.prod_pow _ _ _
    _ ≤ a^d := pow_le_pow_left₀ (Finset.prod_nonneg (fun q _ => zero_le_one.trans (hA q)))
      (finite_prod_le_limit A hA a ha _ ) _

end OrderedEuler



/- Norms and bounded fibers for the map of prime ideals in a number-field extension. -/

namespace IdealNormKernel
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

noncomputable def primeWeight (F : Type*) [Field F] [NumberField F] (s : ℝ) (p : IdealPrimeMap.Primes F) : ℝ :=
  (absNorm p.1 : ℝ)^(-s)

theorem primeWeight_bounds (F : Type*) [Field F] [NumberField F] (s : ℝ) (hs : 0 < s)
    (p : IdealPrimeMap.Primes F) : 0 ≤ primeWeight F s p ∧ primeWeight F s p < 1 := by
  refine ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast IdealClassSeries.prime_norm_gt_one F p)
    (neg_neg_of_pos hs)

theorem zeta_hasProd (F : Type*) [Field F] [NumberField F] (s : ℝ) (hs : 1 < s) :
    HasProd (fun p : IdealPrimeMap.Primes F => (1-primeWeight F s p)⁻¹) (IdealClassSeries.zeta F s) := by
  simpa only [IdealClassSeries.weight,MonoidHom.one_apply,one_mul,primeWeight,IdealClassSeries.zeta,
    PrimeFactorEquiv.prime] using IdealClassSeries.euler_hasProd F 1 s hs

theorem summable_multiset (F : Type*) [Field F] [NumberField F] (s : ℝ) (hs : 1 < s) :
    Summable (fun m : Multiset (IdealPrimeMap.Primes F) => ‖(m.map (primeWeight F s)).prod‖) := by
  have hh := (PrimeFactorEquiv.equiv (α := Ideal (𝓞 F))).symm.summable_iff.mpr
    (IdealClassSeries.summable_norm_weight F (fun _ => 1) s hs)
  have he (m : Multiset (IdealPrimeMap.Primes F)) :
      IdealClassSeries.weight F (fun _ => 1) s (PrimeFactorEquiv.prod m) = (m.map (primeWeight F s)).prod := by
    simpa only [IdealClassSeries.weightHom_apply,IdealClassSeries.weight,MonoidHom.one_apply,one_mul,
      primeWeight,PrimeFactorEquiv.prime] using PrimeFactorEquiv.map_prod (IdealClassSeries.weightHom F 1 s) m
  simpa only [Function.comp_def,PrimeFactorEquiv.equiv_symm_apply,he] using hh

theorem norm_prime (P : IdealPrimeMap.Primes E) :
    IdealPrimeMap.norm K E (PrimeFactorEquiv.prime P) =
      (PrimeFactorEquiv.prime (IdealPrimeMap.below K E P))^IdealPrimeMap.degree K E P := by
  apply Subtype.ext
  exact IdealPrimeMap.relNorm_prime K E P

theorem primeWeight_extension (s : ℝ) (P : IdealPrimeMap.Primes E) :
    primeWeight E s P = (primeWeight K s (IdealPrimeMap.below K E P))^IdealPrimeMap.degree K E P := by
  unfold primeWeight
  rw [IdealPrimeMap.absNorm_prime K E P,Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg _) _ _,
    mul_comm (IdealPrimeMap.degree K E P : ℝ),Real.rpow_mul_natCast (Nat.cast_nonneg _) _ _]

variable {G : Type*} [CommGroup G] [Fintype G]
variable (q : ClassGroup (𝓞 K) →* G)
variable (hkill : ∀ I : (Ideal (𝓞 E))⁰, q (ClassGroup.mk0 (IdealPrimeMap.norm K E I)) = 1)

noncomputable def label (p : IdealPrimeMap.Primes K) : G := q (ClassGroup.mk0 (PrimeFactorEquiv.prime p))

include hkill in
theorem degree_ge_two (P : IdealPrimeMap.Primes E) (hP : label K q (IdealPrimeMap.below K E P) ≠ 1) :
    2 ≤ IdealPrimeMap.degree K E P := by
  have hpos := IdealPrimeMap.degree_pos K E P
  have hh := hkill (PrimeFactorEquiv.prime P)
  rw [norm_prime,map_pow,map_pow] at hh
  by_contra h
  have hd : IdealPrimeMap.degree K E P = 1 := by omega
  rw [hd,pow_one] at hh
  exact hP hh

include hkill in
theorem weight_le_kernel (s : ℝ) (hs : 0 < s) (P : IdealPrimeMap.Primes E) :
    primeWeight E s P ≤ KernelEuler.value G (label K q) (primeWeight K s) (IdealPrimeMap.below K E P) := by
  rw [primeWeight_extension K E]
  have hb := primeWeight_bounds K s hs (IdealPrimeMap.below K E P)
  unfold KernelEuler.value
  split_ifs with h
  · exact pow_le_of_le_one hb.1 hb.2.le (IdealPrimeMap.degree_pos K E P).ne'
  · exact pow_le_pow_of_le_one hb.1 hb.2.le (degree_ge_two K E q hkill P h)

include hkill in
/-- The upstairs zeta function is dominated by the kernel Euler product to
at most the field-extension degree. -/
theorem exists_kernel_bound (s : ℝ) (hs : 1 < s) :
    ∃ a : ℝ, 1 ≤ a ∧
      HasProd (fun p => (1-KernelEuler.value G (label K q) (primeWeight K s) p)⁻¹) a ∧
      IdealClassSeries.zeta E s ≤ a^Module.finrank K E := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hx0 := fun p => (primeWeight_bounds K s hs0 p).1
  have hx := fun p => (primeWeight_bounds K s hs0 p).2
  obtain ⟨a,ha0,ha⟩ := KernelEuler.exists_hasProd G (label K q) (primeWeight K s) hx0 hx
    (summable_multiset K s hs)
  refine ⟨a,ha0,ha,?_⟩
  have hk (p : IdealPrimeMap.Primes K) : KernelEuler.value G (label K q) (primeWeight K s) p < 1 :=
    (KernelEuler.value_bounds G (label K q) (primeWeight K s) hx0 hx p).2.trans_lt (hx p)
  apply OrderedEuler.fiber_bound (IdealPrimeMap.below K E)
    (fun p => (1-KernelEuler.value G (label K q) (primeWeight K s) p)⁻¹)
    (fun P => (1-primeWeight E s P)⁻¹) (Module.finrank K E) ?_ ?_ ?_
    (fun t p => by
      convert IdealPrimeMap.card_fiber_le K E t p using 1
      congr 1
      ext P
      simp only [Finset.mem_filter]) a _ ha (zeta_hasProd E s hs)
  · intro p
    apply (one_le_inv₀ (sub_pos.mpr (hk p))).mpr
    linarith [(KernelEuler.value_bounds G (label K q) (primeWeight K s) hx0 hx p).1]
  · intro P
    exact (inv_pos.mpr (sub_pos.mpr (primeWeight_bounds E s hs0 P).2)).le
  · intro P
    apply (inv_le_inv₀ (sub_pos.mpr (primeWeight_bounds E s hs0 P).2) (sub_pos.mpr (hk _))).mpr
    exact sub_le_sub_left (weight_le_kernel K E q hkill s hs0 P) 1

end IdealNormKernel

namespace NormIndexAnalysis
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable (G : Type*) [CommGroup G] [Fintype G] (hsq : ∀ g : G, g^2 = 1)
variable (q : ClassGroup (𝓞 K) →* G)

noncomputable def pullback (χ : ElementaryCharacters.Index G) : ClassGroup (𝓞 K) →* ℝ :=
  (ElementaryCharacters.realHom G hsq χ).comp q

noncomputable def series (χ : ElementaryCharacters.Index G) (s : ℝ) : ℝ :=
  ∑' I, IdealClassSeries.weight K (pullback K G hsq q χ) s I

@[simp] theorem series_one (s : ℝ) : series K G hsq q 1 s = IdealClassSeries.zeta K s := by
  simp only [series,IdealClassSeries.zeta,IdealClassSeries.weight,pullback,MonoidHom.comp_apply,
    ElementaryCharacters.realHom_one,one_mul]

theorem zeta_nonneg (F : Type*) [Field F] [NumberField F] (s : ℝ) : 0 ≤ IdealClassSeries.zeta F s := by
  apply tsum_nonneg
  intro I
  exact mul_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem zeta_antitone (F : Type*) [Field F] [NumberField F] {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    IdealClassSeries.zeta F t ≤ IdealClassSeries.zeta F s := by
  apply Summable.tsum_le_tsum _ (IdealClassSeries.summable_norm_weight F (fun _ => 1) t (hs.trans_le hst)).of_norm
    (IdealClassSeries.summable_norm_weight F (fun _ => 1) s hs).of_norm
  intro I
  simp only [IdealClassSeries.weight,one_mul]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors I)
  · linarith

theorem primeWeight_square (s : ℝ) (p : IdealPrimeMap.Primes K) :
    IdealNormKernel.primeWeight K (2*s) p = (IdealNormKernel.primeWeight K s p)^2 := by
  unfold IdealNormKernel.primeWeight
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) _ 2]
  congr 1
  norm_num
  ring

/-- The kernel Euler-product estimate specialized to norm-class characters. -/
theorem kernel_character_bound (s : ℝ) (hs : 1 < s) (a : ℝ)
    (ha : HasProd (fun p =>
      (1-KernelEuler.value G (IdealNormKernel.label K q) (IdealNormKernel.primeWeight K s) p)⁻¹) a) :
    a^Fintype.card G ≤ (IdealClassSeries.zeta K (2*s))^Fintype.card G *
      ∏ χ, series K G hsq q χ s := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  apply KernelEuler.character_bound G hsq (IdealNormKernel.label K q) (IdealNormKernel.primeWeight K s)
    (fun p => (IdealNormKernel.primeWeight_bounds K s hs0 p).1)
    (fun p => (IdealNormKernel.primeWeight_bounds K s hs0 p).2) a _ _ ha
  · simpa only [primeWeight_square] using IdealNormKernel.zeta_hasProd K (2*s) (by linarith)
  · intro χ
    simpa only [IdealClassSeries.weight,pullback,MonoidHom.comp_apply,IdealNormKernel.label,
      IdealNormKernel.primeWeight,series] using
      IdealClassSeries.euler_hasProd K (pullback K G hsq q χ) s hs

variable (hq : Function.Surjective q)

include hq in
/-- Every nontrivial pulled-back character is bounded near the simple pole. -/
theorem nontrivial_bounded [IsTotallyReal K] (n : ℕ) (hd : finrank ℚ K = n+1)
    (χ : ElementaryCharacters.Index G) (hχ : χ ≠ 1) :
    ∃ B > (0 : ℝ), ∀ s : ℝ, 1 < s → s ≤ 2 → |series K G hsq q χ s| ≤ B := by
  have hz : ∑ c, pullback K G hsq q χ c = 0 :=
    ElementaryCharacters.sum_pullback_zero G hsq q hq hχ
  obtain ⟨B,hB,h⟩ := IdealClassSeries.bounded_near_one K n hd (pullback K G hsq q χ) hz
  refine ⟨B,hB,?_⟩
  intro s hs hs2
  have hh := h s hs hs2
  rw [IdealClassSeries.lseries_eq_weight K _ s hs,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

include hq in
/-- The product of all quotient-character series has at most one simple pole. -/
theorem product_bound [IsTotallyReal K] (n : ℕ) (hd : finrank ℚ K = n+1) :
    ∃ C > (0 : ℝ), ∀ s : ℝ, 1 < s → s ≤ 2 →
      (∏ χ : ElementaryCharacters.Index G, series K G hsq q χ s) ≤ C*IdealClassSeries.zeta K s := by
  have h : ∀ χ : ElementaryCharacters.Index G, ∃ B > (0 : ℝ),
      χ ≠ 1 → ∀ s : ℝ, 1 < s → s ≤ 2 → |series K G hsq q χ s| ≤ B := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨1,zero_lt_one,fun h => (h hχ).elim⟩
    · obtain ⟨B,hB,h⟩ := nontrivial_bounded K G hsq q hq n hd χ hχ
      exact ⟨B,hB,fun _ => h⟩
  choose B hB hbound using h
  let S : Finset (ElementaryCharacters.Index G) := Finset.univ.erase 1
  let C : ℝ := ∏ χ ∈ S, B χ
  have hC : 0 < C := Finset.prod_pos (fun χ _ => hB χ)
  refine ⟨C,hC,?_⟩
  intro s hs hs2
  have hrest : (∏ χ ∈ S, series K G hsq q χ s) ≤ C := by
    calc
      _ ≤ |∏ χ ∈ S, series K G hsq q χ s| := le_abs_self _
      _ = ∏ χ ∈ S, |series K G hsq q χ s| := Finset.abs_prod _ _
      _ ≤ C := Finset.prod_le_prod (fun χ _ => abs_nonneg _) (fun χ hχ =>
        hbound χ (Finset.mem_erase.mp hχ).1 s hs hs2)
  have he : (∏ χ : ElementaryCharacters.Index G, series K G hsq q χ s) =
      IdealClassSeries.zeta K s * (∏ χ ∈ S, series K G hsq q χ s) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : ElementaryCharacters.Index G)),series_one]
  rw [he]
  calc
    _ ≤ IdealClassSeries.zeta K s*C := mul_le_mul_of_nonneg_left hrest (zeta_nonneg K s)
    _ = _ := mul_comm _ _

end NormIndexAnalysis



/- Comparing pole orders using only real limits. -/
namespace PoleOrderComparison
open Filter Topology

/-- If two functions have finite simple-pole residues, the first positive,
a power comparison forces the corresponding degree inequality. -/
theorem degree_le {α : Type*} (l : Filter α) [l.NeBot]
    (u a b : α → ℝ) (A B C : ℝ) (hA : 0 < A)
    (hu : Tendsto u l (𝓝 0)) (ha : Tendsto (fun x => u x*a x) l (𝓝 A))
    (hb : Tendsto (fun x => u x*b x) l (𝓝 B))
    (hu0 : ∀ᶠ x in l, 0 ≤ u x) (m d : ℕ)
    (h : ∀ᶠ x in l, a x^m ≤ C*b x^d) : m ≤ d := by
  by_contra hmd
  have hdm : d < m := by omega
  have hsub : 0 < m-d := Nat.sub_pos_of_lt hdm
  have hright : Tendsto (fun x => C*(u x*b x)^d*u x^(m-d)) l (𝓝 0) := by
    have hh := ((hb.pow d).const_mul C).mul (hu.pow (m-d))
    simpa only [zero_pow hsub.ne',mul_zero] using hh
  have hbound : ∀ᶠ x in l, (u x*a x)^m ≤ C*(u x*b x)^d*u x^(m-d) := by
    filter_upwards [hu0,h] with x hx hh
    calc
      _ = u x^m*a x^m := mul_pow _ _ _
      _ ≤ u x^m*(C*b x^d) := mul_le_mul_of_nonneg_left hh (pow_nonneg hx _)
      _ = C*(u x*b x)^d*u x^(m-d) := by
        rw [mul_pow]
        have he : u x^m = u x^d*u x^(m-d) := by rw [← pow_add,Nat.add_sub_of_le hdm.le]
        rw [he]
        ring
  have hle := le_of_tendsto_of_tendsto (ha.pow m) hright hbound
  exact (not_le_of_gt (pow_pos hA m)) hle

end PoleOrderComparison

namespace NormIndexAnalysis
open NumberField Ideal Module Filter Topology
open scoped Classical nonZeroDivisors BigOperators
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [IsTotallyReal K]
variable (G : Type*) [CommGroup G] [Fintype G] (hsq : ∀ g : G, g^2 = 1)
variable (q : ClassGroup (𝓞 K) →* G) (hq : Function.Surjective q)
variable (hkill : ∀ I : (Ideal (𝓞 E))⁰, q (ClassGroup.mk0 (IdealPrimeMap.norm K E I)) = 1)

include hsq hq hkill in
/-- An elementary two-quotient of the ordinary ideal class group which
kills all norms has order no larger than the field-extension degree. -/
theorem card_le_degree : Fintype.card G ≤ Module.finrank K E := by
  have hdpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  let n := Module.finrank ℚ K-1
  have hd : Module.finrank ℚ K = n+1 := by dsimp [n]; omega
  obtain ⟨C,hC,hprod⟩ := product_bound K G hsq q hq n hd
  let m := Fintype.card G
  let d := Module.finrank K E
  let T := ((IdealClassSeries.zeta K 2)^m*C)^d
  have hmain (s : ℝ) (hs : 1 < s) (hs2 : s ≤ 2) :
      (IdealClassSeries.zeta E s)^m ≤ T*(IdealClassSeries.zeta K s)^d := by
    obtain ⟨a,ha0,ha,hE⟩ := IdealNormKernel.exists_kernel_bound K E q hkill s hs
    have hchar := kernel_character_bound K G hsq q s hs a ha
    have hsqb : (IdealClassSeries.zeta K (2*s))^m ≤ (IdealClassSeries.zeta K 2)^m :=
      pow_le_pow_left₀ (zeta_nonneg K (2*s)) (zeta_antitone K (by norm_num) (by linarith)) _
    have hA : a^m ≤ ((IdealClassSeries.zeta K 2)^m*C)*IdealClassSeries.zeta K s := by
      calc
        _ ≤ (IdealClassSeries.zeta K (2*s))^m * ∏ χ, series K G hsq q χ s := hchar
        _ ≤ (IdealClassSeries.zeta K (2*s))^m * (C*IdealClassSeries.zeta K s) :=
          mul_le_mul_of_nonneg_left (hprod s hs hs2) (pow_nonneg (zeta_nonneg K _) _)
        _ ≤ (IdealClassSeries.zeta K 2)^m * (C*IdealClassSeries.zeta K s) :=
          mul_le_mul_of_nonneg_right hsqb (mul_nonneg hC.le (zeta_nonneg K s))
        _ = _ := by ring
    calc
      _ ≤ (a^d)^m := pow_le_pow_left₀ (zeta_nonneg E s) hE _
      _ = (a^m)^d := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ (((IdealClassSeries.zeta K 2)^m*C)*IdealClassSeries.zeta K s)^d :=
        pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans ha0) _) hA _
      _ = _ := by rw [mul_pow]
  have hu : Tendsto (fun s : ℝ => s-1) (𝓝[Set.Ioi 1] 1) (𝓝 0) := by
    have hh : Tendsto (fun s : ℝ => s) (𝓝[Set.Ioi 1] 1) (𝓝 1) :=
      tendsto_id'.mpr nhdsWithin_le_nhds
    simpa using hh.sub_const 1
  apply PoleOrderComparison.degree_le (𝓝[Set.Ioi 1] (1 : ℝ)) (fun s => s-1)
    (IdealClassSeries.zeta E) (IdealClassSeries.zeta K) (IdealClassSeries.residue E)
    (IdealClassSeries.residue K) T (IdealClassSeries.residue_pos E) hu
    (IdealClassSeries.zeta_residue E) (IdealClassSeries.zeta_residue K) ?_ m d ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_nonneg.mpr (Set.mem_Ioi.mp hs).le
  · have htwo : ∀ᶠ s : ℝ in 𝓝[Set.Ioi 1] 1, s < 2 :=
      (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,htwo] with s hs hs2
    exact hmain s hs hs2.le

end NormIndexAnalysis

namespace NormClassQuotient
open NumberField Ideal Module
open scoped Classical nonZeroDivisors
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

noncomputable def subgroup : Subgroup (ClassGroup (𝓞 K)) :=
  Subgroup.closure (Set.range (ClassGroup.mk0.comp (IdealPrimeMap.norm K E)))

abbrev quotient := ClassGroup (𝓞 K) ⧸ subgroup K E

noncomputable def map : ClassGroup (𝓞 K) →* quotient K E := QuotientGroup.mk' (subgroup K E)

theorem map_surjective : Function.Surjective (map K E) := QuotientGroup.mk'_surjective _

theorem map_norm (I : (Ideal (𝓞 E))⁰) : map K E (ClassGroup.mk0 (IdealPrimeMap.norm K E I)) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_closure (Set.mem_range_self I)

noncomputable def extend (I : (Ideal (𝓞 K))⁰) : (Ideal (𝓞 E))⁰ :=
  ⟨Ideal.map (algebraMap (𝓞 K) (𝓞 E)) I.1,
    mem_nonZeroDivisors_iff_ne_zero.mpr (Ideal.map_ne_bot_of_ne_bot (nonZeroDivisors.coe_ne_zero I))⟩

theorem norm_extend (I : (Ideal (𝓞 K))⁰) :
    IdealPrimeMap.norm K E (extend K E I) = I ^ Module.finrank K E := by
  letI := FractionRing.liftAlgebra (𝓞 K) (FractionRing (𝓞 E))
  apply Subtype.ext
  change Ideal.relNorm (𝓞 K) (Ideal.map (algebraMap (𝓞 K) (𝓞 E)) I.1) = I.1 ^ Module.finrank K E
  rw [Ideal.relNorm_algebraMap]
  congr 1
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) (FractionRing (𝓞 K)) (𝓞 E) (FractionRing (𝓞 E)),
    Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 E) E]

/-- The ordinary norm-class quotient is annihilated by the relative degree. -/
theorem pow_degree (g : quotient K E) : g ^ Module.finrank K E = 1 := by
  obtain ⟨c,rfl⟩ := map_surjective K E g
  obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective c
  have hh := map_norm K E (extend K E I)
  rwa [norm_extend,map_pow,map_pow] at hh

/-- For a quadratic extension of a totally real field, the ordinary
ideal-class norm quotient has order at most two. -/
theorem card_le_two [IsTotallyReal K] (hd : Module.finrank K E = 2) :
    Fintype.card (quotient K E) ≤ 2 := by
  have hsq (g : quotient K E) : g^2 = 1 := by simpa only [hd] using pow_degree K E g
  have hh := NormIndexAnalysis.card_le_degree K E (quotient K E) hsq (map K E)
    (map_surjective K E) (map_norm K E)
  rwa [hd] at hh

end NormClassQuotient

namespace UnramifiedNormIndex
open NumberField PrincipalInvolutionSequences
open scoped Classical nonZeroDivisors

variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

/-- The subgroup used by the analytic norm-index theorem is exactly the
image of the relative norm on ideal classes. -/
theorem subgroup_eq_range : NormClassQuotient.subgroup K E = (NormClassHom.norm K E).range := by
  have he : Set.range (ClassGroup.mk0.comp (IdealPrimeMap.norm K E)) =
      ((NormClassHom.norm K E).range : Set (ClassGroup (𝓞 K))) := by
    ext c
    constructor
    · rintro ⟨I,rfl⟩
      exact ⟨ClassGroup.mk0 I,NormClassHom.norm_mk0 K E I⟩
    · rintro ⟨c,rfl⟩
      obtain ⟨I,rfl⟩ := ClassGroup.mk0_surjective c
      exact ⟨I,(NormClassHom.norm_mk0 K E I).symm⟩
  rw [NormClassQuotient.subgroup,he,Subgroup.closure_eq]

end UnramifiedNormIndex

namespace UnramifiedNormIndex
open NumberField PrincipalInvolutionSequences
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

noncomputable def rangeEquiv : (ClassNormInvariance.normLinear K E).range ≃ (NormClassHom.norm K E).range :=
  (Additive.toMul.trans (FractionalClasses.equiv K).toEquiv).subtypeEquiv (fun y => by
    constructor
    · rintro ⟨x,rfl⟩
      refine ⟨FractionalClasses.equiv E x.toMul,?_⟩
      change NormClassHom.norm K E (FractionalClasses.equiv E x.toMul) =
        FractionalClasses.equiv K ((FractionalClasses.equiv K).symm
          (NormClassHom.norm K E (FractionalClasses.equiv E x.toMul)))
      rw [MulEquiv.apply_symm_apply]
    · rintro ⟨c,hc⟩
      refine ⟨Additive.ofMul ((FractionalClasses.equiv E).symm c),?_⟩
      apply Additive.toMul.injective
      apply (FractionalClasses.equiv K).injective
      change FractionalClasses.equiv K ((FractionalClasses.equiv K).symm
        (NormClassHom.norm K E (FractionalClasses.equiv E ((FractionalClasses.equiv E).symm c)))) = _
      rw [MulEquiv.apply_symm_apply,MulEquiv.apply_symm_apply]
      exact hc)

variable (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)

include hdeg hne hunram in
/-- The algebraic first inequality for the ordinary class-norm quotient
in an unramified totally real quadratic extension. -/
theorem two_le_card [IsTotallyReal K] [IsTotallyReal E] :
    2 ≤ Nat.card (NormClassQuotient.quotient K E) := by
  have h₁ := ClassNormInvariance.range_card_le_fixed K E σ
  have h₂ := UnramifiedAmbiguousClasses.twice_fixedClasses_le K E σ hdeg hne hunram
  have h : 2*Nat.card (NormClassHom.norm K E).range ≤ Nat.card (ClassGroup (𝓞 K)) := by
    rw [← Nat.card_congr (rangeEquiv K E)]
    exact (Nat.mul_le_mul_left 2 h₁).trans h₂
  have hm : Nat.card (NormClassHom.norm K E).range * Nat.card (NormClassQuotient.quotient K E) =
      Nat.card (ClassGroup (𝓞 K)) := by
    change Nat.card (NormClassHom.norm K E).range * Nat.card
      (ClassGroup (𝓞 K) ⧸ NormClassQuotient.subgroup K E) = _
    rw [subgroup_eq_range]
    exact (NormClassHom.norm K E).range.card_mul_index
  rw [← hm,mul_comm 2] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

include hdeg hne hunram in
/-- Combining the analytic second inequality with the algebraic first
inequality gives the exact ordinary unramified quadratic norm index. -/
theorem card_eq_two [IsTotallyReal K] [IsTotallyReal E] :
    Nat.card (NormClassQuotient.quotient K E) = 2 := by
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card]
    exact NormClassQuotient.card_le_two K E hdeg
  · exact two_le_card K E σ hdeg hne hunram

end UnramifiedNormIndex

namespace FiniteEndomorphism
open scoped Classical
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Finite A] [Finite B]

/-- Equality in the coinvariant image bound identifies the entire kernel. -/
theorem ker_eq_difference (σ : A →ₗ[ℤ] A) (f : A →ₗ[ℤ] B)
    (hf : ∀ x, f (σ x) = f x)
    (hc : Nat.card f.range = Nat.card (InvolutionHerbrand.plus σ)) :
    f.ker = (σ-LinearMap.id).range := by
  have hle : (σ-LinearMap.id).range ≤ f.ker := by
    rintro _ ⟨x,rfl⟩
    change f (σ x-x) = 0
    rw [map_sub,hf,sub_self]
  have h₁ := f.ker.card_eq_card_quotient_mul_card
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv,hc] at h₁
  have h₂ := (σ-LinearMap.id).range.card_eq_card_quotient_mul_card
  rw [card_coker_eq_ker] at h₂
  have he : Nat.card f.ker = Nat.card (σ-LinearMap.id).range :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h₁.symm.trans h₂)
  apply le_antisymm _ hle
  have hs : ((σ-LinearMap.id).range : Set A) = (f.ker : Set A) :=
    Set.eq_of_subset_of_ncard_le hle (by exact he.le)
  exact le_of_eq (SetLike.coe_injective hs.symm)

end FiniteEndomorphism

namespace UnramifiedNormIndex
open NumberField PrincipalInvolutionSequences InvolutionHerbrand InvolutionSequence
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) [IsTotallyReal K] [IsTotallyReal E]

include hdeg hne hunram in
theorem twice_norm_range_card :
    2*Nat.card (ClassNormInvariance.normLinear K E).range = Nat.card (ClassGroup (𝓞 K)) := by
  rw [Nat.card_congr (rangeEquiv K E),mul_comm]
  have h := (NormClassHom.norm K E).range.card_mul_index
  have hi : (NormClassHom.norm K E).range.index = 2 := by
    change Nat.card (ClassGroup (𝓞 K) ⧸ (NormClassHom.norm K E).range) = 2
    rw [← subgroup_eq_range]
    exact card_eq_two K E σ hdeg hne hunram
  rwa [hi] at h

include hdeg hne hunram in
theorem norm_range_card_eq_fixed :
    Nat.card (ClassNormInvariance.normLinear K E).range = Nat.card (plus (A := C E) (cAction K E σ)) := by
  have h₁ := ClassNormInvariance.range_card_le_fixed K E σ
  have h₂ := UnramifiedAmbiguousClasses.twice_fixedClasses_le K E σ hdeg hne hunram
  have h₃ := twice_norm_range_card K E σ hdeg hne hunram
  omega

set_option maxHeartbeats 2000000 in
include hdeg hne hunram in
/-- The class norm has no kernel beyond the differences of conjugates. -/
theorem norm_kernel_eq_difference :
    (ClassNormInvariance.normLinear K E).ker = (cAction K E σ-LinearMap.id).range := by
  letI : Finite (C E) := Finite.of_equiv (FractionalClasses.Classes E) Additive.ofMul
  letI : Finite (C K) := Finite.of_equiv (FractionalClasses.Classes K) Additive.ofMul
  exact @FiniteEndomorphism.ker_eq_difference (C E) (C K) inferInstance inferInstance inferInstance inferInstance
    (cAction K E σ) (ClassNormInvariance.normLinear K E) (ClassNormInvariance.normLinear_action K E σ)
    (norm_range_card_eq_fixed K E σ hdeg hne hunram)

include hdeg hne hunram in
theorem twice_fixed_card :
    2*Nat.card (plus (A := C E) (cAction K E σ)) = Nat.card (ClassGroup (𝓞 K)) := by
  rw [← norm_range_card_eq_fixed K E σ hdeg hne hunram]
  exact twice_norm_range_card K E σ hdeg hne hunram

include hne hunram in
theorem ambiguousDefect_card :
    Nat.card (ambiguousDefect K E σ hdeg) = Nat.card (QuadraticUnitHerbrand.H0 K E σ hdeg) := by
  have h₁ := (pOnFixed (idealsSequence K E σ hdeg)).range.card_eq_card_quotient_mul_card
  change Nat.card (plus (A := C E) (cAction K E σ)) =
    Nat.card (pOnFixed (idealsSequence K E σ hdeg)).range * Nat.card (ambiguousDefect K E σ hdeg) at h₁
  have h₂ := baseQuotient_card K E σ hdeg hne
  rw [Nat.card_congr (UnramifiedAmbiguousClasses.baseEquiv K E σ hdeg hne hunram).toEquiv,
    QuadraticUnitHerbrand.herbrand K E σ hdeg hne] at h₂
  have hc : Nat.card (C K) = Nat.card (ClassGroup (𝓞 K)) :=
    Nat.card_congr (Additive.toMul.trans (FractionalClasses.equiv K).toEquiv)
  rw [hc,← twice_fixed_card K E σ hdeg hne hunram,h₁] at h₂
  have hp : 0 < Nat.card (pOnFixed (idealsSequence K E σ hdeg)).range := Nat.card_pos
  nlinarith

include hne hunram in
theorem principalH1_card :
    Nat.card (InvolutionSequence.H1 (idealsSequence K E σ hdeg)) =
      Nat.card (QuadraticUnitHerbrand.H0 K E σ hdeg) := by
  apply le_antisymm (principalH1_card_le K E σ hdeg hne)
  rw [← ambiguousDefect_card K E σ hdeg hne hunram,
    Nat.card_congr (ambiguousDefectEquiv K E σ hdeg).toEquiv]
  letI := principalH1_finite K E σ hdeg hne
  exact Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective

end UnramifiedNormIndex

namespace UnramifiedNormIndex
open NumberField PrincipalInvolutionSequences InvolutionHerbrand InvolutionSequence
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) [IsTotallyReal K] [IsTotallyReal E]

include hne hunram in
theorem opposite_connecting_surjective :
    Function.Surjective (connecting (unitsSequence K E σ hdeg).neg) := by
  let S := unitsSequence K E σ hdeg
  letI : Finite (quotientH1 S) := principalH1_finite K E σ hdeg hne
  letI : Finite (InvolutionSequence.H1 S.neg) := finite_opposite_units K E σ hdeg
  letI := Fintype.ofFinite (quotientH1 S)
  letI := Fintype.ofFinite (InvolutionSequence.H1 S.neg)
  have hh := hilbert90 K E σ hdeg hne
  have hcard : Fintype.card (quotientH1 S) = Fintype.card (InvolutionSequence.H1 S.neg) := by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
    rw [Nat.card_congr (oppositeUnitsEquiv K E σ hdeg).toEquiv]
    exact principalH1_card K E σ hdeg hne hunram
  have hsurj := ((Fintype.bijective_iff_injective_and_card (oppositeEmbedding S hh)).mpr
    ⟨oppositeEmbedding_injective S hh,hcard⟩).surjective
  intro t
  obtain ⟨q,hq⟩ := hsurj t
  obtain ⟨b,rfl⟩ := (norm (-S.b) (neg_involution S.b S.hb)).range.mkQ_surjective q
  exact ⟨b,hq⟩

include hdeg hne hunram in
/-- Every base unit is a field norm in a totally real unramified quadratic
extension. The preimage is not asserted to be an integral unit. -/
theorem unit_is_field_norm (u : (𝓞 K)ˣ) :
    ∃ x : Eˣ, Algebra.norm K (x : E) = (u : K) := by
  let uf := QuadraticUnitHerbrand.fixedEquiv K E σ hdeg hne (Additive.ofMul u)
  obtain ⟨x,hx⟩ := exists_norm_of_opposite_surjective (unitsSequence K E σ hdeg)
    (opposite_connecting_surjective K E σ hdeg hne hunram) uf
  refine ⟨x.toMul,?_⟩
  apply (algebraMap K E).injective
  rw [QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne]
  have h := congrArg (fun z : F E => (z.toMul : E)) hx
  change ((x.toMul * FractionalGalois.fieldAction E σ.toRingEquiv x.toMul : Eˣ) : E) =
    algebraMap K E (u : K) at h
  rw [Units.val_mul] at h
  change (x.toMul : E)*σ (x.toMul : E) = algebraMap K E (u : K) at h
  simpa only [mul_comm] using h

end UnramifiedNormIndex

namespace UnramifiedIdealNorm
open scoped Classical

section Ring
variable {R : Type*} [CommRing R] (σ : R ≃+* R)

noncomputable def normSpan (I : Ideal R) : Ideal R :=
  Ideal.span ((fun x : R => σ x*x) '' (I : Set R))

private theorem norm_mem (I : Ideal R) (x : R) (hx : x ∈ I) : σ x*x ∈ normSpan σ I :=
  Ideal.subset_span ⟨x,hx,rfl⟩

private theorem cross_mem (I : Ideal R) (x y : R) (hx : x ∈ I) (hy : y ∈ I) :
    σ x*y+x*σ y ∈ normSpan σ I := by
  have h := (normSpan σ I).sub_mem
    ((normSpan σ I).sub_mem (norm_mem σ I (x+y) (I.add_mem hx hy)) (norm_mem σ I x hx))
    (norm_mem σ I y hy)
  convert h using 1
  rw [map_add]
  ring

/-- If conjugate differences generate the unit ideal, an ideal norm is
the product of the ideal and its conjugate, even in residue characteristic two. -/
theorem normSpan_eq_mul (hdiff : Ideal.span (Set.range (fun a : R => σ a-a)) = ⊤) (I : Ideal R) :
    normSpan σ I = I*Ideal.map σ I := by
  have hxy (x y : R) (hx : x ∈ I) (hy : y ∈ I) : x*σ y ∈ normSpan σ I := by
    have hone : (1 : R) ∈ Ideal.span (Set.range (fun a : R => σ a-a)) := by rw [hdiff]; trivial
    have hmul : ∀ a ∈ Ideal.span (Set.range (fun a : R => σ a-a)), a*(x*σ y) ∈ normSpan σ I := by
      intro a ha
      refine Submodule.span_induction (p := fun a _ => a*(x*σ y) ∈ normSpan σ I) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨b,rfl⟩
        have h₁ := cross_mem σ I x (b*y) hx (I.mul_mem_left b hy)
        have h₂ := (normSpan σ I).mul_mem_left b (cross_mem σ I x y hx hy)
        convert (normSpan σ I).sub_mem h₁ h₂ using 1
        rw [map_mul]
        ring
      · simpa using (normSpan σ I).zero_mem
      · intro a b ha hb h₁ h₂
        simpa only [add_mul] using (normSpan σ I).add_mem h₁ h₂
      · intro a b hb h
        simpa only [smul_eq_mul,mul_assoc] using (normSpan σ I).mul_mem_left a h
    simpa only [one_mul] using hmul 1 hone
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨x,hx,rfl⟩
    change σ x*x ∈ I*Ideal.map σ I
    rw [mul_comm (σ x)]
    exact Ideal.mul_mem_mul hx (Ideal.mem_map_of_mem _ hx)
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨z,hz,rfl⟩ := (Ideal.mem_map_iff_of_surjective _ σ.surjective).mp hy
    exact hxy x z hx hz

end Ring

open NumberField
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)

include hdeg hne in
theorem intNorm_eq_mul (x : 𝓞 E) :
    algebraMap (𝓞 K) (𝓞 E) (Algebra.intNorm (𝓞 K) (𝓞 E) x) = RingOfIntegers.mapAlgEquiv σ x*x := by
  apply RingOfIntegers.coe_injective
  change algebraMap K E (algebraMap (𝓞 K) K (Algebra.intNorm (𝓞 K) (𝓞 E) x)) = σ (x : E)*(x : E)
  rw [Algebra.algebraMap_intNorm (K := K) (L := E)]
  exact QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne (x : E)

include hdeg hne in
/-- The relative ideal norm agrees with the product of conjugate ideals
in an unramified quadratic extension. -/
theorem map_relNorm (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) (I : Ideal (𝓞 E)) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 E)) (Ideal.relNorm (𝓞 K) I) =
      I*Ideal.map (RingOfIntegers.mapAlgEquiv σ) I := by
  have h := normSpan_eq_mul (RingOfIntegers.mapAlgEquiv σ).toRingEquiv
    (UnramifiedIdealDescent.difference_span_top K E σ hne hunram) I
  rw [Ideal.map_relNorm]
  have hf : ((algebraMap (𝓞 K) (𝓞 E)) ∘ Algebra.intNorm (𝓞 K) (𝓞 E)) =
      (fun x : 𝓞 E => RingOfIntegers.mapAlgEquiv σ x*x) :=
    funext (intNorm_eq_mul K E σ hdeg hne)
  rw [hf]
  exact h

end UnramifiedIdealNorm

namespace UnramifiedFractionalNorm
open NumberField PrincipalInvolutionSequences InvolutionHerbrand InvolutionSequence FractionalGalois
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)

noncomputable def idealNorm : D E →ₗ[ℤ] D K :=
  (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).symm.toLinearMap.comp
    (InvolutionHerbrand.norm (dAction K E σ) (dAction_involutive K E σ hdeg))

noncomputable def fieldNorm : F E →ₗ[ℤ] F K :=
  (MonoidHom.toAdditive (Units.map (Algebra.norm K))).toIntLinearMap

@[simp] theorem idealFixed_norm (I : D E) :
    UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram (idealNorm K E σ hdeg hne hunram I) =
      InvolutionHerbrand.norm (dAction K E σ) (dAction_involutive K E σ hdeg) I := by
  exact (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).apply_symm_apply _

@[simp] theorem idealNorm_principal (x : F E) :
    idealNorm K E σ hdeg hne hunram (UnramifiedAmbiguousClasses.principalWhole E x) =
      UnramifiedAmbiguousClasses.principalWhole K (fieldNorm K E x) := by
  apply (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).injective
  rw [idealFixed_norm]
  apply Subtype.ext
  change Additive.ofMul (FractionalGalois.action E σ.toRingEquiv (toPrincipalIdeal (𝓞 E) E x.toMul) *
      toPrincipalIdeal (𝓞 E) E x.toMul) =
    Additive.ofMul (FractionalGalois.extend K E (toPrincipalIdeal (𝓞 K) K (Units.map (Algebra.norm K) x.toMul)))
  apply congrArg Additive.ofMul
  rw [action_principal,← map_mul,extend_principal]
  apply congrArg (toPrincipalIdeal (𝓞 E) E)
  apply Units.ext
  change σ (x.toMul : E)*(x.toMul : E) = algebraMap K E (Algebra.norm K (x.toMul : E))
  exact (QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne (x.toMul : E)).symm

@[simp] theorem idealNorm_action (I : D E) :
    idealNorm K E σ hdeg hne hunram (dAction K E σ I) = idealNorm K E σ hdeg hne hunram I := by
  apply (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).injective
  rw [idealFixed_norm,idealFixed_norm]
  apply Subtype.ext
  change dAction K E σ (dAction K E σ I)+dAction K E σ I = dAction K E σ I+I
  rw [involutive _ (dAction_involutive K E σ hdeg)]
  abel

@[simp] theorem idealNorm_integral (I : (Ideal (𝓞 E))⁰) :
    idealNorm K E σ hdeg hne hunram (Additive.ofMul (FractionalIdeal.mk0 E I)) =
      Additive.ofMul (FractionalIdeal.mk0 K (IdealPrimeMap.norm K E I)) := by
  apply (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).injective
  rw [idealFixed_norm]
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Units.ext
  change actionHom E σ.toRingEquiv (FractionalIdeal.mk0 E I).1 * (FractionalIdeal.mk0 E I).1 =
    FractionalIdeal.extendedHomₐ E (𝓞 E) (FractionalIdeal.mk0 K (IdealPrimeMap.norm K E I)).1
  rw [FractionalIdeal.coe_mk0,FractionalIdeal.coe_mk0,
    FractionalIdeal.extendedHomₐ_coeIdeal_eq_map]
  change ((I.1 : FractionalIdeal (𝓞 E)⁰ E).extended E _) * (I.1 : FractionalIdeal (𝓞 E)⁰ E) = _
  rw [FractionalIdeal.extended_coeIdeal_eq_map,← FractionalIdeal.coeIdeal_mul]
  congr 1
  exact (mul_comm _ _).trans (UnramifiedIdealNorm.map_relNorm K E σ hdeg hne hunram I.1).symm

private theorem principalClass_zero (x : F K) :
    classMap K (UnramifiedAmbiguousClasses.principalWhole K x) = 0 :=
  FractionalClasses.mk_principal K x.toMul

private theorem classMap_surjective : Function.Surjective (classMap E) := by
  intro c
  obtain ⟨I,hI⟩ := FractionalClasses.mk_surjective E c.toMul
  exact ⟨Additive.ofMul I,congrArg Additive.ofMul hI⟩

private theorem kernel_class_le : (classMap E).ker ≤
    ((classMap K).comp (idealNorm K E σ hdeg hne hunram)).ker := by
  intro I hI
  rw [UnramifiedAmbiguousClasses.ker_classMap] at hI
  obtain ⟨x,rfl⟩ := hI
  change classMap K (idealNorm K E σ hdeg hne hunram (UnramifiedAmbiguousClasses.principalWhole E x)) = 0
  rw [idealNorm_principal,principalClass_zero]

set_option maxHeartbeats 3000000 in
private noncomputable def inducedNorm : C E →ₗ[ℤ] C K :=
  @factor (D E) (C E) (C K) inferInstance inferInstance inferInstance (classMap E) (classMap_surjective E)
    ((classMap K).comp (idealNorm K E σ hdeg hne hunram)) (kernel_class_le K E σ hdeg hne hunram)

set_option maxHeartbeats 3000000 in
private theorem inducedNorm_class (I : D E) :
    inducedNorm K E σ hdeg hne hunram (classMap E I) = classMap K (idealNorm K E σ hdeg hne hunram I) :=
  @factor_apply (D E) (C E) (C K) inferInstance inferInstance inferInstance
    (classMap E) (classMap_surjective E)
    ((classMap K).comp (idealNorm K E σ hdeg hne hunram)) (kernel_class_le K E σ hdeg hne hunram) I

set_option maxHeartbeats 2000000 in
private theorem inducedNorm_eq : inducedNorm K E σ hdeg hne hunram = ClassNormInvariance.normLinear K E := by
  apply LinearMap.ext
  intro c
  obtain ⟨I,hI⟩ := FractionalClasses.mkIdeal_surjective E c.toMul
  have hc : classMap E (Additive.ofMul (FractionalIdeal.mk0 E I)) = c := congrArg Additive.ofMul hI
  rw [← hc,inducedNorm_class,idealNorm_integral]
  exact (FractionalClasses.norm_mkIdeal K E I).symm

set_option maxHeartbeats 2000000 in
/-- The ideal-group norm induces the already constructed ideal-class norm. -/
theorem norm_class (I : D E) :
    ClassNormInvariance.normLinear K E (classMap E I) = classMap K (idealNorm K E σ hdeg hne hunram I) := by
  rw [← inducedNorm_eq K E σ hdeg hne hunram]
  exact inducedNorm_class K E σ hdeg hne hunram I

end UnramifiedFractionalNorm

namespace UnramifiedFractionalNorm
open NumberField PrincipalInvolutionSequences InvolutionHerbrand InvolutionSequence FractionalGalois
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  [IsTotallyReal K] [IsTotallyReal E]
  (σ : E ≃ₐ[K] E) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)

set_option maxHeartbeats 3000000 in
/-- In an unramified totally real quadratic extension, a field element
whose principal ideal is an ideal norm is itself a field norm. -/
theorem exists_fieldNorm_of_idealNorm (a : F K) (I : D E)
    (ha : UnramifiedAmbiguousClasses.principalWhole K a = idealNorm K E σ hdeg hne hunram I) :
    ∃ x : F E, fieldNorm K E x = a := by
  have hI : classMap E I ∈ (ClassNormInvariance.normLinear K E).ker := by
    change ClassNormInvariance.normLinear K E (classMap E I) = 0
    rw [norm_class K E σ hdeg hne hunram,← ha]
    exact FractionalClasses.mk_principal K a.toMul
  rw [UnramifiedNormIndex.norm_kernel_eq_difference K E σ hdeg hne hunram] at hI
  obtain ⟨c,hc⟩ := hI
  obtain ⟨J,hJ⟩ := FractionalClasses.mk_surjective E c.toMul
  let j : D E := Additive.ofMul J
  have hj : classMap E j = c := congrArg Additive.ofMul hJ
  let T : D E := I-(dAction K E σ j-j)
  have hT : classMap E T = 0 := by
    change classMap E (I-(dAction K E σ j-j)) = 0
    rw [map_sub,map_sub]
    change classMap E I-(cAction K E σ (classMap E j)-classMap E j) = 0
    rw [hj]
    change cAction K E σ c-c = classMap E I at hc
    rw [hc,sub_self]
  have hT' : T ∈ (UnramifiedAmbiguousClasses.principalWhole E).range := by
    rw [← UnramifiedAmbiguousClasses.ker_classMap]
    exact hT
  obtain ⟨x,hx⟩ := hT'
  have hn : idealNorm K E σ hdeg hne hunram T = idealNorm K E σ hdeg hne hunram I := by
    change idealNorm K E σ hdeg hne hunram (I-(dAction K E σ j-j)) = _
    rw [map_sub,map_sub,idealNorm_action,sub_self,sub_zero]
  have hpx : UnramifiedAmbiguousClasses.principalWhole K (fieldNorm K E x) =
      UnramifiedAmbiguousClasses.principalWhole K a := by
    rw [← idealNorm_principal K E σ hdeg hne hunram,hx,hn,ha]
  have hu : UnramifiedAmbiguousClasses.principalWhole K (a-fieldNorm K E x) = 0 := by
    rw [map_sub,hpx,sub_self]
  obtain ⟨u,hu⟩ := (principal_eq_one_iff K (a-fieldNorm K E x).toMul).mp hu
  obtain ⟨y,hy⟩ := UnramifiedNormIndex.unit_is_field_norm K E σ hdeg hne hunram u
  have hy' : fieldNorm K E (Additive.ofMul y) = a-fieldNorm K E x := by
    apply Additive.toMul.injective
    apply Units.ext
    change Algebra.norm K (y : E) = _
    rw [hy]
    exact congrArg (fun z : Kˣ => (z : K)) hu
  refine ⟨x+Additive.ofMul y,?_⟩
  rw [map_add,hy']
  abel

end UnramifiedFractionalNorm


namespace CocycleTwo
open scoped Classical
variable {G A B : Type*} [Group G] [AddCommGroup A] [AddCommGroup B]
  (ρ : G →* AddAut A)

def IsCocycle (f : G → G → A) : Prop :=
  ∀ g h k, ρ g (f h k)+f g (h*k) = f g h+f (g*h) k

def boundary (b : G → A) (g h : G) : A := ρ g (b h)-b (g*h)+b g

def IsCoboundary (f : G → G → A) : Prop := ∃ b, f = boundary ρ b

@[simp] theorem act_one (a : A) : ρ 1 a = a := by rw [map_one]; rfl
@[simp] theorem act_mul (g h : G) (a : A) : ρ (g*h) a = ρ g (ρ h a) := by rw [map_mul]; rfl

@[simp] theorem boundary_one_one (b : G → A) : boundary ρ b 1 1 = b 1 := by
  simp [boundary]

theorem boundary_cocycle (b : G → A) : IsCocycle ρ (boundary ρ b) := by
  intro g h k
  simp only [boundary,map_add,map_sub,act_mul,mul_assoc]
  abel

theorem cocycle_one_left {f : G → G → A} (hf : IsCocycle ρ f) (g : G) : f 1 g = f 1 1 := by
  have h := hf 1 1 g
  simp only [act_one,one_mul] at h
  exact add_right_cancel h

theorem cocycle_one_right {f : G → G → A} (hf : IsCocycle ρ f) (g : G) : f g 1 = ρ g (f 1 1) := by
  have h := hf g 1 1
  simp only [one_mul,mul_one] at h
  exact (add_right_cancel h).symm

/-- In a group of order two, a cocycle is determined modulo boundaries by
one invariant element. -/
theorem quadratic_fixed {f : G → G → A} (hf : IsCocycle ρ f)
    (s : G) (hs : s*s = 1) :
    ρ s (f s s-ρ s (f 1 1)) = f s s-ρ s (f 1 1) := by
  have h := hf s s s
  rw [hs,cocycle_one_left ρ hf,cocycle_one_right ρ hf] at h
  have he : ρ s (ρ s (f 1 1)) = f 1 1 := by rw [← act_mul,hs,act_one]
  rw [map_sub,he]
  exact sub_eq_sub_iff_add_eq_add.mpr h

/-- Explicit trivialization of a quadratic cocycle with norm obstruction zero. -/
theorem quadratic_coboundary {f : G → G → A} (hf : IsCocycle ρ f)
    (s : G) (hne : s ≠ 1) (hs : s*s = 1) (hg : ∀ g : G, g = 1 ∨ g = s)
    (x : A) (hx : ρ s x+x = f s s-ρ s (f 1 1)) : IsCoboundary ρ f := by
  let b : G → A := fun g => f 1 1 + if g = 1 then 0 else x
  refine ⟨b,?_⟩
  funext g h
  rcases hg g with rfl | rfl <;> rcases hg h with rfl | rfl
  · simp [b,boundary]
  · simp [b,boundary,cocycle_one_left ρ hf]
  · rw [cocycle_one_right ρ hf]
    simp only [boundary,b,mul_one,if_pos,if_neg hne,add_zero]
    abel
  · simp only [boundary,b,hs,if_pos,if_neg hne,map_add,add_zero]
    have hh := (eq_sub_iff_add_eq.mp hx).symm
    convert hh using 1 <;> abel

/-- An equivariant map that reflects the quadratic norm obstruction is
injective on second cohomology, in explicit cocycle form. -/
theorem quadratic_injective (τ : G →* AddAut B) (p : A →+ B)
    (hp : ∀ g a, p (ρ g a) = τ g (p a))
    (s : G) (hne : s ≠ 1) (hs : s*s = 1) (hg : ∀ g : G, g = 1 ∨ g = s)
    (hlift : ∀ a : A, ρ s a = a → ∀ I : B,
      p a = τ s I+I → ∃ x : A, ρ s x+x = a)
    {f : G → G → A} (hf : IsCocycle ρ f)
    (hb : IsCoboundary τ (fun g h => p (f g h))) : IsCoboundary ρ f := by
  obtain ⟨b,hb⟩ := hb
  have hb' (g h : G) : p (f g h) = boundary τ b g h := congrFun (congrFun hb g) h
  have h1 : p (f 1 1) = b 1 := by simpa using hb' 1 1
  have hnorm : p (f s s-ρ s (f 1 1)) = τ s (b s-b 1)+(b s-b 1) := by
    rw [map_sub,hp,h1,hb' s s]
    simp only [boundary,hs,map_sub]
    abel
  obtain ⟨x,hx⟩ := hlift _ (quadratic_fixed ρ hf s hs) _ hnorm
  exact quadratic_coboundary ρ hf s hne hs hg x hx

end CocycleTwo

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

noncomputable def fieldAction : Gal(E/K) →* AddAut (F E) where
  toFun σ := (FractionalGalois.fieldAction E σ.toRingEquiv).toAdditive
  map_one' := by
    apply AddEquiv.ext
    intro x
    rfl
  map_mul' σ τ := by
    apply AddEquiv.ext
    intro x
    rfl

noncomputable def idealAction : Gal(E/K) →* AddAut (D E) where
  toFun σ := (FractionalGalois.action E σ.toRingEquiv).toAdditive
  map_one' := by
    apply AddEquiv.ext
    intro I
    apply Additive.toMul.injective
    apply Units.ext
    ext x
    change x ∈ actionHom E (1 : Gal(E/K)).toRingEquiv I.toMul.1 ↔ x ∈ I.toMul.1
    rw [mem_actionHom]
    rfl
  map_mul' σ τ := by
    apply AddEquiv.ext
    intro I
    apply Additive.toMul.injective
    apply Units.ext
    ext x
    change x ∈ actionHom E (σ*τ).toRingEquiv I.toMul.1 ↔
      x ∈ actionHom E σ.toRingEquiv (actionHom E τ.toRingEquiv I.toMul.1)
    rw [mem_actionHom,mem_actionHom,mem_actionHom]
    rfl

theorem principal_equivariant (σ : Gal(E/K)) (x : F E) :
    UnramifiedAmbiguousClasses.principalWhole E (fieldAction K E σ x) =
      idealAction K E σ (UnramifiedAmbiguousClasses.principalWhole E x) := by
  exact congrArg Additive.ofMul (FractionalGalois.action_principal E σ.toRingEquiv x.toMul).symm

end GaloisCocycleActions


namespace UnramifiedFractionalNorm
open NumberField PrincipalInvolutionSequences InvolutionHerbrand FractionalGalois
open scoped Classical nonZeroDivisors

variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  [IsTotallyReal K] [IsTotallyReal E]
  (σ : Gal(E/K)) (hdeg : Module.finrank K E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)

theorem fieldFixed_norm (x : F E) :
    (UnramifiedAmbiguousClasses.fieldFixed K E σ hdeg hne (fieldNorm K E x)).1 =
      fAction K E σ x+x := by
  apply Additive.toMul.injective
  apply Units.ext
  exact QuadraticUnitHerbrand.norm_eq_mul K E σ hdeg hne x.toMul

include hdeg hne hunram in
theorem fixed_norm_lift (a : F E) (ha : fAction K E σ a = a) (I : D E)
    (hI : UnramifiedAmbiguousClasses.principalWhole E a = dAction K E σ I+I) :
    ∃ x : F E, fAction K E σ x+x = a := by
  let af : plus (fAction K E σ) := ⟨a,(mem_plus _ _).mpr ha⟩
  let a₀ := (UnramifiedAmbiguousClasses.fieldFixed K E σ hdeg hne).symm af
  have ha₀ : (UnramifiedAmbiguousClasses.fieldFixed K E σ hdeg hne a₀).1 = a := by
    exact congrArg Subtype.val ((UnramifiedAmbiguousClasses.fieldFixed K E σ hdeg hne).apply_symm_apply af)
  have hnorm : UnramifiedAmbiguousClasses.principalWhole K a₀ = idealNorm K E σ hdeg hne hunram I := by
    apply (UnramifiedAmbiguousClasses.idealFixed K E σ hdeg hne hunram).injective
    rw [idealFixed_norm]
    apply Subtype.ext
    change Additive.ofMul (FractionalGalois.extend K E (toPrincipalIdeal (𝓞 K) K a₀.toMul)) = _
    rw [extend_principal]
    change UnramifiedAmbiguousClasses.principalWhole E
      (UnramifiedAmbiguousClasses.fieldFixed K E σ hdeg hne a₀).1 = dAction K E σ I+I
    rw [ha₀,hI]
  obtain ⟨x,hx⟩ := exists_fieldNorm_of_idealNorm K E σ hdeg hne hunram a₀ I hnorm
  refine ⟨x,?_⟩
  rw [← fieldFixed_norm K E σ hdeg hne,hx,ha₀]

include σ hdeg hne hunram in
/-- Principal ideals induce an injection on quadratic second cohomology,
expressed without choosing a cohomology presentation. -/
theorem quadratic_cocycle_injective
    {f : Gal(E/K) → Gal(E/K) → F E}
    (hf : CocycleTwo.IsCocycle (GaloisCocycleActions.fieldAction K E) f)
    (hb : CocycleTwo.IsCoboundary (GaloisCocycleActions.idealAction K E)
      (fun g h => UnramifiedAmbiguousClasses.principalWhole E (f g h))) :
    CocycleTwo.IsCoboundary (GaloisCocycleActions.fieldAction K E) f := by
  apply CocycleTwo.quadratic_injective (GaloisCocycleActions.fieldAction K E)
    (GaloisCocycleActions.idealAction K E) (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom
    (GaloisCocycleActions.principal_equivariant K E) σ hne _
    (QuadraticUnitHerbrand.aut_eq_one_or K E σ hdeg hne) _ hf hb
  · ext x
    exact sigma_involutive K E σ hdeg x
  · intro a ha I hI
    exact fixed_norm_lift K E σ hdeg hne hunram a ha I hI

end UnramifiedFractionalNorm

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
variable {G : Type*} [Group G] [Fintype G] (r : G →* Gal(E/K))

/-- First cohomology of the fractional ideal group vanishes: the sum of
a multiplicative cocycle's ideals supplies a potential. -/
theorem ideal_hilbert90 (b : G → D E)
    (hb : ∀ g h, b (g*h) = GaloisCocycleActions.idealAction K E (r g) (b h)+b g) :
    ∃ I : D E, ∀ g, GaloisCocycleActions.idealAction K E (r g) I-I = b g := by
  let J : FractionalIdeal (𝓞 E)⁰ E := ∑ g : G, (b g).toMul.1
  have hJ : J ≠ 0 := by
    intro h
    have hh : (b 1).toMul.1 ≤ J := Finset.single_le_sum (f := fun g : G => (b g).toMul.1) (fun g _ => zero_le _) (Finset.mem_univ (1 : G))
    rw [h] at hh
    exact (b 1).toMul.ne_zero (le_antisymm hh (zero_le _))
  let j : Ideals E := Units.mk0 J hJ
  have hj (g : G) : (b g).toMul.1 * actionHom E (r g).toRingEquiv J = J := by
    change (b g).toMul.1 * actionHom E (r g).toRingEquiv (∑ h : G, (b h).toMul.1) = _
    rw [map_sum,Finset.mul_sum]
    calc
      (∑ h : G, (b g).toMul.1 * actionHom E (r g).toRingEquiv (b h).toMul.1) =
          ∑ h : G, (b (g*h)).toMul.1 := by
        apply Finset.sum_congr rfl
        intro h _
        have hh := congrArg (fun z : D E => z.toMul.1) (hb g h)
        change (b (g*h)).toMul.1 = actionHom E (r g).toRingEquiv (b h).toMul.1 * (b g).toMul.1 at hh
        rw [hh,mul_comm]
      _ = J := by exact Equiv.sum_comp (Equiv.mulLeft g) (fun h => (b h).toMul.1)
  refine ⟨-Additive.ofMul j,?_⟩
  intro g
  have hh : b g+GaloisCocycleActions.idealAction K E (r g) (Additive.ofMul j) = Additive.ofMul j := by
    apply Additive.toMul.injective
    exact Units.ext (hj g)
  rw [map_neg]
  have hh' := eq_sub_of_add_eq hh
  rw [hh']
  abel

end GaloisCocycleActions

namespace FractionalGalois
open NumberField
open scoped Classical nonZeroDivisors
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  (σ : K ≃+* K) (τ : E ≃+* E)
  (hcomm : ∀ x, τ (algebraMap K E x) = algebraMap K E (σ x))

include hcomm in
theorem action_mem_extension (I : FractionalIdeal (𝓞 K)⁰ K) (x : E)
    (hx : x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) I) :
    τ x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) (actionHom K σ I) := by
  change x ∈ ((FractionalIdeal.extendedHomₐ E (𝓞 E) I) : Submodule (𝓞 E) E) at hx
  change τ x ∈ ((FractionalIdeal.extendedHomₐ E (𝓞 E) (actionHom K σ I)) : Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHomₐ_eq_span] at hx ⊢
  refine Submodule.span_induction (p := fun x _ => τ x ∈
    Submodule.span (𝓞 E) (algebraMap K E '' (actionHom K σ I : Set K))) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y,hy,rfl⟩
    rw [hcomm]
    refine Submodule.subset_span ⟨σ y,?_,rfl⟩
    exact (mem_actionHom K σ I (σ y)).mpr (by simpa only [RingEquiv.symm_apply_apply] using hy)
  · simpa only [map_zero] using Submodule.zero_mem _
  · intro a b ha hb h₁ h₂
    simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · intro a b hb h
    change τ ((a : E)*b) ∈ _
    rw [map_mul]
    exact Submodule.smul_mem _ (RingOfIntegers.mapRingEquiv τ a) h

include hcomm in
theorem action_extend (I : Ideals K) :
    action E τ (extend K E I) = extend K E (action K σ I) := by
  have hi (x : K) : τ.symm (algebraMap K E x) = algebraMap K E (σ.symm x) := by
    apply τ.injective
    rw [RingEquiv.apply_symm_apply,hcomm,RingEquiv.apply_symm_apply]
  apply Units.ext
  ext x
  change x ∈ actionHom E τ (FractionalIdeal.extendedHomₐ E (𝓞 E) I.1) ↔
    x ∈ FractionalIdeal.extendedHomₐ E (𝓞 E) (actionHom K σ I.1)
  rw [mem_actionHom]
  constructor
  · intro hx
    simpa only [RingEquiv.apply_symm_apply] using
      action_mem_extension K E σ τ hcomm I.1 (τ.symm x) hx
  · intro hx
    have h := action_mem_extension K E σ.symm τ.symm hi (actionHom K σ I.1) x hx
    rwa [actionHom_symm] at h

end FractionalGalois

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois
open scoped Classical nonZeroDivisors
variable (K M E : Type) [Field K] [Field M] [Field E]
  [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [Normal K M]

noncomputable def fieldExtension : F M →+ F E := MonoidHom.toAdditive (fieldExtend M E)
noncomputable def idealExtension : D M →+ D E := MonoidHom.toAdditive (extend M E)

theorem fieldExtension_injective : Function.Injective (fieldExtension M E) := by
  exact Units.map_injective (algebraMap M E).injective

theorem idealExtension_injective : Function.Injective (idealExtension M E) := extend_injective M E

theorem fieldExtension_equivariant (σ : Gal(E/K)) (x : F M) :
    fieldExtension M E (GaloisCocycleActions.fieldAction K M (AlgEquiv.restrictNormalHom M σ) x) =
      GaloisCocycleActions.fieldAction K E σ (fieldExtension M E x) := by
  apply Additive.toMul.injective
  apply Units.ext
  exact σ.restrictNormal_commutes M x.toMul

theorem idealExtension_equivariant (σ : Gal(E/K)) (I : D M) :
    idealExtension M E (GaloisCocycleActions.idealAction K M (AlgEquiv.restrictNormalHom M σ) I) =
      GaloisCocycleActions.idealAction K E σ (idealExtension M E I) := by
  exact congrArg Additive.ofMul (action_extend M E (σ.restrictNormal M).toRingEquiv σ.toRingEquiv
    (fun x => (σ.restrictNormal_commutes M x).symm) I.toMul).symm

theorem principal_extension (x : F M) :
    UnramifiedAmbiguousClasses.principalWhole E (fieldExtension M E x) =
      idealExtension M E (UnramifiedAmbiguousClasses.principalWhole M x) := by
  exact congrArg Additive.ofMul (extend_principal M E x.toMul).symm

end GaloisCocycleActions


namespace CocycleTwo
open scoped Classical
variable {G Q A : Type*} [Group G] [Group Q] [AddCommGroup A]
  (ρ : G →* AddAut A)

def IsCocycleOne (b : G → A) : Prop := ∀ g h, b (g*h) = ρ g (b h)+b g

def VanishingH1 : Prop := ∀ b : G → A, IsCocycleOne ρ b → ∃ a, ∀ g, ρ g a-a = b g

theorem cocycle_add {f t : G → G → A} (hf : IsCocycle ρ f) (ht : IsCocycle ρ t) :
    IsCocycle ρ (fun g h => f g h+t g h) := by
  intro g h k
  simp only [map_add]
  calc
    _ = (ρ g (f h k)+f g (h*k))+(ρ g (t h k)+t g (h*k)) := by abel
    _ = (f g h+f (g*h) k)+(t g h+t (g*h) k) := by rw [hf,ht]
    _ = _ := by abel

theorem cocycle_sub {f t : G → G → A} (hf : IsCocycle ρ f) (ht : IsCocycle ρ t) :
    IsCocycle ρ (fun g h => f g h-t g h) := by
  intro g h k
  simp only [map_sub]
  calc
    _ = (ρ g (f h k)+f g (h*k))-(ρ g (t h k)+t g (h*k)) := by abel
    _ = (f g h+f (g*h) k)-(t g h+t (g*h) k) := by rw [hf,ht]
    _ = _ := by abel

theorem boundary_add (b c : G → A) (g h : G) :
    boundary ρ (fun g => b g+c g) g h = boundary ρ b g h+boundary ρ c g h := by
  simp only [boundary,map_add]
  abel

theorem boundary_neg (b : G → A) (g h : G) :
    boundary ρ (fun g => -b g) g h = -boundary ρ b g h := by
  simp only [boundary,map_neg]
  abel

/-- A normalized section of a surjective group homomorphism. -/
theorem exists_section (q : G →* Q) (hq : Function.Surjective q) :
    ∃ r : Q → G, r 1 = 1 ∧ ∀ x, q (r x) = x := by
  let r : Q → G := fun x => if x = 1 then 1 else (hq x).choose
  refine ⟨r,by simp [r],?_⟩
  intro x
  by_cases hx : x = 1
  · simp [r,hx]
  · simpa [r,hx] using (hq x).choose_spec

/-- First cochain normalization: vanishing on the kernel square can be
extended to vanishing whenever the first argument is in the kernel. -/
theorem normalize_left (q : G →* Q) (r : Q → G) (hr1 : r 1 = 1) (hr : ∀ x, q (r x) = x)
    {f : G → G → A} (hf : IsCocycle ρ f)
    (hzero : ∀ h k, q h = 1 → q k = 1 → f h k = 0) :
    ∃ b : G → A, ∀ h g, q h = 1 → f h g+boundary ρ b h g = 0 := by
  let b : G → A := fun g => f (g*(r (q g))⁻¹) (r (q g))
  refine ⟨b,?_⟩
  intro h g hh
  have h₁ : f 1 1 = 0 := hzero 1 1 (map_one q) (map_one q)
  have bh : b h = 0 := by
    simp only [b,hh,hr1,inv_one,mul_one]
    rw [cocycle_one_right ρ hf,h₁,map_zero]
  have hk : q (g*(r (q g))⁻¹) = 1 := by simp [hr]
  have hp : (g*(r (q g))⁻¹)*r (q g) = g := by group
  have hb : b (h*g) = f (h*(g*(r (q g))⁻¹)) (r (q g)) := by
    simp only [b,map_mul,hh,one_mul,mul_assoc]
  have he := hf h (g*(r (q g))⁻¹) (r (q g))
  rw [hp,hzero h _ hh hk,zero_add] at he
  change ρ h (b g)+f h g = _ at he
  rw [← hb] at he
  simp only [boundary,bh,add_zero]
  rw [← he]
  abel

/-- A left-normalized cocycle transforms equivariantly under left kernel
translation in its first variable. -/
theorem left_covariant (q : G →* Q) {f : G → G → A} (hf : IsCocycle ρ f)
    (hz : ∀ h g, q h = 1 → f h g = 0) (h g k : G) (hh : q h = 1) :
    f (h*g) k = ρ h (f g k) := by
  have he := hf h g k
  rw [hz h _ hh,hz h _ hh,add_zero,zero_add] at he
  exact he.symm

/-- The conjugation defect of a left-normalized cocycle is a 1-cocycle on
the kernel. -/
theorem conjugation_defect (q : G →* Q) {f : G → G → A} (hf : IsCocycle ρ f)
    (hz : ∀ h g, q h = 1 → f h g = 0) (g : G) :
    IsCocycleOne (ρ.comp q.ker.subtype) (fun h : q.ker => f g (g⁻¹*h*g)) := by
  intro h k
  have hq : q h = 1 := h.property
  have hh : q (g⁻¹*h*g) = 1 := by simp only [map_mul,map_inv,hq,mul_one,inv_mul_cancel]
  have hp : (g⁻¹*(h*k : q.ker)*g) = (g⁻¹*h*g)*(g⁻¹*k*g) := by
    change g⁻¹*((h : G)*(k : G))*g = _
    group
  have he := hf g (g⁻¹*h*g) (g⁻¹*k*g)
  rw [hz _ _ hh,map_zero,zero_add,← hp] at he
  have hgh : g*(g⁻¹*h*g) = (h : G)*g := by group
  rw [hgh,left_covariant ρ q hf hz h g _ h.property] at he
  change f g (g⁻¹*(h*k : q.ker)*g) = ρ h (f g (g⁻¹*k*g))+f g (g⁻¹*h*g)
  exact he.trans (add_comm _ _)

/-- If kernel H1 vanishes, a left-normalized cocycle can also be normalized
in the second variable, without disturbing the first normalization. -/
theorem normalize_right (q : G →* Q) (r : Q → G) (hr1 : r 1 = 1) (hr : ∀ x, q (r x) = x)
    (hH1 : VanishingH1 (ρ.comp q.ker.subtype))
    {f : G → G → A} (hf : IsCocycle ρ f)
    (hz : ∀ h g, q h = 1 → f h g = 0) :
    ∃ b : G → A, (∀ h g, q h = 1 → f h g+boundary ρ b h g = 0) ∧
      (∀ g h, q h = 1 → f g h+boundary ρ b g h = 0) := by
  have hex (x : Q) : ∃ a : A, ∀ h : q.ker,
      ρ h a-a = f (r x) ((r x)⁻¹*h*r x) :=
    hH1 _ (conjugation_defect ρ q hf hz (r x))
  let a : Q → A := fun x => if x = 1 then 0 else (hex x).choose
  have ha1 : a 1 = 0 := by simp [a]
  have ha (x : Q) (h : G) (hh : q h = 1) :
      ρ h (a x)-a x = f (r x) ((r x)⁻¹*h*r x) := by
    by_cases hx : x = 1
    · subst x
      rw [ha1,map_zero,sub_self,hr1,hz 1 _ (map_one q)]
    · simpa only [a,if_neg hx] using (hex x).choose_spec ⟨h,hh⟩
  let k : G → G := fun g => g*(r (q g))⁻¹
  have hk (g : G) : q (k g) = 1 := by simp [k,hr]
  have hkr (g : G) : k g*r (q g) = g := by simp [k]
  let b : G → A := fun g => ρ (k g) (a (q g))
  have bh (h : G) (hh : q h = 1) : b h = 0 := by simp [b,hh,ha1]
  have bc (h g : G) (hh : q h = 1) : b (h*g) = ρ h (b g) := by
    simp only [b,k,map_mul,hh,one_mul]
    rw [mul_assoc]; rfl
  have hd (g h : G) (hh : q h = 1) :
      f g (g⁻¹*h*g) = ρ h (b g)-b g := by
    have hkh : q ((k g)⁻¹*h*k g) = 1 := by simp [hh,hk]
    have ht : (r (q g))⁻¹*((k g)⁻¹*h*k g)*r (q g) = g⁻¹*h*g := by
      simp only [k]
      group
    have he := ha (q g) ((k g)⁻¹*h*k g) hkh
    rw [ht] at he
    have hc := left_covariant ρ q hf hz (k g) (r (q g)) (g⁻¹*h*g) (hk g)
    rw [hkr,← he,map_sub] at hc
    rw [hc]
    change ρ (k g) (ρ ((k g)⁻¹*h*k g) (a (q g)))-ρ (k g) (a (q g)) =
      ρ h (ρ (k g) (a (q g)))-ρ (k g) (a (q g))
    congr 1
    rw [← act_mul,← act_mul]
    congr 2
    group
  refine ⟨b,?_,?_⟩
  · intro h g hh
    rw [hz h g hh,boundary,bh h hh,bc h g hh]
    abel
  · intro g h hh
    have hgh : q (g*h*g⁻¹) = 1 := by simp [hh]
    have he := hd g (g*h*g⁻¹) hgh
    have ht : g⁻¹*(g*h*g⁻¹)*g = h := by group
    rw [ht] at he
    have hb : b (g*h) = ρ (g*h*g⁻¹) (b g) := by
      convert bc (g*h*g⁻¹) g hgh using 1
      group
    rw [boundary,bh h hh,map_zero,zero_sub,hb,he]
    abel

/-- A cocycle is horizontal if it vanishes when either argument is in
the kernel of the quotient homomorphism. -/
def Horizontal (q : G →* Q) (f : G → G → A) : Prop :=
  (∀ h g, q h = 1 → f h g = 0) ∧ (∀ g h, q h = 1 → f g h = 0)

/-- The low-degree inflation/restriction normalization theorem. -/
theorem exists_horizontal (q : G →* Q) (hq : Function.Surjective q)
    (hH1 : VanishingH1 (ρ.comp q.ker.subtype))
    {f : G → G → A} (hf : IsCocycle ρ f)
    (hres : IsCoboundary (ρ.comp q.ker.subtype) (fun h k : q.ker => f h k)) :
    ∃ b : G → A, Horizontal q (fun g h => f g h+boundary ρ b g h) := by
  obtain ⟨r,hr1,hr⟩ := exists_section q hq
  obtain ⟨t,ht⟩ := hres
  let d : G → A := fun g => if hg : q g = 1 then -t ⟨g,hg⟩ else 0
  have hd (h : q.ker) : d h = -t h := by
    have hh : q h = 1 := h.property
    simp only [d,dif_pos hh]
  let f₀ : G → G → A := fun g h => f g h+boundary ρ d g h
  have hf₀ : IsCocycle ρ f₀ := cocycle_add ρ hf (boundary_cocycle ρ d)
  have hz₀ (g h : G) (hg : q g = 1) (hh : q h = 1) : f₀ g h = 0 := by
    let g' : q.ker := ⟨g,hg⟩
    let h' : q.ker := ⟨h,hh⟩
    have he : f g h = boundary (ρ.comp q.ker.subtype) t g' h' :=
      congrFun (congrFun ht g') h'
    change f g h+(ρ g (d h)-d (g*h)+d g) = 0
    rw [show d g = -t g' from hd g',show d h = -t h' from hd h',
      show d (g*h) = -t (g'*h') from hd (g'*h'),he,map_neg]
    change (ρ g (t h')-t (g'*h')+t g')+(-ρ g (t h')- -t (g'*h')+-t g') = 0
    abel
  obtain ⟨b₁,hb₁⟩ := normalize_left ρ q r hr1 hr hf₀ hz₀
  let f₁ : G → G → A := fun g h => f₀ g h+boundary ρ b₁ g h
  have hf₁ : IsCocycle ρ f₁ := cocycle_add ρ hf₀ (boundary_cocycle ρ b₁)
  obtain ⟨b₂,hb₂,hb₂'⟩ := normalize_right ρ q r hr1 hr hH1 hf₁ hb₁
  let b : G → A := fun g => (d g+b₁ g)+b₂ g
  have he (g h : G) : f g h+boundary ρ b g h = f₁ g h+boundary ρ b₂ g h := by
    simp only [b,boundary_add,f₁,f₀]
    abel
  refine ⟨b,?_,?_⟩
  · intro h g hh
    exact (he h g).trans (hb₂ h g hh)
  · intro g h hh
    exact (he g h).trans (hb₂' g h hh)

end CocycleTwo



namespace CocycleTwo
open scoped Classical
variable {G Q A A₀ : Type*} [Group G] [Group Q] [AddCommGroup A] [AddCommGroup A₀]
  (ρ : G →* AddAut A) (q : G →* Q)

theorem horizontal_right_mul {f : G → G → A} (hf : IsCocycle ρ f) (hz : Horizontal q f)
    (g k h : G) (hh : q h = 1) : f g (k*h) = f g k := by
  have he := hf g k h
  rw [hz.2 k h hh,hz.2 (g*k) h hh,map_zero,zero_add,add_zero] at he
  exact he

theorem horizontal_right_eq {f : G → G → A} (hf : IsCocycle ρ f) (hz : Horizontal q f)
    (g h k : G) (heq : q h = q k) : f g h = f g k := by
  have hk : q (k⁻¹*h) = 1 := by simp [heq]
  convert horizontal_right_mul ρ q hf hz g k (k⁻¹*h) hk using 1
  group

theorem horizontal_left_eq {f : G → G → A} (hf : IsCocycle ρ f) (hz : Horizontal q f)
    (g h k : G) (heq : q g = q h) : f g k = f h k := by
  have hk : q (h⁻¹*g) = 1 := by simp [heq]
  have he := hf h (h⁻¹*g) k
  rw [hz.1 _ _ hk,hz.2 _ _ hk,map_zero,zero_add,zero_add] at he
  have hp : h*(h⁻¹*g) = g := by group
  rw [hp] at he
  rw [← he]
  apply horizontal_right_eq ρ q hf hz
  simp [hk]

theorem horizontal_fixed {f : G → G → A} (hf : IsCocycle ρ f) (hz : Horizontal q f)
    (g k h : G) (hh : q h = 1) : ρ h (f g k) = f g k := by
  rw [← left_covariant ρ q hf hz.1 h g k hh]
  apply horizontal_left_eq ρ q hf hz
  simp [hh]

variable (ρ₀ : Q →* AddAut A₀) (e : A₀ →+ A)
  (hei : Function.Injective e)
  (hee : ∀ g x, e (ρ₀ (q g) x) = ρ g (e x))
  (hes : ∀ a : A, (∀ h : G, q h = 1 → ρ h a = a) → ∃ x : A₀, e x = a)

include hei hee hes in
/-- Horizontal cocycles descend to any identification of the kernel-fixed
coefficient group with a quotient representation. -/
theorem descend_cocycle (hq : Function.Surjective q)
    {f : G → G → A} (hf : IsCocycle ρ f) (hz : Horizontal q f) :
    ∃ f₀ : Q → Q → A₀, IsCocycle ρ₀ f₀ ∧ ∀ g h, e (f₀ (q g) (q h)) = f g h := by
  obtain ⟨r,hr1,hr⟩ := exists_section q hq
  have hex (x y : Q) : ∃ a : A₀, e a = f (r x) (r y) :=
    hes _ (horizontal_fixed ρ q hf hz (r x) (r y))
  let f₀ : Q → Q → A₀ := fun x y => (hex x y).choose
  have he (g h : G) : e (f₀ (q g) (q h)) = f g h := by
    change e (hex (q g) (q h)).choose = _
    rw [(hex (q g) (q h)).choose_spec]
    exact (horizontal_left_eq ρ q hf hz _ _ _ (hr (q g))).trans
      (horizontal_right_eq ρ q hf hz _ _ _ (hr (q h)))
  refine ⟨f₀,?_,he⟩
  intro x y z
  obtain ⟨g,rfl⟩ := hq x
  obtain ⟨h,rfl⟩ := hq y
  obtain ⟨k,rfl⟩ := hq z
  apply hei
  rw [map_add,map_add,hee,he,← map_mul,← map_mul,he,he,he]
  exact hf g h k

/-- A zero-boundary (difference of translates of one element) has zero
second boundary. -/
theorem boundary_difference (a : A) (g h : G) :
    boundary ρ (fun g => ρ g a-a) g h = 0 := by
  simp only [boundary,map_sub,act_mul]
  abel

include hei hee hes in
/-- When kernel H1 vanishes, a descended cocycle which is a coboundary
upstairs is already a coboundary downstairs. -/
theorem descend_coboundary (hq : Function.Surjective q)
    (hH1 : VanishingH1 (ρ.comp q.ker.subtype))
    {f : G → G → A} (hz : Horizontal q f) (hb : IsCoboundary ρ f)
    {f₀ : Q → Q → A₀} (he : ∀ g h, e (f₀ (q g) (q h)) = f g h) :
    IsCoboundary ρ₀ f₀ := by
  obtain ⟨b,hb⟩ := hb
  have hb' (g h : G) : f g h = boundary ρ b g h := congrFun (congrFun hb g) h
  have hc : IsCocycleOne (ρ.comp q.ker.subtype) (fun h : q.ker => b h) := by
    intro g h
    have he₁ := hb' g h
    rw [hz.1 g _ g.property] at he₁
    change 0 = ρ g (b h)-b (g*h)+b g at he₁
    exact (eq_of_sub_eq_zero (show b (g*h)-(ρ g (b h)+b g) = 0 by
      calc
        _ = -(ρ g (b h)-b (g*h)+b g) := by abel
        _ = 0 := by rw [← he₁,neg_zero]))
  obtain ⟨a,ha⟩ := hH1 _ hc
  let c : G → A := fun g => b g-(ρ g a-a)
  have ch (h : G) (hh : q h = 1) : c h = 0 := by
    have he := ha ⟨h,hh⟩
    change ρ h a-a = b h at he
    simp [c,he]
  have cb (g h : G) : boundary ρ c g h = f g h := by
    rw [hb' g h]
    change (ρ g (b h-(ρ h a-a))-(b (g*h)-(ρ (g*h) a-a))+(b g-(ρ g a-a))) = _
    simp only [map_sub,act_mul,boundary]
    abel
  have cr (g h : G) (hh : q h = 1) : c (g*h) = c g := by
    have he := cb g h
    rw [hz.2 g h hh,boundary,ch h hh,map_zero,zero_sub] at he
    exact (sub_eq_zero.mp (show c g-c (g*h) = 0 by convert he using 1 <;> abel)).symm
  have ce (g h : G) (heq : q g = q h) : c g = c h := by
    have hk : q (h⁻¹*g) = 1 := by simp [heq]
    convert cr h (h⁻¹*g) hk using 1
    group
  have cf (g h : G) (hh : q h = 1) : ρ h (c g) = c g := by
    have he := cb h g
    rw [hz.1 h g hh,boundary,ch h hh,add_zero,ce (h*g) g (by simp [hh])] at he
    exact sub_eq_zero.mp he
  obtain ⟨r,hr1,hr⟩ := exists_section q hq
  have hex (x : Q) : ∃ a : A₀, e a = c (r x) := hes _ (cf (r x))
  let c₀ : Q → A₀ := fun x => (hex x).choose
  have ec (g : G) : e (c₀ (q g)) = c g := by
    exact (hex (q g)).choose_spec.trans (ce _ _ (hr (q g)))
  refine ⟨c₀,?_⟩
  funext x y
  obtain ⟨g,rfl⟩ := hq x
  obtain ⟨h,rfl⟩ := hq y
  apply hei
  rw [he,boundary,map_add,map_sub,hee,ec,← map_mul,ec,ec]
  exact (cb g h).symm

end CocycleTwo


namespace CocycleTwo
open scoped Classical
variable {G Q A B A₀ B₀ : Type*} [Group G] [Group Q]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup A₀] [AddCommGroup B₀]
  (ρ : G →* AddAut A) (τ : G →* AddAut B) (p : A →+ B)
  (hp : ∀ g a, p (ρ g a) = τ g (p a))

include hp in
theorem map_cocycle {f : G → G → A} (hf : IsCocycle ρ f) :
    IsCocycle τ (fun g h => p (f g h)) := by
  intro g h k
  rw [← hp,← map_add,← map_add,hf]

include hp in
theorem map_boundary (b : G → A) (g h : G) :
    p (boundary ρ b g h) = boundary τ (fun g => p (b g)) g h := by
  simp only [boundary,map_add,map_sub,hp]

include hp in
theorem map_coboundary {f : G → G → A} (hf : IsCoboundary ρ f) :
    IsCoboundary τ (fun g h => p (f g h)) := by
  obtain ⟨b,rfl⟩ := hf
  exact ⟨fun g => p (b g),funext fun g => funext fun h => map_boundary ρ τ p hp b g h⟩

theorem coboundary_add {f t : G → G → A}
    (hf : IsCoboundary ρ f) (ht : IsCoboundary ρ t) :
    IsCoboundary ρ (fun g h => f g h+t g h) := by
  obtain ⟨b,rfl⟩ := hf
  obtain ⟨c,rfl⟩ := ht
  exact ⟨fun g => b g+c g,funext fun g => funext fun h => (boundary_add ρ b c g h).symm⟩

theorem coboundary_sub_boundary {f : G → G → A} (hf : IsCoboundary ρ f) (c : G → A) :
    IsCoboundary ρ (fun g h => f g h-boundary ρ c g h) := by
  obtain ⟨b,rfl⟩ := hf
  refine ⟨fun g => b g-c g,?_⟩
  funext g h
  simp only [boundary,map_sub]
  abel

/-- Injectivity on H2, stated directly with cocycles and coboundaries. -/
def ReflectsBoundaries : Prop :=
  ∀ f : G → G → A, IsCocycle ρ f → IsCoboundary τ (fun g h => p (f g h)) → IsCoboundary ρ f

include hp in
/-- Injectivity on H2 descends through a normal subgroup when H1 of both
coefficient modules vanishes. No spectral sequence is required. -/
theorem injective_of_kernel_quotient (q : G →* Q) (hq : Function.Surjective q)
    (ρ₀ : Q →* AddAut A₀) (τ₀ : Q →* AddAut B₀) (p₀ : A₀ →+ B₀)
    (eA : A₀ →+ A) (eB : B₀ →+ B)
    (heiA : Function.Injective eA) (heiB : Function.Injective eB)
    (heeA : ∀ g x, eA (ρ₀ (q g) x) = ρ g (eA x))
    (heeB : ∀ g x, eB (τ₀ (q g) x) = τ g (eB x))
    (hesA : ∀ a : A, (∀ h : G, q h = 1 → ρ h a = a) → ∃ x : A₀, eA x = a)
    (hesB : ∀ a : B, (∀ h : G, q h = 1 → τ h a = a) → ∃ x : B₀, eB x = a)
    (hcomm : ∀ x, p (eA x) = eB (p₀ x))
    (hH1A : VanishingH1 (ρ.comp q.ker.subtype))
    (hH1B : VanishingH1 (τ.comp q.ker.subtype))
    (hH2ker : ReflectsBoundaries (ρ.comp q.ker.subtype) (τ.comp q.ker.subtype) p)
    (hH2quot : ReflectsBoundaries ρ₀ τ₀ p₀) : ReflectsBoundaries ρ τ p := by
  intro f hf hb
  have hres : IsCoboundary (ρ.comp q.ker.subtype) (fun g h : q.ker => f g h) := by
    apply hH2ker
    · intro g h k
      exact hf g h k
    · obtain ⟨b,hb⟩ := hb
      refine ⟨fun g : q.ker => b g,?_⟩
      funext g h
      exact congrFun (congrFun hb g) h
  obtain ⟨d,hd⟩ := exists_horizontal ρ q hq hH1A hf hres
  let f' : G → G → A := fun g h => f g h+boundary ρ d g h
  have hf' : IsCocycle ρ f' := cocycle_add ρ hf (boundary_cocycle ρ d)
  have hb' : IsCoboundary τ (fun g h => p (f' g h)) := by
    have hb₂ : IsCoboundary τ (fun g h => p (boundary ρ d g h)) :=
      map_coboundary ρ τ p hp ⟨d,rfl⟩
    simpa only [f',map_add] using coboundary_add τ hb hb₂
  obtain ⟨f₀,hf₀,he₀⟩ := descend_cocycle ρ q ρ₀ eA heiA heeA hesA hq hf' hd
  have hzB : Horizontal q (fun g h => p (f' g h)) := by
    constructor
    · intro h g hh
      exact (congrArg p (hd.1 h g hh)).trans (map_zero p)
    · intro g h hh
      exact (congrArg p (hd.2 g h hh)).trans (map_zero p)
  have heB (g h : G) : eB (p₀ (f₀ (q g) (q h))) = p (f' g h) := by
    rw [← hcomm,he₀]
  have hB₀ : IsCoboundary τ₀ (fun g h => p₀ (f₀ g h)) :=
    descend_coboundary τ q τ₀ eB heiB heeB hesB hq hH1B hzB hb' heB
  obtain ⟨a,ha⟩ := hH2quot f₀ hf₀ hB₀
  have hc : IsCoboundary ρ f' := by
    refine ⟨fun g => eA (a (q g)),?_⟩
    funext g h
    rw [← he₀,ha,boundary,map_add,map_sub,heeA,← map_mul]
    rfl
  have hc' := coboundary_sub_boundary ρ hc d
  simpa only [f',add_sub_cancel_right] using hc'

end CocycleTwo


namespace CocycleTwo
open scoped Classical
variable {G H A B : Type*} [Group G] [Group H] [AddCommGroup A] [AddCommGroup B]
  (ρ : G →* AddAut A) (τ : G →* AddAut B) (p : A →+ B) (e : H ≃* G)

theorem VanishingH1.comp_equiv (hρ : VanishingH1 ρ) : VanishingH1 (ρ.comp e.toMonoidHom) := by
  intro b hb
  have hc : IsCocycleOne ρ (fun g => b (e.symm g)) := by
    intro g h
    simpa only [map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
      using hb (e.symm g) (e.symm h)
  obtain ⟨a,ha⟩ := hρ _ hc
  refine ⟨a,?_⟩
  intro h
  simpa only [MulEquiv.symm_apply_apply] using ha (e h)

theorem ReflectsBoundaries.comp_equiv (hρ : ReflectsBoundaries ρ τ p) :
    ReflectsBoundaries (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom) p := by
  intro f hf hb
  let f' : G → G → A := fun g h => f (e.symm g) (e.symm h)
  have hf' : IsCocycle ρ f' := by
    intro g h k
    simpa only [f',map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply]
      using hf (e.symm g) (e.symm h) (e.symm k)
  have hb' : IsCoboundary τ (fun g h => p (f' g h)) := by
    obtain ⟨b,hb⟩ := hb
    refine ⟨fun g => b (e.symm g),?_⟩
    funext g h
    have he := congrFun (congrFun hb (e.symm g)) (e.symm h)
    simpa only [f',boundary,map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.apply_symm_apply] using he
  obtain ⟨b,hb⟩ := hρ f' hf' hb'
  refine ⟨fun h => b (e h),?_⟩
  funext g h
  have he := congrFun (congrFun hb (e g)) (e h)
  simpa only [f',boundary,map_mul,MulEquiv.symm_apply_apply] using he

end CocycleTwo


namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E]

theorem field_hilbert90 : VanishingH1 (fieldAction K E) := by
  intro b hb
  have hm : groupCohomology.IsMulCocycle₁ (fun g : Gal(E/K) => (b g).toMul) := by
    intro g h
    exact congrArg Additive.toMul (hb g h)
  obtain ⟨a,ha⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hm
  refine ⟨Additive.ofMul a,?_⟩
  intro g
  exact congrArg Additive.ofMul (ha g)

variable (M : IntermediateField K E) [Normal K M]

noncomputable def kernelAutEquiv : (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker ≃* Gal(E/M) :=
  (MulEquiv.subgroupCongr M.restrictNormalHom_ker).trans (IntermediateField.fixingSubgroupEquiv M)

@[simp] theorem kernelAutEquiv_apply (g : (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker) (x : E) :
    kernelAutEquiv K E M g x = g.1 x := rfl

@[simp] theorem kernelAutEquiv_symm_apply (g : Gal(E/M)) (x : E) :
    ((kernelAutEquiv K E M).symm g).1 x = g x := rfl

variable [NumberField M]

theorem kernel_field_hilbert90 :
    VanishingH1 ((fieldAction K E).comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker.subtype) := by
  change VanishingH1 ((fieldAction M E).comp (kernelAutEquiv K E M).toMonoidHom)
  exact VanishingH1.comp_equiv (fieldAction M E) (kernelAutEquiv K E M) (field_hilbert90 M E)

theorem kernel_ideal_hilbert90 :
    VanishingH1 ((idealAction K E).comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker.subtype) := by
  intro b hb
  exact ideal_hilbert90 K E _ b hb

variable [IsGalois M E] [IsTotallyReal M] [IsTotallyReal E]
  (σ : Gal(E/M)) (hdeg : Module.finrank M E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 M) (𝓞 E) = ⊤)

include σ hdeg hne hunram in
theorem kernel_reflects_boundaries :
    ReflectsBoundaries
      ((fieldAction K E).comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker.subtype)
      ((idealAction K E).comp (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M).ker.subtype)
      (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom := by
  change ReflectsBoundaries ((fieldAction M E).comp (kernelAutEquiv K E M).toMonoidHom)
    ((idealAction M E).comp (kernelAutEquiv K E M).toMonoidHom) _
  apply ReflectsBoundaries.comp_equiv
  intro f hf hb
  exact UnramifiedFractionalNorm.quadratic_cocycle_injective M E σ hdeg hne hunram hf hb

include hdeg hne in
theorem kernel_field_descent (a : F E)
    (ha : ∀ g : Gal(E/K), AlgEquiv.restrictNormalHom M g = 1 → fieldAction K E g a = a) :
    ∃ x : F M, fieldExtension M E x = a := by
  have haσ : fAction M E σ a = a := ha ((kernelAutEquiv K E M).symm σ).1 ((kernelAutEquiv K E M).symm σ).property
  let af : InvolutionHerbrand.plus (fAction M E σ) := ⟨a,(InvolutionHerbrand.mem_plus _ _).mpr haσ⟩
  obtain ⟨x,hx⟩ := (UnramifiedAmbiguousClasses.fieldFixed M E σ hdeg hne).surjective af
  exact ⟨x,congrArg Subtype.val hx⟩

include hdeg hne hunram in
theorem kernel_ideal_descent (a : D E)
    (ha : ∀ g : Gal(E/K), AlgEquiv.restrictNormalHom M g = 1 → idealAction K E g a = a) :
    ∃ x : D M, idealExtension M E x = a := by
  have haσ : dAction M E σ a = a := ha ((kernelAutEquiv K E M).symm σ).1 ((kernelAutEquiv K E M).symm σ).property
  let af : InvolutionHerbrand.plus (dAction M E σ) := ⟨a,(InvolutionHerbrand.mem_plus _ _).mpr haσ⟩
  obtain ⟨x,hx⟩ := (UnramifiedAmbiguousClasses.idealFixed M E σ hdeg hne hunram).surjective af
  exact ⟨x,congrArg Subtype.val hx⟩

end GaloisCocycleActions

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal E]
  (M : IntermediateField K E) [Normal K M] [NumberField M] [IsTotallyReal M]
  (σ : Gal(E/M)) (hdeg : Module.finrank M E = 2) (hne : σ ≠ 1)
  (hunram : differentIdeal (𝓞 M) (𝓞 E) = ⊤)

include σ hdeg hne hunram in
/-- H2 injectivity for a Galois extension follows from that for its normal
subfield when the remaining top step is unramified quadratic. -/
theorem quadratic_top_descent
    (hM : ReflectsBoundaries (fieldAction K M) (idealAction K M)
      (UnramifiedAmbiguousClasses.principalWhole M).toAddMonoidHom) :
    ReflectsBoundaries (fieldAction K E) (idealAction K E)
      (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom := by
  exact injective_of_kernel_quotient (fieldAction K E) (idealAction K E)
    (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom (principal_equivariant K E)
    (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
    (fieldAction K M) (idealAction K M) (UnramifiedAmbiguousClasses.principalWhole M).toAddMonoidHom
    (fieldExtension M E) (idealExtension M E)
    (fieldExtension_injective M E) (idealExtension_injective M E)
    (fieldExtension_equivariant K M E) (idealExtension_equivariant K M E)
    (kernel_field_descent K E M σ hdeg hne) (kernel_ideal_descent K E M σ hdeg hne hunram)
    (principal_extension M E)
    (kernel_field_hilbert90 K E M) (kernel_ideal_hilbert90 K E M)
    (kernel_reflects_boundaries K E M σ hdeg hne hunram) hM

end GaloisCocycleActions


namespace PGroupCentralTwo
open scoped Classical
variable (G : Type*) [Group G] [Finite G] [Nontrivial G]

theorem exists_normal_two (hG : IsPGroup 2 G) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  letI := hG.center_nontrivial
  obtain ⟨n,hn,he⟩ := (hG.to_subgroup (Subgroup.center G)).nontrivial_iff_card.mp inferInstance
  have hd : 2 ∣ Nat.card (Subgroup.center G) := by
    rw [he]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 hd
  let H := Subgroup.zpowers (s : G)
  have hcent : H ≤ Subgroup.center G := Subgroup.zpowers_le.mpr s.property
  refine ⟨H,?_,?_⟩
  · refine ⟨?_⟩
    intro n hn g
    have hc := (Subgroup.mem_center_iff.mp (hcent hn)) g
    simpa only [hc,mul_assoc,mul_inv_cancel,mul_one] using hn
  · change Nat.card (Subgroup.zpowers (s : G)) = 2
    rw [Nat.card_zpowers]
    exact (orderOf_injective (Subgroup.center G).subtype Subtype.val_injective s).trans hs

end PGroupCentralTwo

namespace UnramifiedTowerDescent
open NumberField
variable (K M E : Type*) [Field K] [Field M] [Field E] [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]

theorem different_top (h : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    differentIdeal (𝓞 M) (𝓞 E) = ⊤ ∧ differentIdeal (𝓞 K) (𝓞 M) = ⊤ := by
  have ht := differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 M) (𝓞 E)
  have h₁ : differentIdeal (𝓞 M) (𝓞 E) = ⊤ := by
    apply top_unique
    rw [← h,ht]
    exact Ideal.mul_le_right
  have h₂ : Ideal.map (algebraMap (𝓞 M) (𝓞 E)) (differentIdeal (𝓞 K) (𝓞 M)) = ⊤ := by
    apply top_unique
    rw [← h,ht]
    exact Ideal.mul_le_left
  refine ⟨h₁,?_⟩
  exact (Ideal.map_eq_top_iff (algebraMap (𝓞 M) (𝓞 E))
    (FaithfulSMul.algebraMap_injective (𝓞 M) (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp h₂

end UnramifiedTowerDescent

namespace CocycleTwo
variable {G A : Type*} [Group G] [AddCommGroup A]
theorem coboundary_subsingleton [Subsingleton G] (ρ : G →* AddAut A) (f : G → G → A) :
    IsCoboundary ρ f := by
  refine ⟨fun _ => f 1 1,?_⟩
  funext g h
  have hg : g = 1 := Subsingleton.elim _ _
  have hh : h = 1 := Subsingleton.elim _ _
  subst g h
  simp [boundary]
end CocycleTwo

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]

/-- Principal ideals reflect second-cohomology coboundaries in every finite,
totally real, everywhere-unramified Galois 2-extension. -/
theorem unramified_pgroup_reflects (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    ReflectsBoundaries (fieldAction K E) (idealAction K E)
      (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom := by
  generalize hn : Module.finrank K E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    rcases subsingleton_or_nontrivial Gal(E/K) with htriv | hnontriv
    · letI := htriv
      intro f hf hb
      exact coboundary_subsingleton _ _
    · letI := hnontriv
      obtain ⟨H,hH,hcard⟩ := PGroupCentralTwo.exists_normal_two Gal(E/K) hG
      letI := hH
      let M := IntermediateField.fixedField H
      letI : NumberField M := NumberField.of_module_finite ℚ M
      letI : IsTotallyReal M := IsTotallyReal.of_algebra M E
      have hdeg : Module.finrank M E = 2 := by
        exact (IntermediateField.finrank_fixedField_eq_card H).trans hcard
      have hMlt : Module.finrank K M < n := by
        have he := Module.finrank_mul_finrank K M E
        rw [hdeg,hn] at he
        have hp : 0 < Module.finrank K M := Module.finrank_pos
        omega
      have hGM : IsPGroup 2 Gal(M/K) :=
        hG.of_surjective (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
      have hu := UnramifiedTowerDescent.different_top K M E hunram
      have hM := ih (Module.finrank K M) hMlt M hGM hu.2 rfl
      have hc : Nat.card Gal(E/M) = 2 := (IsGalois.card_aut_eq_finrank M E).trans hdeg
      letI : Nontrivial Gal(E/M) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨σ,hσ⟩ := exists_ne (1 : Gal(E/M))
      exact quadratic_top_descent K E M σ hdeg hσ hu.1 hM

end GaloisCocycleActions

namespace FractionalGalois
open NumberField
open scoped Classical nonZeroDivisors
variable (E : Type*) [Field E] [NumberField E]

/-- Squaring is injective on nonzero fractional ideals; cancellation of
`I+J` proves this without prime factorization. -/
theorem square_injective : Function.Injective (fun I : Ideals E => I*I) := by
  intro I J h
  apply Units.ext
  have hs : I.1*I.1 = J.1*J.1 := congrArg Units.val h
  have hsum : I.1+J.1 ≠ 0 := by
    intro hz
    have hle : I.1 ≤ I.1+J.1 := le_add_of_nonneg_right (zero_le _)
    rw [hz] at hle
    exact I.ne_zero (le_antisymm hle (zero_le _))
  apply mul_left_cancel₀ hsum
  calc
    (I.1+J.1)*I.1 = I.1*I.1+I.1*J.1 := by ring
    _ = J.1*J.1+I.1*J.1 := by rw [hs]
    _ = (I.1+J.1)*J.1 := by ring

theorem double_injective : Function.Injective (fun I : Additive (Ideals E) => I+I) := by
  intro I J h
  apply Additive.toMul.injective
  exact square_injective E (congrArg Additive.toMul h)

end FractionalGalois


/-! Elementary functoriality and invariants of abelian groups modulo two. -/
namespace ModTwo
open scoped Classical
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

abbrev V (A : Type*) [AddCommGroup A] := ModN A 2
abbrev mk : A →+ V A := ModN.mkQ 2

theorem mk_surjective : Function.Surjective (mk (A := A)) :=
  (LinearMap.range (LinearMap.lsmul ℤ A (2 : ℤ))).mkQ_surjective

theorem mk_eq_zero (a : A) : mk a = 0 ↔ ∃ b : A, b+b = a := by
  change Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change (∃ b : A, (2 : ℤ) • b = a) ↔ _
  simp only [two_smul]

theorem mk_double (a : A) : mk (a+a) = 0 := (mk_eq_zero _).mpr ⟨a,rfl⟩

theorem double_zero (a : V A) : a+a = 0 := by
  obtain ⟨x,rfl⟩ := mk_surjective a
  rw [← map_add,mk_double]

noncomputable def map (p : A →+ B) : V A →ₗ[ZMod 2] V B :=
  (ModN.liftEquiv' (n := 2)).symm ⟨mk.comp p,fun a => by
    change 2 • mk (p a) = 0
    simpa only [two_nsmul] using double_zero (mk (p a))⟩

@[simp] theorem map_mk (p : A →+ B) (a : A) : map p (mk a) = mk (p a) := rfl

variable {G : Type*} [Group G] (ρ : G →* AddAut A)

def fixed : Submodule (ZMod 2) (V A) where
  carrier := {a | ∀ g, map (ρ g).toAddMonoidHom a = a}
  zero_mem' g := map_zero _
  add_mem' ha hb g := by rw [map_add,ha g,hb g]
  smul_mem' c a ha g := by rw [map_smul,ha g]

@[simp] theorem mem_fixed (v : V A) : v ∈ fixed ρ ↔ ∀ g, map (ρ g).toAddMonoidHom v = v := Iff.rfl

def pairs : AddSubgroup (A × (G → A)) where
  carrier := {x | ∀ g, ρ g x.1-x.1 = x.2 g+x.2 g}
  zero_mem' g := by simp
  add_mem' := by
    intro x y hx hy g
    change ρ g (x.1+y.1)-(x.1+y.1) = (x.2 g+y.2 g)+(x.2 g+y.2 g)
    rw [map_add]
    calc
      _ = (ρ g x.1-x.1)+(ρ g y.1-y.1) := by abel
      _ = _ := by rw [hx,hy]; abel
  neg_mem' := by
    intro x hx g
    change ρ g (-x.1)- -x.1 = -x.2 g+ -x.2 g
    rw [map_neg]
    calc
      _ = -(ρ g x.1-x.1) := by abel
      _ = _ := by rw [hx]; abel

noncomputable def projection : pairs ρ →+ fixed ρ where
  toFun x := ⟨mk x.1.1,fun g => by
    rw [map_mk]
    change mk (ρ g x.1.1) = mk x.1.1
    apply sub_eq_zero.mp
    rw [← map_sub,x.property g,mk_double]⟩
  map_zero' := Subtype.ext (map_zero mk)
  map_add' x y := Subtype.ext (map_add mk x.1.1 y.1.1)

theorem projection_surjective : Function.Surjective (projection ρ) := by
  intro v
  obtain ⟨a,ha⟩ := mk_surjective v.1
  have hex (g : G) : ∃ b : A, b+b = ρ g a-a := by
    apply (mk_eq_zero _).mp
    have hp := v.property g
    rw [← ha,map_mk] at hp
    change mk (ρ g a) = mk a at hp
    rw [map_sub,hp,sub_self]
  choose b hb using hex
  exact ⟨⟨(a,b),fun g => (hb g).symm⟩,Subtype.ext ha⟩

end ModTwo

namespace KummerConnecting
open scoped Classical
open CocycleTwo
variable {G A : Type} [Group G] [AddCommGroup A]
  (ρ : G →* AddAut A) (i : ZMod 2 →+ A)
  (hi : Function.Injective i) (hfix : ∀ g t, ρ g (i t) = i t)
  (hker : ∀ a : A, a+a = 0 → ∃ t : ZMod 2, i t = a)

noncomputable abbrev H2 (G : Type) [Group G] := groupCohomology (Rep.trivial (ZMod 2) G (ZMod 2)) 2
noncomputable abbrev Z2 (G : Type) [Group G] := groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) G (ZMod 2))

theorem double_pair_boundary (x : ModTwo.pairs ρ) (g h : G) :
    boundary ρ x.1.2 g h+boundary ρ x.1.2 g h = 0 := by
  rw [← boundary_add]
  have he : (fun g => x.1.2 g+x.1.2 g) = (fun g => ρ g x.1.1-x.1.1) :=
    funext fun g => (x.property g).symm
  rw [he,boundary_difference]

noncomputable def value (x : ModTwo.pairs ρ) (g h : G) : ZMod 2 :=
  (hker _ (double_pair_boundary ρ x g h)).choose

@[simp] theorem i_value (x : ModTwo.pairs ρ) (g h : G) :
    i (value ρ i hker x g h) = boundary ρ x.1.2 g h :=
  (hker _ (double_pair_boundary ρ x g h)).choose_spec

include hi hfix in
theorem value_cocycle (x : ModTwo.pairs ρ) :
    (fun gh : G × G => value ρ i hker x gh.1 gh.2) ∈ Z2 G := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  apply hi
  change i (value ρ i hker x (g*h) k+value ρ i hker x g h) =
    i (value ρ i hker x h k+value ρ i hker x g (h*k))
  rw [map_add,map_add,i_value,i_value,i_value,i_value]
  have hf := boundary_cocycle ρ x.1.2 g h k
  rw [← i_value ρ i hker x h k,hfix,i_value] at hf
  exact (add_comm _ _).trans hf.symm

noncomputable def pairCocycle : ModTwo.pairs ρ →+ Z2 G where
  toFun x := ⟨fun gh => value ρ i hker x gh.1 gh.2,value_cocycle ρ i hi hfix hker x⟩
  map_zero' := by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker 0 gh.1 gh.2) = i 0
    rw [i_value,map_zero]
    simp [boundary]
  map_add' x y := by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker (x+y) gh.1 gh.2) =
      i (value ρ i hker x gh.1 gh.2+value ρ i hker y gh.1 gh.2)
    rw [map_add,i_value,i_value,i_value]
    exact boundary_add ρ x.1.2 y.1.2 gh.1 gh.2

noncomputable def pairClass : ModTwo.pairs ρ →+ H2 G :=
  (groupCohomology.H2π (Rep.trivial (ZMod 2) G (ZMod 2))).hom.toAddMonoidHom.comp
    (pairCocycle ρ i hi hfix hker)

include hi hfix in
/-- The connecting class is zero when the initial squareclass is zero. -/
theorem pairClass_zero_of_projection_zero (x : ModTwo.pairs ρ)
    (hx : ModTwo.projection ρ x = 0) : pairClass ρ i hi hfix hker x = 0 := by
  have hx₀ : ModTwo.mk x.1.1 = 0 := congrArg Subtype.val hx
  obtain ⟨z,hz⟩ := (ModTwo.mk_eq_zero _).mp hx₀
  have ht (g : G) : ∃ t : ZMod 2, i t = x.1.2 g-(ρ g z-z) := by
    apply hker
    have hxg := x.property g
    rw [← hz,map_add] at hxg
    calc
      _ = (x.1.2 g+x.1.2 g)-((ρ g z+ρ g z)-(z+z)) := by abel
      _ = 0 := by rw [← hxg,sub_self]
  choose t ht using ht
  apply (groupCohomology.H2π_eq_zero_iff _).mpr
  refine ⟨t,?_⟩
  funext gh
  apply hi
  change i (t gh.2-t (gh.1*gh.2)+t gh.1) = i (value ρ i hker x gh.1 gh.2)
  rw [map_add,map_sub,i_value,ht,ht,ht]
  have hfg : ρ gh.1 (x.1.2 gh.2-(ρ gh.2 z-z)) = x.1.2 gh.2-(ρ gh.2 z-z) := by
    rw [← ht,hfix]
  rw [← hfg]
  simp only [map_sub,act_mul,boundary]
  abel

private noncomputable def factor {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (p : X →ₗ[ℤ] Y) (hp : Function.Surjective p) (f : X →ₗ[ℤ] Z) (h : p.ker ≤ f.ker) : Y →ₗ[ℤ] Z :=
  (p.ker.liftQ f h).comp (p.quotKerEquivOfSurjective hp).symm.toLinearMap

private theorem factor_apply {X Y Z : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (p : X →ₗ[ℤ] Y) (hp : Function.Surjective p) (f : X →ₗ[ℤ] Z) (h : p.ker ≤ f.ker) (x : X) :
    factor p hp f h (p x) = f x := by
  change p.ker.liftQ f h ((p.quotKerEquivOfSurjective hp).symm (p x)) = _
  rw [← p.quotKerEquivOfSurjective_apply_mk hp x,LinearEquiv.symm_apply_apply]
  rfl

private theorem ker_projection_le :
    (ModTwo.projection ρ).toIntLinearMap.ker ≤ (pairClass ρ i hi hfix hker).toIntLinearMap.ker := by
  intro x hx
  exact pairClass_zero_of_projection_zero ρ i hi hfix hker x hx

/-- The Kummer connecting map from invariant squareclasses to H2 with
coefficients F2. -/
noncomputable def connecting : ModTwo.fixed ρ →ₗ[ZMod 2] H2 G :=
  (factor (ModTwo.projection ρ).toIntLinearMap (ModTwo.projection_surjective ρ)
    (pairClass ρ i hi hfix hker).toIntLinearMap (ker_projection_le ρ i hi hfix hker)).toAddMonoidHom.toZModLinearMap 2

@[simp] theorem connecting_projection (x : ModTwo.pairs ρ) :
    connecting ρ i hi hfix hker (ModTwo.projection ρ x) = pairClass ρ i hi hfix hker x :=
  factor_apply (ModTwo.projection ρ).toIntLinearMap (ModTwo.projection_surjective ρ)
    (pairClass ρ i hi hfix hker).toIntLinearMap (ker_projection_le ρ i hi hfix hker) x

include hi hfix in
/-- If field H1 vanishes and all F2-valued 2-cocycles become boundaries in
A, the Kummer connecting map is onto. -/
theorem connecting_surjective (hH1 : VanishingH1 ρ)
    (hH2 : ∀ f : Z2 G, IsCoboundary ρ (fun g h => i (f (g,h)))) :
    Function.Surjective (connecting ρ i hi hfix hker) := by
  intro y
  induction y using groupCohomology.H2_induction_on with | h f =>
  obtain ⟨b,hb⟩ := hH2 f
  have hb' (g h : G) : i (f (g,h)) = boundary ρ b g h := congrFun (congrFun hb g) h
  have hc : IsCocycleOne ρ (fun g => b g+b g) := by
    intro g h
    have hδ : boundary ρ (fun g => b g+b g) g h = 0 := by
      rw [boundary_add,← hb',← map_add,CharTwo.add_self_eq_zero,map_zero]
    change ρ g (b h+b h)-(b (g*h)+b (g*h))+(b g+b g) = 0 at hδ
    have he : (ρ g (b h+b h)+(b g+b g))-(b (g*h)+b (g*h)) = 0 := by
      rw [← sub_add_eq_add_sub]
      exact hδ
    exact (sub_eq_zero.mp he).symm
  obtain ⟨a,ha⟩ := hH1 _ hc
  let x : ModTwo.pairs ρ := ⟨(a,b),ha⟩
  have hx : pairCocycle ρ i hi hfix hker x = f := by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker x gh.1 gh.2) = i (f (gh.1,gh.2))
    rw [i_value,hb']
  refine ⟨ModTwo.projection ρ x,?_⟩
  rw [connecting_projection]
  change groupCohomology.H2π _ (pairCocycle ρ i hi hfix hker x) = _
  rw [hx]

include hi hfix in
/-- Classes represented by genuinely invariant elements are in the kernel
of the connecting map. -/
theorem connecting_invariant (a : A) (ha : ∀ g, ρ g a = a)
    (v : ModTwo.fixed ρ) (hv : v.1 = ModTwo.mk a) :
    connecting ρ i hi hfix hker v = 0 := by
  let x : ModTwo.pairs ρ := ⟨(a,fun _ => 0),fun g => by simp [ha]⟩
  have hx : ModTwo.projection ρ x = v := Subtype.ext hv.symm
  rw [← hx,connecting_projection]
  have hcx : pairCocycle ρ i hi hfix hker x = 0 := by
    apply Subtype.ext
    funext gh
    apply hi
    change i (value ρ i hker x gh.1 gh.2) = i 0
    rw [i_value,map_zero]
    simp [x,boundary]
  change groupCohomology.H2π _ (pairCocycle ρ i hi hfix hker x) = 0
  rw [hcx,map_zero]

end KummerConnecting



namespace FieldKummerConnecting
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo
open scoped Classical nonZeroDivisors
variable (E : Type) [Field E] [NumberField E]

noncomputable def sign : ZMod 2 →+ F E where
  toFun t := if t = 0 then 0 else Additive.ofMul (-1 : Eˣ)
  map_zero' := by simp
  map_add' a b := by
    fin_cases a <;> fin_cases b <;> norm_num
    change (if (1+1 : ZMod 2) = 0 then (0 : F E) else Additive.ofMul (-1 : Eˣ)) =
      Additive.ofMul (-1 : Eˣ)+Additive.ofMul (-1 : Eˣ)
    rw [show (1+1 : ZMod 2) = 0 by decide,if_pos rfl]
    change Additive.ofMul (1 : Eˣ) = Additive.ofMul ((-1 : Eˣ)*(-1))
    simp

@[simp] theorem sign_zero : sign E 0 = 0 := map_zero _
@[simp] theorem sign_one : sign E 1 = Additive.ofMul (-1 : Eˣ) := by simp [sign]

theorem sign_injective : Function.Injective (sign E) := by
  intro a b h
  fin_cases a <;> fin_cases b
  · rfl
  · have he := congrArg (fun a : F E => (a.toMul : E)) h
    norm_num [sign] at he
  · have he := congrArg (fun a : F E => (a.toMul : E)) h
    norm_num [sign] at he
  · rfl

theorem sign_range (a : F E) (ha : a+a = 0) : ∃ t : ZMod 2, sign E t = a := by
  have hs : (a.toMul : E)^2 = (1 : E)^2 := by
    have he := congrArg (fun a : F E => (a.toMul : E)) ha
    simpa only [pow_two,mul_one] using he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · refine ⟨0,?_⟩
    rw [sign_zero]
    apply Additive.toMul.injective
    exact Units.ext h.symm
  · refine ⟨1,?_⟩
    rw [sign_one]
    apply Additive.toMul.injective
    exact Units.ext h.symm

theorem principal_sign (t : ZMod 2) : UnramifiedAmbiguousClasses.principalWhole E (sign E t) = 0 := by
  fin_cases t
  · simp
  · change UnramifiedAmbiguousClasses.principalWhole E (sign E (1 : ZMod 2)) = 0
    rw [sign_one]
    change toPrincipalIdeal (𝓞 E) E (-1 : Eˣ) = 1
    apply (principal_eq_one_iff E _).mpr
    refine ⟨(-1 : (𝓞 E)ˣ),?_⟩
    apply Units.ext
    simp [integerUnits]

variable (K : Type) [Field K] [NumberField K] [Algebra K E]

theorem sign_fixed (g : Gal(E/K)) (t : ZMod 2) :
    GaloisCocycleActions.fieldAction K E g (sign E t) = sign E t := by
  fin_cases t
  · simp
  · change GaloisCocycleActions.fieldAction K E g (sign E (1 : ZMod 2)) = sign E 1
    rw [sign_one]
    apply Additive.toMul.injective
    apply Units.ext
    change g (-1 : E) = -1
    simp

noncomputable def connecting : ModTwo.fixed (GaloisCocycleActions.fieldAction K E) →ₗ[ZMod 2]
    KummerConnecting.H2 Gal(E/K) :=
  KummerConnecting.connecting (GaloisCocycleActions.fieldAction K E) (sign E)
    (sign_injective E) (sign_fixed E K) (sign_range E)

variable [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]

/-- The invariant squareclasses map onto H2 of the Galois group with F2
coefficients in an unramified totally real Galois 2-extension. -/
theorem connecting_surjective (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) : Function.Surjective (connecting E K) := by
  apply KummerConnecting.connecting_surjective _ _ _ _ _ (GaloisCocycleActions.field_hilbert90 K E)
  intro f
  apply GaloisCocycleActions.unramified_pgroup_reflects K E hG hunram
  · intro g h k
    change GaloisCocycleActions.fieldAction K E g (sign E (f (h,k)))+sign E (f (g,h*k)) =
      sign E (f (g,h))+sign E (f (g*h,k))
    rw [sign_fixed,← map_add (sign E),← map_add (sign E)]
    apply congrArg (sign E)
    have he := (groupCohomology.mem_cocycles₂_iff f).mp f.property g h k
    exact he.symm.trans (add_comm _ _)
  · refine ⟨fun _ => 0,?_⟩
    funext g h
    exact (principal_sign E _).trans (by simp [boundary])

end FieldKummerConnecting

namespace FractionalGalois
open NumberField
open scoped Classical nonZeroDivisors
variable (K M E : Type*) [Field K] [Field M] [Field E] [NumberField K] [NumberField M] [NumberField E]
  [Algebra K M] [Algebra M E] [Algebra K E] [IsScalarTower K M E]

theorem extend_trans (I : Ideals K) : extend M E (extend K M I) = extend K E I := by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change ((FractionalIdeal.extendedHomₐ E (𝓞 E) (FractionalIdeal.extendedHomₐ M (𝓞 M) I.1)) :
    Submodule (𝓞 E) E) = (FractionalIdeal.extendedHomₐ E (𝓞 E) I.1 : Submodule (𝓞 E) E)
  rw [FractionalIdeal.coe_extendedHomₐ_eq_span,FractionalIdeal.coe_extendedHomₐ_eq_span]
  have hI : ((FractionalIdeal.extendedHomₐ M (𝓞 M) I.1) : Set M) =
      (Submodule.span (𝓞 M) (algebraMap K M '' (I.1 : Set K)) : Set M) :=
    congrArg (fun p : Submodule (𝓞 M) M => (p : Set M)) (FractionalIdeal.coe_extendedHomₐ_eq_span M (𝓞 M) I.1)
  rw [hI]
  let f : M →ₗ[𝓞 M] E := (IsScalarTower.toAlgHom (𝓞 M) M E).toLinearMap
  change Submodule.span (𝓞 E) (f '' (Submodule.span (𝓞 M) (algebraMap K M '' (I.1 : Set K)) : Set M)) = _
  rw [← Submodule.map_coe,Submodule.map_span,Submodule.span_span_of_tower,Set.image_image]
  congr 1
  have he : (fun x => f (algebraMap K M x)) = algebraMap K E := by
    funext x
    exact (IsScalarTower.algebraMap_apply K M E x).symm
  rw [he]

/-- Extension is onto when the field algebra map is onto. -/
theorem extend_surjective_of_surjective (ha : Function.Surjective (algebraMap K E)) :
    Function.Surjective (extend K E) := by
  intro I
  let V := UnramifiedIdealDescent.contractionModule K E I.1
  have hV : IsFractional (𝓞 K)⁰ V := by
    obtain ⟨d,hd,hI⟩ := I.1.isFractional
    obtain ⟨r,hr⟩ := ha (d : E)
    have hint : IsIntegral ℤ r :=
      (isIntegral_algebraMap_iff (R := ℤ) (algebraMap K E).injective).mp (hr ▸ d.property)
    let r₀ : 𝓞 K := ⟨r,hint⟩
    have hr0 : r₀ ≠ 0 := by
      intro hz
      apply mem_nonZeroDivisors_iff_ne_zero.mp hd
      apply RingOfIntegers.coe_injective
      have hrz : r = 0 := congrArg (fun z : 𝓞 K => (z : K)) hz
      change (d : E) = 0
      rw [← hr,hrz,map_zero]
    refine ⟨r₀,mem_nonZeroDivisors_iff_ne_zero.mpr hr0,?_⟩
    intro x hx
    obtain ⟨b,hb⟩ := hI (algebraMap K E x) hx
    have he : algebraMap K E (r*x) = (b : E) := by
      change (b : E) = (d : E)*algebraMap K E x at hb
      rw [map_mul,hr,hb]
    have hint' : IsIntegral ℤ (r*x) :=
      (isIntegral_algebraMap_iff (R := ℤ) (algebraMap K E).injective).mp (he ▸ b.property)
    exact ⟨⟨r*x,hint'⟩,rfl⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨V,hV⟩
  have he : FractionalIdeal.extendedHomₐ E (𝓞 E) J = I.1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (FractionalIdeal.extendedHomₐ E (𝓞 E) J : Submodule (𝓞 E) E) = I.1.coeToSubmodule
    rw [FractionalIdeal.coe_extendedHomₐ_eq_span]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,rfl⟩
      exact hx
    · intro x hx
      obtain ⟨y,rfl⟩ := ha x
      exact Submodule.subset_span ⟨y,hx,rfl⟩
  have hJ : J ≠ 0 := by
    intro hz
    rw [hz,map_zero] at he
    exact I.ne_zero he.symm
  refine ⟨Units.mk0 J hJ,?_⟩
  exact Units.ext he

end FractionalGalois

namespace GaloisCocycleActions
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]

/-- Every Galois-invariant fractional ideal descends in an everywhere
unramified Galois 2-extension. -/
theorem unramified_ideal_descent (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) (I : D E)
    (hI : ∀ g : Gal(E/K), idealAction K E g I = I) :
    ∃ J : D K, idealExtension K E J = I := by
  generalize hn : Module.finrank K E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    by_cases hdeg : Module.finrank K E = 1
    · have hcard : Nat.card Gal(E/K) = 1 := (IsGalois.card_aut_eq_finrank K E).trans hdeg
      have hg (g : Gal(E/K)) : g = 1 := by
        have hp : g ^ Nat.card Gal(E/K) = 1 := pow_card_eq_one'
        rwa [hcard,pow_one] at hp
      have ha : Function.Surjective (algebraMap K E) := by
        intro x
        change x ∈ Set.range (algebraMap K E)
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro g
        rw [hg g]
        rfl
      obtain ⟨J,hJ⟩ := extend_surjective_of_surjective K E ha I.toMul
      exact ⟨Additive.ofMul J,congrArg Additive.ofMul hJ⟩
    · have hc : 1 < Nat.card Gal(E/K) := by
        rw [IsGalois.card_aut_eq_finrank]
        have hp : 0 < Module.finrank K E := Module.finrank_pos
        omega
      letI : Nontrivial Gal(E/K) := Finite.one_lt_card_iff_nontrivial.mp hc
      obtain ⟨H,hH,hcard⟩ := PGroupCentralTwo.exists_normal_two Gal(E/K) hG
      letI := hH
      let M := IntermediateField.fixedField H
      letI : NumberField M := NumberField.of_module_finite ℚ M
      have hdegM : Module.finrank M E = 2 :=
        (IntermediateField.finrank_fixedField_eq_card H).trans hcard
      have hMlt : Module.finrank K M < n := by
        have he := Module.finrank_mul_finrank K M E
        rw [hdegM,hn] at he
        have hp : 0 < Module.finrank K M := Module.finrank_pos
        omega
      have hGM : IsPGroup 2 Gal(M/K) :=
        hG.of_surjective (AlgEquiv.restrictNormalHom M) (AlgEquiv.restrictNormalHom_surjective E)
      have hu := UnramifiedTowerDescent.different_top K M E hunram
      have hcardM : Nat.card Gal(E/M) = 2 := (IsGalois.card_aut_eq_finrank M E).trans hdegM
      letI : Nontrivial Gal(E/M) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨σ,hσ⟩ := exists_ne (1 : Gal(E/M))
      have hσI : dAction M E σ I = I := hI (σ.restrictScalars K)
      obtain ⟨J,hJ⟩ := (UnramifiedAmbiguousClasses.idealFixed M E σ hdegM hσ hu.1).surjective
        ⟨I,(InvolutionHerbrand.mem_plus _ _).mpr hσI⟩
      have hj : idealExtension M E J = I := congrArg Subtype.val hJ
      have hfix (g : Gal(M/K)) : idealAction K M g J = J := by
        obtain ⟨s,rfl⟩ := AlgEquiv.restrictNormalHom_surjective E g
        apply idealExtension_injective M E
        rw [idealExtension_equivariant,hj,hI]
      obtain ⟨L,hL⟩ := ih (Module.finrank K M) hMlt M hGM hu.2 J hfix rfl
      refine ⟨L,?_⟩
      have he := congrArg (idealExtension M E) hL
      change Additive.ofMul (extend M E (extend K M L.toMul)) = idealExtension M E J at he
      rw [extend_trans] at he
      exact he.trans hj

end GaloisCocycleActions


namespace ModTwo
open CocycleTwo
open scoped Classical
variable {G A : Type} [Group G] [AddCommGroup A] (ρ : G →* AddAut A)

theorem fixed_lift (hH1 : VanishingH1 ρ) (h2 : Function.Injective (fun a : A => a+a)) (v : fixed ρ) :
    ∃ a : A, mk a = v.1 ∧ ∀ g, ρ g a = a := by
  obtain ⟨x,hx⟩ := projection_surjective ρ v
  have hb : IsCocycleOne ρ x.1.2 := by
    intro g h
    have hz : boundary ρ x.1.2 g h = 0 := h2 (by
      simpa only [zero_add] using KummerConnecting.double_pair_boundary ρ x g h)
    change ρ g (x.1.2 h)-x.1.2 (g*h)+x.1.2 g = 0 at hz
    have hz' : (ρ g (x.1.2 h)+x.1.2 g)-x.1.2 (g*h) = 0 := by
      rw [← sub_add_eq_add_sub]
      exact hz
    exact (sub_eq_zero.mp hz').symm
  obtain ⟨a,ha⟩ := hH1 _ hb
  refine ⟨x.1.1-(a+a),?_,?_⟩
  · rw [map_sub,mk_double,sub_zero]
    exact congrArg Subtype.val hx
  · intro g
    have hp := x.property g
    rw [← ha g] at hp
    apply sub_eq_zero.mp
    calc
      _ = (ρ g x.1.1-x.1.1)-((ρ g a-a)+(ρ g a-a)) := by rw [map_sub,map_add]; abel
      _ = 0 := by rw [hp,sub_self]

end ModTwo

namespace ModTwo
open CocycleTwo
open scoped Classical
variable {G A B A₀ : Type} [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup A₀]
  (ρ : G →* AddAut A) (τ : G →* AddAut B) (p : A →+ B)
  (hp : ∀ g a, p (ρ g a) = τ g (p a))

include hp in
theorem map_equivariant (g : G) (v : V A) :
    map (τ g).toAddMonoidHom (map p v) = map p (map (ρ g).toAddMonoidHom v) := by
  obtain ⟨a,rfl⟩ := mk_surjective v
  simp only [map_mk]
  exact congrArg mk (hp g a).symm

noncomputable def mapFixed : fixed ρ →ₗ[ZMod 2] fixed τ :=
  ((map p).comp (fixed ρ).subtype).codRestrict _ (fun v g => by
    change map (τ g).toAddMonoidHom (map p v.1) = map p v.1
    rw [map_equivariant ρ τ p hp,v.property g])

variable (e : A₀ →+ A) (hei : Function.Injective e)
  (hef : ∀ g a, ρ g (e a) = e a)
  (hes : ∀ a : A, (∀ g, ρ g a = a) → ∃ a₀ : A₀, e a₀ = a)

noncomputable def toFixed : V A₀ →ₗ[ZMod 2] fixed ρ :=
  (map e).codRestrict _ (fun v g => by
    obtain ⟨a,rfl⟩ := mk_surjective v
    rw [map_mk,map_mk]
    exact congrArg mk (hef g a))

include hef hes in
theorem toFixed_surjective (hH1 : VanishingH1 ρ) (h2 : Function.Injective (fun a : A => a+a)) :
    Function.Surjective (toFixed ρ e hef) := by
  intro v
  obtain ⟨a,ha,haf⟩ := fixed_lift ρ hH1 h2 v
  obtain ⟨b,hb⟩ := hes a haf
  refine ⟨mk b,Subtype.ext ?_⟩
  change map e (mk b) = v.1
  rw [map_mk,hb,ha]

include hei hef hes in
theorem toFixed_injective (h2 : Function.Injective (fun a : A => a+a)) :
    Function.Injective (toFixed ρ e hef) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  obtain ⟨a,rfl⟩ := mk_surjective v
  have hz : mk (e a) = 0 := congrArg Subtype.val hv
  obtain ⟨b,hb⟩ := (mk_eq_zero _).mp hz
  have hbf (g : G) : ρ g b = b := h2 (by
    change ρ g b+ρ g b = b+b
    rw [← map_add,hb,hef])
  obtain ⟨c,hc⟩ := hes b hbf
  apply (mk_eq_zero _).mpr
  refine ⟨c,hei ?_⟩
  rw [map_add,hc,hb]

noncomputable def fixedEquiv (hH1 : VanishingH1 ρ) (h2 : Function.Injective (fun a : A => a+a)) :
    V A₀ ≃ₗ[ZMod 2] fixed ρ :=
  LinearEquiv.ofBijective (toFixed ρ e hef)
    ⟨toFixed_injective ρ e hei hef hes h2,toFixed_surjective ρ e hef hes hH1 h2⟩

@[simp] theorem fixedEquiv_mk (hH1 : VanishingH1 ρ) (h2 : Function.Injective (fun a : A => a+a)) (a : A₀) :
    (fixedEquiv ρ e hei hef hes hH1 h2 (mk a)).1 = mk (e a) := rfl

end ModTwo

namespace VirtualClassObstruction
open NumberField PrincipalInvolutionSequences FractionalGalois CocycleTwo GaloisCocycleActions
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E]

private theorem ideal_H1 : VanishingH1 (idealAction K E) := by
  intro b hb
  exact ideal_hilbert90 K E (MonoidHom.id _) b hb

private theorem idealExtension_fixed (g : Gal(E/K)) (I : D K) :
    idealAction K E g (idealExtension K E I) = idealExtension K E I := by
  exact congrArg Additive.ofMul (extend_fixed K E g I.toMul)

noncomputable def idealParityEquiv (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    ModTwo.V (D K) ≃ₗ[ZMod 2] ModTwo.fixed (idealAction K E) :=
  ModTwo.fixedEquiv (idealAction K E) (idealExtension K E) (idealExtension_injective K E)
    (idealExtension_fixed K E) (unramified_ideal_descent K E hG hunram) (ideal_H1 K E)
    (FractionalGalois.double_injective E)

@[simp] theorem idealParityEquiv_mk (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) (I : D K) :
    (idealParityEquiv K E hG hunram (ModTwo.mk I)).1 = ModTwo.mk (idealExtension K E I) := rfl

noncomputable def divisorFixed : ModTwo.fixed (fieldAction K E) →ₗ[ZMod 2] ModTwo.fixed (idealAction K E) :=
  ModTwo.mapFixed (fieldAction K E) (idealAction K E)
    (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom (principal_equivariant K E)

/-- The invariant virtual-unit squareclasses. -/
noncomputable def virtualFixed : Submodule (ZMod 2) (ModTwo.fixed (fieldAction K E)) := (divisorFixed K E).ker

noncomputable def obstruction (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    ModTwo.fixed (fieldAction K E) →ₗ[ZMod 2] ModTwo.V (C K) :=
  (ModTwo.map (A := D K) (B := C K) (classMap K).toAddMonoidHom).comp
    ((idealParityEquiv K E hG hunram).symm.toLinearMap.comp (divisorFixed K E))

private theorem fieldExtension_fixed (g : Gal(E/K)) (a : F K) :
    fieldAction K E g (fieldExtension K E a) = fieldExtension K E a := by
  apply Additive.toMul.injective
  apply Units.ext
  exact g.commutes a.toMul

noncomputable def baseSquareclass : F K →+ ModTwo.fixed (fieldAction K E) where
  toFun a := ⟨ModTwo.mk (fieldExtension K E a),fun g => by
    rw [ModTwo.map_mk]
    exact congrArg ModTwo.mk (fieldExtension_fixed K E g a)⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp

@[simp] theorem baseSquareclass_val (a : F K) :
    (baseSquareclass K E a).1 = ModTwo.mk (fieldExtension K E a) := rfl

theorem divisor_base (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) (a : F K) :
    divisorFixed K E (baseSquareclass K E a) =
      idealParityEquiv K E hG hunram (ModTwo.mk (UnramifiedAmbiguousClasses.principalWhole K a)) := by
  apply Subtype.ext
  change ModTwo.map (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom
    (ModTwo.mk (fieldExtension K E a)) = ModTwo.mk (idealExtension K E (UnramifiedAmbiguousClasses.principalWhole K a))
  rw [ModTwo.map_mk]
  exact congrArg ModTwo.mk (principal_extension K E a)

theorem connecting_base (a : F K) : FieldKummerConnecting.connecting E K (baseSquareclass K E a) = 0 := by
  exact KummerConnecting.connecting_invariant (fieldAction K E) (FieldKummerConnecting.sign E)
    (FieldKummerConnecting.sign_injective E) (FieldKummerConnecting.sign_fixed E K)
    (FieldKummerConnecting.sign_range E) (fieldExtension K E a) (fieldExtension_fixed K E · a) _ rfl

set_option maxHeartbeats 2000000 in
/-- A relation with trivial base ideal-class obstruction is represented by
an invariant virtual unit, up to a class killed by the Kummer map. -/
theorem kernel_obstruction (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (v : ModTwo.fixed (fieldAction K E)) (hv : obstruction K E hG hunram v = 0) :
    ∃ s : virtualFixed K E, FieldKummerConnecting.connecting E K s.1 = FieldKummerConnecting.connecting E K v := by
  obtain ⟨J,hJ⟩ := ModTwo.mk_surjective ((idealParityEquiv K E hG hunram).symm (divisorFixed K E v))
  have hdiv : divisorFixed K E v = idealParityEquiv K E hG hunram (ModTwo.mk J) := by
    rw [hJ,LinearEquiv.apply_symm_apply]
  have hclass : ModTwo.mk (classMap K J) = 0 := by
    change ModTwo.map (A := D K) (B := C K) (classMap K).toAddMonoidHom
      ((idealParityEquiv K E hG hunram).symm (divisorFixed K E v)) = 0 at hv
    rw [← hJ,ModTwo.map_mk] at hv
    exact hv
  obtain ⟨c,hc⟩ := (ModTwo.mk_eq_zero _).mp hclass
  obtain ⟨I,hI⟩ := FractionalClasses.mk_surjective K c.toMul
  let I' : D K := Additive.ofMul I
  have hI' : classMap K I' = c := congrArg Additive.ofMul hI
  have hpr : J-(I'+I') ∈ (UnramifiedAmbiguousClasses.principalWhole K).range := by
    rw [← UnramifiedAmbiguousClasses.ker_classMap]
    change classMap K (J-(I'+I')) = 0
    rw [map_sub,map_add,hI',hc,sub_self]
  obtain ⟨a,ha⟩ := hpr
  have hparity : ModTwo.mk (UnramifiedAmbiguousClasses.principalWhole K a) = ModTwo.mk J := by
    rw [ha,map_sub,ModTwo.mk_double,sub_zero]
  have hd : divisorFixed K E (baseSquareclass K E a) = divisorFixed K E v := by
    rw [divisor_base K E hG hunram,hparity,hdiv]
  refine ⟨⟨v-baseSquareclass K E a,?_⟩,?_⟩
  · change divisorFixed K E (v-baseSquareclass K E a) = 0
    rw [map_sub,hd,sub_self]
  · change FieldKummerConnecting.connecting E K (v-baseSquareclass K E a) = _
    rw [map_sub,connecting_base,sub_zero]

end VirtualClassObstruction


/-! A dimension bound from an obstruction map and representatives of its kernel. -/
namespace LinearObstructionBound
open scoped Classical
variable {k V H C : Type*} [Field k] [AddCommGroup V] [AddCommGroup H] [AddCommGroup C]
  [Module k V] [Module k H] [Module k C] [FiniteDimensional k C]

/-- A surjective target is bounded by the dimension of an obstruction space
plus a subspace providing representatives for the obstruction kernel. -/
theorem finrank_le (f : V →ₗ[k] H) (hf : Function.Surjective f) (g : V →ₗ[k] C)
    (S : Submodule k V) [FiniteDimensional k S]
    (hS : ∀ v : V, g v = 0 → ∃ s : S, f s.1 = f v) :
    Module.finrank k H ≤ Module.finrank k C+Module.finrank k S := by
  obtain ⟨s,hs⟩ := LinearMap.exists_rightInverse_of_surjective g.rangeRestrict
    (LinearMap.range_eq_top.mpr g.surjective_rangeRestrict)
  have hs' (c : g.range) : g (s c) = c.1 :=
    congrArg Subtype.val (LinearMap.congr_fun hs c)
  let F : g.range × S →ₗ[k] H := (f.comp s).coprod (f.comp S.subtype)
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨v,rfl⟩ := hf y
    have hw : g (v-s (g.rangeRestrict v)) = 0 := by rw [map_sub,hs']; exact sub_self _
    obtain ⟨u,hu⟩ := hS _ hw
    refine ⟨(g.rangeRestrict v,u),?_⟩
    change f (s (g.rangeRestrict v))+f u.1 = f v
    rw [hu,map_sub]
    abel
  have hbound := F.finrank_range_le
  rw [LinearMap.range_eq_top.mpr hF,(Submodule.topEquiv : (⊤ : Submodule k H) ≃ₗ[k] H).finrank_eq,Module.finrank_prod] at hbound
  exact hbound.trans (Nat.add_le_add_right (Submodule.finrank_le g.range) _)

end LinearObstructionBound

namespace VirtualClassObstruction
open NumberField PrincipalInvolutionSequences GaloisCocycleActions
open scoped Classical nonZeroDivisors
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]

set_option maxHeartbeats 2000000 in
/-- A weak relation bound sufficient for large initial genus rank. The
virtual-unit invariant term still needs a terminal-layer local estimate. -/
theorem relation_bound (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    [FiniteDimensional (ZMod 2) (virtualFixed K E)] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Gal(E/K) (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2) (ModTwo.V (C K))+Module.finrank (ZMod 2) (virtualFixed K E) := by
  letI : Finite (C K) := Finite.of_equiv (FractionalClasses.Classes K) Additive.ofMul
  letI : Finite (ModTwo.V (C K)) := Finite.of_surjective ModTwo.mk ModTwo.mk_surjective
  letI : FiniteDimensional (ZMod 2) (ModTwo.V (C K)) := Module.Finite.of_finite
  exact LinearObstructionBound.finrank_le (FieldKummerConnecting.connecting E K)
    (FieldKummerConnecting.connecting_surjective E K hG hunram) (obstruction K E hG hunram)
    (virtualFixed K E) (kernel_obstruction K E hG hunram)

end VirtualClassObstruction


/-! Integral local-unit representatives of virtual-unit squareclasses. -/
namespace VirtualLocalNormalization
open NumberField FractionalIdeal
open scoped Classical nonZeroDivisors
variable (E : Type*) [Field E] [NumberField E]

/-- A virtual radicand can be rescaled by a square to become integral and
coprime to any prescribed nonzero proper ideal. -/
theorem exists_coprime_representative (P : Ideal (𝓞 E)) (hp0 : P ≠ ⊥) (hp1 : P ≠ ⊤)
    (a : E) (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0)
    (ha : spanSingleton (𝓞 E)⁰ a = I*I) :
    ∃ x : E, x ≠ 0 ∧ ∃ b : 𝓞 E, (b : E) = a*x^2 ∧ IsCoprime P (Ideal.span {b}) := by
  obtain ⟨x,hx⟩ := IsDedekindDomain.exists_add_spanSingleton_mul_eq
    (a := (P : FractionalIdeal (𝓞 E)⁰ E)) (b := I) (c := 1)
    coeIdeal_le_one (coeIdeal_ne_zero.mpr hp0) hI
  have hx0 : x ≠ 0 := by
    intro h
    rw [h,spanSingleton_zero,zero_mul,add_zero] at hx
    apply hp1
    apply coeIdeal_injective (K := E)
    simpa only [coeIdeal_top] using hx
  have hle : spanSingleton (𝓞 E)⁰ x*I ≤ 1 := by
    rw [← hx]
    exact le_add_of_nonneg_left (FractionalIdeal.zero_le _)
  obtain ⟨J,hJ⟩ := le_one_iff_exists_coeIdeal.mp hle
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    apply coeIdeal_injective (K := E)
    change ((P ⊔ J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = ((⊤ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
    rw [coeIdeal_sup,coeIdeal_top,hJ]
    exact hx
  have hprod : spanSingleton (𝓞 E)⁰ (a*x^2) = (J : FractionalIdeal (𝓞 E)⁰ E)*(J : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← spanSingleton_mul_spanSingleton,← spanSingleton_pow,ha,hJ]
    ring
  have hr : a*x^2 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    have hle' : (J : FractionalIdeal (𝓞 E)⁰ E)*(J : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := by
      have hj : (J : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 := coeIdeal_le_one
      exact (mul_le_mul' hj hj).trans_eq (_root_.one_mul _)
    exact hle' (hprod ▸ mem_spanSingleton_self (𝓞 E)⁰ (a*x^2))
  obtain ⟨b,hb⟩ := (mem_one_iff (𝓞 E)⁰).mp hr
  change (b : E) = a*x^2 at hb
  refine ⟨x,hx0,b,hb,?_⟩
  have hbJ : Ideal.span {b} = J^2 := by
    apply coeIdeal_injective (K := E)
    change ((Ideal.span {b}) : FractionalIdeal (𝓞 E)⁰ E) = ((J^2 : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
    rw [coeIdeal_span_singleton,coeIdeal_pow,pow_two]
    change spanSingleton (𝓞 E)⁰ (b : E) = _
    rw [hb,hprod]
  rw [hbJ]
  exact hcop.pow_right

end VirtualLocalNormalization

namespace ModFourResidues
open NumberField
open scoped Classical nonZeroDivisors
variable (E : Type*) [Field E] [NumberField E]

def modulus : Ideal (𝓞 E) := Ideal.span {(4 : 𝓞 E)}
abbrev R := 𝓞 E ⧸ modulus E
abbrev reduce : 𝓞 E →+* R E := Ideal.Quotient.mk (modulus E)

@[simp] theorem reduce_four : reduce E 4 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem modulus_ne_top : modulus E ≠ ⊤ := by
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(4 : ℤ)}) = ⊤ := by
    simpa only [Ideal.map_span,Set.image_singleton,map_ofNat] using h
  have he := (Ideal.map_eq_top_iff (algebraMap ℤ (𝓞 E))
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp hm
  have hu : IsUnit (4 : ℤ) := Ideal.span_singleton_eq_top.mp he
  norm_num [Int.isUnit_iff] at hu

theorem isUnit_reduce_iff (a : 𝓞 E) : IsUnit (reduce E a) ↔ IsCoprime a 4 := by
  constructor
  · rintro ⟨u,hu⟩
    obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (R E)ˣ) : R E)
    have he : reduce E (a*b) = reduce E 1 := by
      rw [map_mul,map_one,← hu,hb]
      exact u.val_inv
    have hm : a*b-1 ∈ Ideal.span {(4 : 𝓞 E)} := Ideal.Quotient.eq.mp he
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
    refine ⟨b,-c,?_⟩
    linear_combination hc
  · intro h
    have he := h.map (reduce E)
    rw [reduce_four,isCoprime_zero_right] at he
    exact he

noncomputable def unit (a : 𝓞 E) (ha : IsUnit (reduce E a)) : (R E)ˣ := ha.unit

@[simp] theorem unit_val (a : 𝓞 E) (ha : IsUnit (reduce E a)) : (unit E a ha : R E) = reduce E a := ha.unit_spec

noncomputable def squareclass (a : 𝓞 E) (ha : IsUnit (reduce E a)) : ModTwo.V (Additive (R E)ˣ) :=
  ModTwo.mk (Additive.ofMul (unit E a ha))

/-- Integral representatives prime to four of the same field squareclass
have the same residue-unit squareclass. -/
theorem squareclass_eq_of_square (a b : 𝓞 E) (ha : IsUnit (reduce E a)) (hb : IsUnit (reduce E b))
    (x : E) (hx : (a : E) = (b : E)*x^2) : squareclass E a ha = squareclass E b hb := by
  have hy : ((b : E)*x)^2 = (a*b : 𝓞 E) := by
    change ((b : E)*x)^2 = (a : E)*(b : E)
    rw [hx]
    ring
  have hyi : IsIntegral ℤ ((b : E)*x) := IsIntegral.of_pow (by norm_num : 0 < 2) (hy ▸ (a*b).property)
  let y : 𝓞 E := ⟨(b : E)*x,hyi⟩
  have hyy : y*y = a*b := by
    apply RingOfIntegers.coe_injective
    simpa only [pow_two] using hy
  have hyq : reduce E y*reduce E y = reduce E a*reduce E b := by
    rw [← map_mul,hyy,map_mul]
  have huy : IsUnit (reduce E y) := isUnit_of_mul_isUnit_left (hyq ▸ ha.mul hb)
  have he : unit E a ha*unit E b hb = unit E y huy*unit E y huy := by
    apply Units.ext
    simpa only [Units.val_mul,unit_val] using hyq.symm
  have he' : (Additive.ofMul (unit E a ha) : Additive (R E)ˣ)+Additive.ofMul (unit E b hb) =
      Additive.ofMul (unit E y huy)+Additive.ofMul (unit E y huy) := congrArg Additive.ofMul he
  have hm := congrArg (ModTwo.mk (A := Additive (R E)ˣ)) he'
  rw [map_add,map_add,ModTwo.double_zero] at hm
  change squareclass E a ha+squareclass E b hb = 0 at hm
  have hn : -squareclass E b hb = squareclass E b hb :=
    neg_eq_iff_add_eq_zero.mpr (ModTwo.double_zero _)
  exact (eq_neg_of_add_eq_zero_left hm).trans hn

instance : Nontrivial (R E) := Ideal.Quotient.nontrivial (modulus_ne_top E)
instance : Finite (R E) := (modulus E).finiteQuotientOfFreeOfNeBot (by simp [modulus])

@[simp] theorem squareclass_one : squareclass E 1 (by simp) = 0 := by
  have hu : unit E 1 (by simp) = 1 := by apply Units.ext; simp
  unfold squareclass
  rw [hu]
  exact map_zero ModTwo.mk

theorem squareclass_mul (a b : 𝓞 E) (ha : IsUnit (reduce E a)) (hb : IsUnit (reduce E b)) :
    squareclass E (a*b) (by simpa only [map_mul] using ha.mul hb) =
      squareclass E a ha+squareclass E b hb := by
  have hu : unit E (a*b) (by simpa only [map_mul] using ha.mul hb) = unit E a ha*unit E b hb := by
    apply Units.ext
    simp only [unit_val,Units.val_mul,map_mul]
  change ModTwo.mk (Additive.ofMul (unit E (a*b) _)) = _
  rw [hu]
  exact map_add ModTwo.mk _ _

/-- A trivial residue squareclass supplies an actual congruence modulo4. -/
theorem exists_square_mod_four (a : 𝓞 E) (ha : IsUnit (reduce E a))
    (h : squareclass E a ha = 0) : ∃ b c : 𝓞 E, a = b^2+4*c := by
  obtain ⟨v,hv⟩ := (ModTwo.mk_eq_zero _).mp h
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective (v.toMul : R E)
  have he : reduce E a = reduce E (b^2) := by
    have hv' := congrArg (fun z : Additive (R E)ˣ => (z.toMul : R E)) hv
    change (v.toMul : R E)*(v.toMul : R E) = (unit E a ha : R E) at hv'
    rw [unit_val,← hb] at hv'
    simpa only [map_pow,pow_two] using hv'.symm
  have hm : a-b^2 ∈ Ideal.span {(4 : 𝓞 E)} := Ideal.Quotient.eq.mp he
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
  refine ⟨b,c,?_⟩
  linear_combination hc

end ModFourResidues



namespace VirtualUnitResidues
open NumberField PrincipalInvolutionSequences FractionalGalois
open scoped Classical nonZeroDivisors
variable (E : Type) [Field E] [NumberField E]

noncomputable def divisor : ModTwo.V (F E) →ₗ[ZMod 2] ModTwo.V (D E) :=
  ModTwo.map (UnramifiedAmbiguousClasses.principalWhole E).toAddMonoidHom

/-- Virtual-unit squareclasses, characterized by a square principal ideal. -/
noncomputable def Sel := (divisor E).ker

noncomputable def integralClass (a : 𝓞 E) (ha : a ≠ 0) : ModTwo.V (F E) :=
  ModTwo.mk (Additive.ofMul (Units.mk0 (a : E) (RingOfIntegers.coe_ne_zero_iff.mpr ha)))

structure Representative (v : ModTwo.V (F E)) where
  a : 𝓞 E
  ne_zero : a ≠ 0
  unit : IsUnit (ModFourResidues.reduce E a)
  class_eq : integralClass E a ne_zero = v

/-- Every virtual-unit squareclass has an integral representative which
is a unit modulo four. -/
theorem exists_representative (v : Sel E) : Nonempty (Representative E v.1) := by
  obtain ⟨a,ha⟩ := ModTwo.mk_surjective v.1
  have hp : ModTwo.mk (UnramifiedAmbiguousClasses.principalWhole E a) = 0 := by
    have h := v.property
    change divisor E v.1 = 0 at h
    rw [← ha] at h
    exact h
  obtain ⟨I,hI⟩ := (ModTwo.mk_eq_zero _).mp hp
  have hvirt : FractionalIdeal.spanSingleton (𝓞 E)⁰ (a.toMul : E) = I.toMul.1*I.toMul.1 := by
    have he := congrArg (fun I : D E => I.toMul.1) hI.symm
    change (toPrincipalIdeal (𝓞 E) E a.toMul : FractionalIdeal (𝓞 E)⁰ E) = _ at he
    simpa only [coe_toPrincipalIdeal] using he
  have hp0 : ModFourResidues.modulus E ≠ ⊥ := by simp [ModFourResidues.modulus]
  obtain ⟨x,hx,r,hr,hcop⟩ := VirtualLocalNormalization.exists_coprime_representative E
    (ModFourResidues.modulus E) hp0 (ModFourResidues.modulus_ne_top E)
    (a.toMul : E) I.toMul.1 I.toMul.ne_zero hvirt
  have hr0 : r ≠ 0 := by
    apply RingOfIntegers.coe_ne_zero_iff.mp
    change (r : E) ≠ 0
    rw [hr]
    exact mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ hx)
  have hru : IsUnit (ModFourResidues.reduce E r) :=
    (ModFourResidues.isUnit_reduce_iff E r).mpr
      ((Ideal.isCoprime_span_singleton_iff (4 : 𝓞 E) r).mp hcop).symm
  refine ⟨⟨r,hr0,hru,?_⟩⟩
  let xu : Eˣ := Units.mk0 x hx
  have he : Units.mk0 (r : E) (RingOfIntegers.coe_ne_zero_iff.mpr hr0) = a.toMul*(xu*xu) := by
    apply Units.ext
    simpa only [Units.val_mul,Units.val_mk0,pow_two] using hr
  change ModTwo.mk (Additive.ofMul (Units.mk0 (r : E) _)) = v.1
  rw [he]
  change ModTwo.mk (a+(Additive.ofMul xu+Additive.ofMul xu)) = v.1
  rw [map_add,ModTwo.mk_double,add_zero,ha]

theorem representatives_residue_eq {v : ModTwo.V (F E)} (a b : Representative E v) :
    ModFourResidues.squareclass E a.a a.unit = ModFourResidues.squareclass E b.a b.unit := by
  let au : F E := Additive.ofMul (Units.mk0 (a.a : E) (RingOfIntegers.coe_ne_zero_iff.mpr a.ne_zero))
  let bu : F E := Additive.ofMul (Units.mk0 (b.a : E) (RingOfIntegers.coe_ne_zero_iff.mpr b.ne_zero))
  have hm : ModTwo.mk (au-bu) = 0 := by
    rw [map_sub]
    change integralClass E a.a a.ne_zero-integralClass E b.a b.ne_zero = 0
    rw [a.class_eq,b.class_eq,sub_self]
  obtain ⟨z,hz⟩ := (ModTwo.mk_eq_zero _).mp hm
  have he : au = bu+(z+z) := by rw [hz]; abel
  have hv := congrArg (fun a : F E => (a.toMul : E)) he
  change (a.a : E) = (b.a : E)*((z.toMul : E)*(z.toMul : E)) at hv
  exact ModFourResidues.squareclass_eq_of_square E a.a b.a a.unit b.unit z.toMul (by simpa only [pow_two] using hv)

noncomputable def residue (v : Sel E) : ModTwo.V (Additive (ModFourResidues.R E)ˣ) :=
  ModFourResidues.squareclass E (exists_representative E v).some.a (exists_representative E v).some.unit

theorem residue_of_representative (v : Sel E) (r : Representative E v.1) :
    residue E v = ModFourResidues.squareclass E r.a r.unit :=
  representatives_residue_eq E (exists_representative E v).some r

@[simp] theorem integralClass_one : integralClass E 1 (by simp) = 0 := by
  have he : Units.mk0 (1 : E) (by simp) = 1 := by apply Units.ext; rfl
  change ModTwo.mk (Additive.ofMul (Units.mk0 (1 : E) _)) = 0
  rw [he]
  exact map_zero ModTwo.mk

theorem integralClass_mul (a b : 𝓞 E) (ha : a ≠ 0) (hb : b ≠ 0) :
    integralClass E (a*b) (mul_ne_zero ha hb) = integralClass E a ha+integralClass E b hb := by
  have he : Units.mk0 ((a*b : 𝓞 E) : E) (RingOfIntegers.coe_ne_zero_iff.mpr (mul_ne_zero ha hb)) =
      Units.mk0 (a : E) (RingOfIntegers.coe_ne_zero_iff.mpr ha)*
        Units.mk0 (b : E) (RingOfIntegers.coe_ne_zero_iff.mpr hb) := by apply Units.ext; rfl
  change ModTwo.mk (Additive.ofMul (Units.mk0 ((a*b : 𝓞 E) : E) _)) = _
  rw [he]
  exact map_add ModTwo.mk _ _

@[simp] theorem residue_zero : residue E 0 = 0 := by
  let r : Representative E (0 : ModTwo.V (F E)) := ⟨1,by simp,by simp,integralClass_one E⟩
  rw [residue_of_representative E 0 r]
  exact ModFourResidues.squareclass_one E

theorem residue_add (v w : Sel E) : residue E (v+w) = residue E v+residue E w := by
  let a := (exists_representative E v).some
  let b := (exists_representative E w).some
  let r : Representative E (v+w).1 := {
    a := a.a*b.a
    ne_zero := mul_ne_zero a.ne_zero b.ne_zero
    unit := by simpa only [map_mul] using a.unit.mul b.unit
    class_eq := by rw [integralClass_mul E a.a b.a a.ne_zero b.ne_zero,a.class_eq,b.class_eq]; rfl }
  rw [residue_of_representative E (v+w) r,residue_of_representative E v a,residue_of_representative E w b]
  exact ModFourResidues.squareclass_mul E a.a b.a a.unit b.unit

/-- Residue squareclasses of virtual units, as a linear map over F2. -/
noncomputable def residueLinear : Sel E →ₗ[ZMod 2] ModTwo.V (Additive (ModFourResidues.R E)ˣ) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := residue E
    map_zero' := residue_zero E
    map_add' := residue_add E }

end VirtualUnitResidues

namespace SquareclassSigns
open NumberField PrincipalInvolutionSequences GaloisCocycleActions
open scoped Classical
variable (E : Type) [Field E] [NumberField E] [IsTotallyReal E]

noncomputable def signHom (τ : E →+* ℝ) : F E →+ ZMod 2 where
  toFun a := if 0 < τ (a.toMul : E) then 0 else 1
  map_zero' := by change (if 0 < τ 1 then (0 : ZMod 2) else 1) = 0; simp
  map_add' a b := by
    change (if 0 < τ ((a.toMul : E)*(b.toMul : E)) then (0 : ZMod 2) else 1) =
      (if 0 < τ (a.toMul : E) then 0 else 1)+(if 0 < τ (b.toMul : E) then 0 else 1)
    rw [map_mul]
    have ha : τ (a.toMul : E) ≠ 0 := by simpa only [map_zero] using τ.injective.ne (Units.ne_zero a.toMul)
    have hb : τ (b.toMul : E) ≠ 0 := by simpa only [map_zero] using τ.injective.ne (Units.ne_zero b.toMul)
    by_cases ha' : 0 < τ (a.toMul : E) <;> by_cases hb' : 0 < τ (b.toMul : E)
    · simp [ha',hb',mul_pos ha' hb']
    · have hb'' : τ (b.toMul : E) < 0 := lt_of_le_of_ne (le_of_not_gt hb') hb
      simp [ha',hb',not_lt.mpr (mul_neg_of_pos_of_neg ha' hb'').le]
    · have ha'' : τ (a.toMul : E) < 0 := lt_of_le_of_ne (le_of_not_gt ha') ha
      simp [ha',hb',not_lt.mpr (mul_neg_of_neg_of_pos ha'' hb').le]
    · have ha'' : τ (a.toMul : E) < 0 := lt_of_le_of_ne (le_of_not_gt ha') ha
      have hb'' : τ (b.toMul : E) < 0 := lt_of_le_of_ne (le_of_not_gt hb') hb
      simp only [if_neg ha',if_neg hb',if_pos (mul_pos_of_neg_of_neg ha'' hb'')]
      exact (CharTwo.add_self_eq_zero (1 : ZMod 2)).symm

noncomputable def atEmbedding (φ : E →+* ℂ) : ModTwo.V (F E) →ₗ[ZMod 2] ZMod 2 :=
  (ModN.liftEquiv' (n := 2)).symm
    ⟨signHom E (IsTotallyReal.complexEmbedding_isReal φ).embedding,fun a => by
      simpa only [two_nsmul] using CharTwo.add_self_eq_zero
        (signHom E (IsTotallyReal.complexEmbedding_isReal φ).embedding a)⟩

@[simp] theorem atEmbedding_mk (φ : E →+* ℂ) (a : F E) :
    atEmbedding E φ (ModTwo.mk a) = if 0 < (φ (a.toMul : E)).re then 0 else 1 := rfl

theorem positive_of_zero (φ : E →+* ℂ) (a : F E) (h : atEmbedding E φ (ModTwo.mk a) = 0) :
    0 < (φ (a.toMul : E)).re := by
  simpa only [atEmbedding_mk,ite_eq_left_iff,one_ne_zero,imp_false,not_not] using h

variable (K : Type) [Field K] [NumberField K] [Algebra K E]

theorem equivariant (φ : E →+* ℂ) (g : Gal(E/K)) (v : ModTwo.V (F E)) :
    atEmbedding E φ (ModTwo.map (fieldAction K E g).toAddMonoidHom v) =
      atEmbedding E (φ.comp g.toRingHom) v := by
  obtain ⟨a,rfl⟩ := ModTwo.mk_surjective v
  rw [ModTwo.map_mk,atEmbedding_mk,atEmbedding_mk]
  rfl

variable [FiniteDimensional K E] [IsGalois K E]

/-- Signs of invariant squareclasses need only be recorded at one embedding
above each embedding of the base. -/
noncomputable def fixedSigns : ModTwo.fixed (fieldAction K E) →ₗ[ZMod 2] ((K →+* ℂ) → ZMod 2) :=
  LinearMap.pi (fun φ => (atEmbedding E (ComplexEmbedding.lift E φ)).comp (ModTwo.fixed (fieldAction K E)).subtype)

theorem positive_of_fixedSigns_zero (v : ModTwo.fixed (fieldAction K E)) (hv : fixedSigns E K v = 0)
    (a : F E) (ha : ModTwo.mk a = v.1) : ∀ φ : E →+* ℂ, 0 < (φ (a.toMul : E)).re := by
  intro φ
  let τ : K →+* ℂ := φ.comp (algebraMap K E)
  let ψ : E →+* ℂ := ComplexEmbedding.lift E τ
  obtain ⟨g,hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq ψ φ (by
    exact ComplexEmbedding.lift_comp_algebraMap E τ)
  have hψ : atEmbedding E ψ v.1 = 0 := congrFun hv τ
  have he := equivariant E K ψ g.symm v.1
  change ψ.comp g.symm.toRingHom = φ at hg
  rw [v.property g.symm,hg] at he
  apply positive_of_zero E φ a
  rw [ha,← he,hψ]

/-- The sign target has exactly the absolute base degree many dimensions. -/
theorem signs_finrank : Module.finrank (ZMod 2) ((K →+* ℂ) → ZMod 2) = Module.finrank ℚ K := by
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,NumberField.Embeddings.card,Nat.cast_id]

end SquareclassSigns

namespace VirtualUnitResidues
open NumberField PrincipalInvolutionSequences FractionalGalois GaloisCocycleActions
open scoped Classical nonZeroDivisors
variable (E : Type) [Field E] [NumberField E]

/-- The arithmetic square criterion supplied by a terminal unramified tower. -/
def SquareCriterion : Prop := ∀ (a b c : 𝓞 E), a ≠ 0 → IsCoprime a 2 → a = b^2+4*c →
  ∀ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → FractionalIdeal.spanSingleton (𝓞 E)⁰ (a : E) = I*I →
  (∀ φ : E →+* ℂ, 0 ≤ (φ (a : E)).re) → IsSquare (a : E)

theorem integralClass_eq_zero_of_isSquare (a : 𝓞 E) (ha : a ≠ 0) (hs : IsSquare (a : E)) :
    integralClass E a ha = 0 := by
  obtain ⟨x,hx⟩ := hs
  have hx0 : x ≠ 0 := by
    intro h
    apply RingOfIntegers.coe_ne_zero_iff.mpr ha
    change (a : E) = 0
    rw [hx,h,zero_mul]
  let u : Eˣ := Units.mk0 x hx0
  have he : Units.mk0 (a : E) (RingOfIntegers.coe_ne_zero_iff.mpr ha) = u*u := Units.ext hx
  change ModTwo.mk (Additive.ofMul (Units.mk0 (a : E) _)) = 0
  rw [he]
  exact ModTwo.mk_double (Additive.ofMul u)

variable (K : Type) [Field K] [NumberField K] [Algebra K E]

/-- Invariant virtual squareclasses, viewed as ordinary virtual squareclasses. -/
noncomputable def fromFixed : VirtualClassObstruction.virtualFixed K E →ₗ[ZMod 2] Sel E where
  toFun v := ⟨v.1.1,congrArg Subtype.val v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [IsTotallyReal E] [FiniteDimensional K E] [IsGalois K E]

noncomputable def localSigns : VirtualClassObstruction.virtualFixed K E →ₗ[ZMod 2]
    ModTwo.V (Additive (ModFourResidues.R E)ˣ) × ((K →+* ℂ) → ZMod 2) :=
  ((residueLinear E).comp (fromFixed E K)).prod
    ((SquareclassSigns.fixedSigns E K).comp (VirtualClassObstruction.virtualFixed K E).subtype)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in
/-- At a terminal layer, residues and signs jointly detect invariant virtual
unit squareclasses. The subsequent fixed-residue dimension bound is separate. -/
theorem localSigns_injective (hterm : SquareCriterion E) : Function.Injective (localSigns E K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hr : residue E (fromFixed E K v) = 0 := congrArg Prod.fst hv
  have hs : SquareclassSigns.fixedSigns E K v.1 = 0 := congrArg Prod.snd hv
  let r := (exists_representative E (fromFixed E K v)).some
  have hres : ModFourResidues.squareclass E r.a r.unit = 0 := by
    rw [← residue_of_representative E (fromFixed E K v) r]
    exact hr
  obtain ⟨b,c,hbc⟩ := ModFourResidues.exists_square_mod_four E r.a r.unit hres
  have hcop : IsCoprime r.a (4 : 𝓞 E) := (ModFourResidues.isUnit_reduce_iff E r.a).mp r.unit
  have hcop2 : IsCoprime r.a (2 : 𝓞 E) :=
    (IsCoprime.pow_right_iff (by norm_num : 0 < 2)).mp (by simpa only [show (2 : 𝓞 E)^2 = 4 by norm_num] using hcop)
  let a : F E := Additive.ofMul (Units.mk0 (r.a : E) (RingOfIntegers.coe_ne_zero_iff.mpr r.ne_zero))
  have ha : ModTwo.mk a = v.1.1 := r.class_eq
  have hpositive (φ : E →+* ℂ) : 0 ≤ (φ (r.a : E)).re :=
    (SquareclassSigns.positive_of_fixedSigns_zero E K v.1 hs a ha φ).le
  have hdiv : ModTwo.mk (UnramifiedAmbiguousClasses.principalWhole E a) = 0 := by
    have hh := (fromFixed E K v).property
    change divisor E v.1.1 = 0 at hh
    rw [← ha] at hh
    exact hh
  obtain ⟨I,hI⟩ := (ModTwo.mk_eq_zero _).mp hdiv
  have hvirt : FractionalIdeal.spanSingleton (𝓞 E)⁰ (r.a : E) = I.toMul.1*I.toMul.1 := by
    have he := congrArg (fun I : D E => I.toMul.1) hI.symm
    change (toPrincipalIdeal (𝓞 E) E a.toMul : FractionalIdeal (𝓞 E)⁰ E) = _ at he
    simpa only [coe_toPrincipalIdeal] using he
  have hsq := hterm r.a b c r.ne_zero hcop2 hbc I.toMul.1 I.toMul.ne_zero hvirt hpositive
  have hz := integralClass_eq_zero_of_isSquare E r.a r.ne_zero hsq
  apply Subtype.ext
  apply Subtype.ext
  exact r.class_eq.symm.trans hz

end VirtualUnitResidues



/-! Integers modulo two, with Galois action. -/
set_option synthInstance.maxHeartbeats 200000
namespace ModTwoResidues
open NumberField
open scoped Classical
variable (E : Type*) [Field E] [NumberField E]

def modulus : Ideal (𝓞 E) := Ideal.span {(2 : 𝓞 E)}
abbrev R := 𝓞 E ⧸ modulus E
abbrev reduce : 𝓞 E →+* R E := Ideal.Quotient.mk (modulus E)

@[simp] theorem reduce_two : reduce E 2 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem modulus_ne_top : modulus E ≠ ⊤ := by
  intro h
  have hm : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(2 : ℤ)}) = ⊤ := by
    simpa only [Ideal.map_span,Set.image_singleton,map_ofNat] using h
  have he := (Ideal.map_eq_top_iff (algebraMap ℤ (𝓞 E))
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)) (Algebra.isIntegral_def.mp inferInstance)).mp hm
  have hu : IsUnit (2 : ℤ) := Ideal.span_singleton_eq_top.mp he
  norm_num [Int.isUnit_iff] at hu

instance : Nontrivial (R E) := Ideal.Quotient.nontrivial (modulus_ne_top E)
instance : Finite (R E) := (modulus E).finiteQuotientOfFreeOfNeBot (by simp [modulus])
instance : CharP (R E) 2 := (CharP.charP_iff_prime_eq_zero (by norm_num : Nat.Prime 2)).mpr (by
  simpa only [map_ofNat] using reduce_two E)
noncomputable instance : Algebra (ZMod 2) (R E) := ZMod.algebra _ _
instance : FiniteDimensional (ZMod 2) (R E) := Module.Finite.of_finite

theorem finrank : Module.finrank (ZMod 2) (R E) = Module.finrank ℚ E := by
  apply Nat.pow_right_injective (a := 2) (by norm_num)
  have hc : Nat.card (R E) = 2^Module.finrank ℚ E := by
    change Ideal.absNorm (modulus E) = _
    rw [modulus,Ideal.absNorm_span_singleton]
    have hn := Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis E) (2 : ℤ)
    rw [← Module.finrank_eq_card_basis (RingOfIntegers.basis E),RingOfIntegers.rank] at hn
    simpa only [map_ofNat,Int.natAbs_pow,show (2 : ℤ).natAbs = 2 from rfl] using congrArg Int.natAbs hn
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card,ZMod.card] at hc
  exact hc

variable (K : Type*) [Field K] [NumberField K] [Algebra K E]

noncomputable def action (g : Gal(E/K)) : R E ≃+* R E :=
  Ideal.quotientEquiv (modulus E) (modulus E) (RingOfIntegers.mapAlgEquiv g).toRingEquiv
    (by simp only [modulus,Ideal.map_span,Set.image_singleton,map_ofNat])

@[simp] theorem action_reduce (g : Gal(E/K)) (a : 𝓞 E) :
    action E K g (reduce E a) = reduce E (RingOfIntegers.mapAlgEquiv g a) := rfl

noncomputable def actionLinear (g : Gal(E/K)) : R E →ₗ[ZMod 2] R E :=
  AddMonoidHom.toZModLinearMap 2 (action E K g).toAddMonoidHom

noncomputable def fixed : Submodule (ZMod 2) (R E) where
  carrier := {x | ∀ g, action E K g x = x}
  zero_mem' g := map_zero _
  add_mem' hx hy g := by rw [map_add,hx g,hy g]
  smul_mem' c x hx g := by
    change actionLinear E K g (c • x) = c • x
    rw [map_smul]
    exact congrArg (c • ·) (hx g)

noncomputable def extend : R K →+* R E :=
  Ideal.quotientMap (modulus E) (algebraMap (𝓞 K) (𝓞 E)) (by
    rw [modulus,Ideal.span_le]
    rintro x (rfl : x = 2)
    change algebraMap (𝓞 K) (𝓞 E) 2 ∈ modulus E
    simp only [map_ofNat]
    exact Ideal.mem_span_singleton_self _)

@[simp] theorem extend_reduce (a : 𝓞 K) :
    extend E K (reduce K a) = reduce E (algebraMap (𝓞 K) (𝓞 E) a) := rfl

noncomputable def extendFixed : R K →ₗ[ZMod 2] fixed E K :=
  (AddMonoidHom.toZModLinearMap 2 (extend E K).toAddMonoidHom).codRestrict _ (by
    intro x g
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change action E K g (extend E K (reduce K a)) = extend E K (reduce K a)
    rw [extend_reduce,action_reduce]
    congr 1
    apply RingOfIntegers.coe_injective
    exact g.commutes (a : K))

end ModTwoResidues


namespace LocalResidueSquareclasses
open NumberField
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
variable (E : Type*) [Field E] [NumberField E]
local notation "R₂" => ModTwoResidues.R E
local notation "R₄" => ModFourResidues.R E
local notation "q₂" => ModTwoResidues.reduce E
local notation "q₄" => ModFourResidues.reduce E
abbrev U := Additive (ModFourResidues.R E)ˣ
abbrev W := ModTwo.V (U E)

noncomputable def toTwo : R₄ →+* R₂ :=
  Ideal.quotientMap (ModTwoResidues.modulus E) (RingHom.id _) (by
    rw [ModFourResidues.modulus,Ideal.span_le]
    rintro x (rfl : x = 4)
    change (4 : 𝓞 E) ∈ Ideal.span {(2 : 𝓞 E)}
    exact Ideal.mem_span_singleton.mpr ⟨2,by norm_num⟩)

@[simp] theorem toTwo_reduce (a : 𝓞 E) : toTwo E (q₄ a) = q₂ a := rfl

private theorem principal_sq (a : 𝓞 E) : q₄ (1+2*a)*q₄ (1+2*a) = 1 := by
  rw [← map_mul]
  have he : (1+2*a)*(1+2*a) = 1+4*(a+a*a) := by ring
  rw [he,map_add,map_mul,ModFourResidues.reduce_four,zero_mul,map_one,add_zero]

noncomputable def principal (a : 𝓞 E) : R₄ˣ :=
  Units.mkOfMulEqOne (q₄ (1+2*a)) (q₄ (1+2*a)) (principal_sq E a)

@[simp] theorem principal_val (a : 𝓞 E) : (principal E a : R₄) = q₄ (1+2*a) := rfl

noncomputable def principalHom : 𝓞 E →+ U E where
  toFun a := Additive.ofMul (principal E a)
  map_zero' := by apply Additive.toMul.injective; apply Units.ext; simp
  map_add' a b := by
    apply Additive.toMul.injective
    apply Units.ext
    change q₄ (1+2*(a+b)) = q₄ (1+2*a)*q₄ (1+2*b)
    rw [← map_mul]
    have he : (1+2*a)*(1+2*b) = (1+2*(a+b))+4*(a*b) := by ring
    simp only [he,map_add,map_mul,ModFourResidues.reduce_four,zero_mul,add_zero]

private theorem principal_ker : (q₂).toAddMonoidHom.ker ≤ (principalHom E).ker := by
  intro a ha
  change q₂ a = 0 at ha
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha)
  change Additive.ofMul (principal E a) = 0
  apply Additive.toMul.injective
  apply Units.ext
  change q₄ (1+2*a) = 1
  rw [hb]
  have he : (1+2*(2*b)) = (1+4*b) := by ring
  rw [he,map_add,map_mul,ModFourResidues.reduce_four,zero_mul,map_one,add_zero]

noncomputable def principalUnits : R₂ →+ U E :=
  (q₂).toAddMonoidHom.liftOfSurjective Ideal.Quotient.mk_surjective ⟨principalHom E,principal_ker E⟩

@[simp] theorem principalUnits_reduce (a : 𝓞 E) :
    principalUnits E (q₂ a) = Additive.ofMul (principal E a) := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

noncomputable def principalClasses : R₂ →ₗ[ZMod 2] W E :=
  AddMonoidHom.toZModLinearMap 2 (ModTwo.mk.comp (principalUnits E))

@[simp] theorem principalClasses_reduce (a : 𝓞 E) :
    principalClasses E (q₂ a) = ModTwo.mk (Additive.ofMul (principal E a)) := by
  change ModTwo.mk (principalUnits E (q₂ a)) = _
  rw [principalUnits_reduce]

/-- Multiplication by two identifies the additive mod-two quotient with
principal units congruent to one modulo two. -/
theorem principalUnits_injective : Function.Injective (principalUnits E) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [principalUnits_reduce] at hx
  have he := congrArg (fun u : U E => (u.toMul : R₄)) hx
  change q₄ (1+2*a) = 1 at he
  rw [← map_one q₄] at he
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he)
  have hb' : 2*b = a := by
    have htwo : (2 : 𝓞 E) ≠ 0 := by norm_num
    apply mul_left_cancel₀ htwo
    linear_combination -hb
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨b,hb'.symm⟩

variable [IsReduced (ModTwoResidues.R E)]

private theorem square_eq_one (u : R₄ˣ) (hu : toTwo E ((u : R₄)^2) = 1) :
    toTwo E (u : R₄) = 1 := by
  apply frobenius_inj R₂ 2
  change (toTwo E (u : R₄))^2 = (1 : R₂)^2
  simpa only [map_pow,one_pow] using hu

/-- Every two-torsion unit is a principal unit. -/
theorem exists_principal (u : U E) (hu : u+u = 0) : ∃ x : R₂, principalUnits E x = u := by
  have hu' : (u.toMul : R₄)^2 = 1 := by
    have h := congrArg (fun u : U E => (u.toMul : R₄)) hu
    simpa only [pow_two] using h
  have hred : toTwo E (u.toMul : R₄) = 1 := square_eq_one E u.toMul (by rw [hu',map_one])
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective (u.toMul : R₄)
  change q₄ a = (u.toMul : R₄) at ha
  have ha' : q₂ a = q₂ 1 := by rw [← toTwo_reduce,ha,hred,map_one]
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp ha')
  have he : a = 1+2*b := by linear_combination hb
  refine ⟨q₂ b,?_⟩
  rw [principalUnits_reduce]
  apply Additive.toMul.injective
  apply Units.ext
  change q₄ (1+2*b) = (u.toMul : R₄)
  rw [← he,ha]

/-- The principal-unit map stays injective after quotienting by squares. -/
theorem principalClasses_injective : Function.Injective (principalClasses E) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change ModTwo.mk (principalUnits E x) = 0 at hx
  obtain ⟨u,hu⟩ := (ModTwo.mk_eq_zero _).mp hx
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [principalUnits_reduce] at hu
  have he := congrArg (fun u : U E => (u.toMul : R₄)) hu
  change (u.toMul : R₄)*(u.toMul : R₄) = q₄ (1+2*a) at he
  have hred : toTwo E (u.toMul : R₄) = 1 := by
    apply square_eq_one E u.toMul
    rw [pow_two,he,toTwo_reduce,map_add,map_mul,map_one,ModTwoResidues.reduce_two,zero_mul,add_zero]
  obtain ⟨b,hb⟩ := Ideal.Quotient.mk_surjective (u.toMul : R₄)
  change q₄ b = (u.toMul : R₄) at hb
  have hb' : q₂ b = q₂ 1 := by rw [← toTwo_reduce,hb,hred,map_one]
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hb')
  have hbc : b = 1+2*c := by linear_combination hc
  have hu0 : u+u = 0 := by
    apply Additive.toMul.injective
    apply Units.ext
    change (u.toMul : R₄)*(u.toMul : R₄) = 1
    rw [← hb,hbc]
    exact principal_sq E c
  apply principalUnits_injective E
  rw [map_zero,principalUnits_reduce,← hu,hu0]

/-- No local squareclass is missed by principal units. -/
theorem principalClasses_bijective : Function.Bijective (principalClasses E) := by
  letI : Finite (W E) := Finite.of_surjective ModTwo.mk ModTwo.mk_surjective
  apply (principalClasses_injective E).bijective_of_nat_card_le
  rw [ModNFinitelyGenerated.card_modN_of_finite (U E) 2]
  let f : R₂ → (ModNFinitelyGenerated.mulN (U E) 2).ker := fun x =>
    ⟨principalUnits E x,by
      change (2 : ℤ) • principalUnits E x = 0
      rw [two_zsmul]
      rw [← map_add,CharTwo.add_self_eq_zero,map_zero]⟩
  apply Nat.card_le_card_of_surjective f
  intro u
  have hu := u.property
  change (2 : ℤ) • u.1 = 0 at hu
  rw [two_zsmul] at hu
  obtain ⟨x,hx⟩ := exists_principal E u.1 hu
  exact ⟨x,Subtype.ext hx⟩

noncomputable def equiv : R₂ ≃ₗ[ZMod 2] W E :=
  LinearEquiv.ofBijective (principalClasses E) (principalClasses_bijective E)

end LocalResidueSquareclasses



/-! Integral trace is surjective for an everywhere-unramified extension. -/
namespace UnramifiedTrace
open NumberField
open scoped nonZeroDivisors Classical
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E]

noncomputable def trace : 𝓞 E →ₗ[𝓞 K] 𝓞 K where
  toFun x := ⟨Algebra.trace K E (x : E), Algebra.isIntegral_trace x.property⟩
  map_add' x y := by apply RingOfIntegers.coe_injective; exact map_add (Algebra.trace K E) _ _
  map_smul' r x := by
    apply RingOfIntegers.coe_injective
    change Algebra.trace K E ((algebraMap K E (r : K))*(x : E)) = (r : K)*Algebra.trace K E (x : E)
    simpa only [Algebra.smul_def,smul_eq_mul] using map_smul (Algebra.trace K E) (r : K) (x : E)

@[simp] theorem coe_trace (x : 𝓞 E) : (trace K E x : K) = Algebra.trace K E (x : E) := rfl

theorem traceDual_one (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  have h := coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)
  rw [hunram,FractionalIdeal.coeIdeal_top] at h
  have := congrArg (fun I : FractionalIdeal (𝓞 E)⁰ E => I⁻¹) h
  simpa only [inv_one,inv_inv] using this.symm

/-- The inverse of the trace ideal is integral when the codifferent is trivial. -/
theorem traceIdeal_inv_le_one (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (hJ : (LinearMap.range (trace K E) : Ideal (𝓞 K)) ≠ ⊥) :
    ((LinearMap.range (trace K E) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤ 1 := by
  intro x hx
  have hJ0 : ((LinearMap.range (trace K E) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_eq_zero.not.mpr hJ
  have hx' : ∀ y : 𝓞 E, x*Algebra.trace K E (y : E) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro y
    exact (FractionalIdeal.mem_inv_iff hJ0).mp hx _
      (FractionalIdeal.mem_coeIdeal_of_mem _ (show trace K E y ∈ LinearMap.range (trace K E) from ⟨y,rfl⟩))
  have hmem : algebraMap K E x ∈ FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (by simp)]
    intro y hy
    obtain ⟨b,rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy
    change Algebra.trace K E (algebraMap K E x*(b : E)) ∈ (algebraMap (𝓞 K) K).range
    have ht : Algebra.trace K E (algebraMap K E x*(b : E)) = x*Algebra.trace K E (b : E) := by
      simpa only [Algebra.smul_def,smul_eq_mul] using map_smul (Algebra.trace K E) x (b : E)
    rw [ht]
    exact (FractionalIdeal.mem_one_iff _).mp (hx' b)
  rw [traceDual_one K E hunram] at hmem
  obtain ⟨a,ha⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  have hi : IsIntegral ℤ (algebraMap K E x) := ha ▸ a.property
  have hxint : IsIntegral ℤ x := (isIntegral_algebraMap_iff (algebraMap K E).injective).mp hi
  exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x,hxint⟩,rfl⟩

theorem traceIdeal_ne_bot : (LinearMap.range (trace K E) : Ideal (𝓞 K)) ≠ ⊥ := by
  intro h
  have hz : trace K E 1 = 0 := by
    have hm : trace K E 1 ∈ LinearMap.range (trace K E) := ⟨1,rfl⟩
    rw [h] at hm
    exact hm
  have he := congrArg (fun x : 𝓞 K => (x : K)) hz
  change Algebra.trace K E 1 = 0 at he
  rw [← map_one (algebraMap K E),Algebra.trace_algebraMap] at he
  have hd : (Module.finrank K E : K) ≠ 0 := Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  exact hd (by simpa only [nsmul_eq_mul,mul_one] using he)

theorem trace_surjective (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Function.Surjective (trace K E) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  apply (FractionalIdeal.coeIdeal_le_coeIdeal K).mp
  rw [FractionalIdeal.coeIdeal_top]
  have h := traceIdeal_inv_le_one K E hunram (traceIdeal_ne_bot K E)
  have h' := (FractionalIdeal.inv_le_comm (A := 𝓞 K) (K := K) (J := 1)
    (FractionalIdeal.coeIdeal_eq_zero.not.mpr (traceIdeal_ne_bot K E)) (by simp)).mp h
  simpa only [inv_one] using h'

theorem exists_trace_one (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    ∃ t : 𝓞 E, Algebra.trace K E (t : E) = 1 := by
  obtain ⟨t,ht⟩ := trace_surjective K E hunram 1
  exact ⟨t,congrArg (fun x : 𝓞 K => (x : K)) ht⟩


variable [IsGalois K E]

theorem algebraMap_trace (x : 𝓞 E) :
    algebraMap (𝓞 K) (𝓞 E) (trace K E x) = ∑ g : Gal(E/K), RingOfIntegers.mapAlgEquiv g x := by
  apply RingOfIntegers.coe_injective
  change algebraMap K E (Algebra.trace K E (x : E)) = _
  rw [trace_eq_sum_automorphisms]
  simp only [map_sum]
  rfl

end UnramifiedTrace


namespace ModTwoResidues
open NumberField
open scoped Classical
variable (E K : Type*) [Field E] [Field K] [NumberField E] [NumberField K]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E]

/-- Integral trace-one averaging descends all invariant residues. -/
theorem extendFixed_surjective (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Function.Surjective (extendFixed E K) := by
  intro v
  obtain ⟨t,ht⟩ := UnramifiedTrace.exists_trace_one K E hunram
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective v.1
  change reduce E x = v.1 at hx
  refine ⟨reduce K (UnramifiedTrace.trace K E (t*x)),?_⟩
  apply Subtype.ext
  change extend E K (reduce K (UnramifiedTrace.trace K E (t*x))) = v.1
  rw [extend_reduce,UnramifiedTrace.algebraMap_trace,map_sum]
  have hgx (g : Gal(E/K)) : reduce E (RingOfIntegers.mapAlgEquiv g x) = v.1 := by
    rw [← action_reduce,hx]
    exact v.property g
  simp_rw [map_mul,hgx,← Finset.sum_mul,← map_sum,← UnramifiedTrace.algebraMap_trace]
  have ht' : UnramifiedTrace.trace K E t = 1 := RingOfIntegers.coe_injective ht
  rw [ht',map_one,map_one,one_mul]

/-- The invariant residue space has at most the absolute base degree dimensions. -/
theorem fixed_finrank_le (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (fixed E K) ≤ Module.finrank ℚ K := by
  rw [← finrank K]
  have h := LinearMap.finrank_range_le (extendFixed E K)
  rw [LinearMap.range_eq_top.mpr (extendFixed_surjective E K hunram),finrank_top] at h
  exact h

end ModTwoResidues


namespace ModFourResidues
open NumberField
open scoped Classical
variable (E K : Type*) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]

noncomputable def action (g : Gal(E/K)) : R E ≃+* R E :=
  Ideal.quotientEquiv (modulus E) (modulus E) (RingOfIntegers.mapAlgEquiv g).toRingEquiv
    (by simp only [modulus,Ideal.map_span,Set.image_singleton,map_ofNat])

@[simp] theorem action_reduce (g : Gal(E/K)) (a : 𝓞 E) :
    action E K g (reduce E a) = reduce E (RingOfIntegers.mapAlgEquiv g a) := rfl

theorem action_one (x : R E) : action E K 1 x = x := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem action_mul (g h : Gal(E/K)) (x : R E) : action E K (g*h) x = action E K g (action E K h x) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

noncomputable def unitAction : Gal(E/K) →* AddAut (Additive (R E)ˣ) where
  toFun g := (Units.mapEquiv (action E K g).toMulEquiv).toAdditive
  map_one' := by
    apply AddEquiv.ext
    intro u
    apply Additive.toMul.injective
    apply Units.ext
    exact action_one E K (u.toMul : R E)
  map_mul' g h := by
    apply AddEquiv.ext
    intro u
    apply Additive.toMul.injective
    apply Units.ext
    exact action_mul E K g h (u.toMul : R E)

@[simp] theorem unitAction_val (g : Gal(E/K)) (u : Additive (R E)ˣ) :
    ((unitAction E K g u).toMul : R E) = action E K g (u.toMul : R E) := rfl

theorem squareclass_action (g : Gal(E/K)) (a : 𝓞 E) (ha : IsUnit (reduce E a)) :
    squareclass E (RingOfIntegers.mapAlgEquiv g a) (by
      rw [← action_reduce]; exact ha.map (action E K g).toMonoidHom) =
      ModTwo.map (unitAction E K g).toAddMonoidHom (squareclass E a ha) := by
  simp only [squareclass,ModTwo.map_mk]
  apply congrArg ModTwo.mk
  apply Additive.toMul.injective
  apply Units.ext
  change (unit E (RingOfIntegers.mapAlgEquiv g a) _ : R E) = action E K g (unit E a ha : R E)
  simp only [unit_val,action_reduce]

end ModFourResidues

namespace LocalResidueSquareclasses
open NumberField
open scoped Classical
variable (E K : Type*) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]

theorem principalClasses_equivariant (g : Gal(E/K)) (x : ModTwoResidues.R E) :
    principalClasses E (ModTwoResidues.action E K g x) =
      ModTwo.map (ModFourResidues.unitAction E K g).toAddMonoidHom (principalClasses E x) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [ModTwoResidues.action_reduce,principalClasses_reduce,principalClasses_reduce,ModTwo.map_mk]
  apply congrArg ModTwo.mk
  apply Additive.toMul.injective
  apply Units.ext
  change ModFourResidues.reduce E (1+2*RingOfIntegers.mapAlgEquiv g a) =
    ModFourResidues.action E K g (ModFourResidues.reduce E (1+2*a))
  simp only [ModFourResidues.action_reduce,map_add,map_mul,map_one,map_ofNat]

variable [IsReduced (ModTwoResidues.R E)]

noncomputable def fixedToTwo : ModTwo.fixed (ModFourResidues.unitAction E K) →ₗ[ZMod 2]
    ModTwoResidues.fixed E K :=
  ((equiv E).symm.toLinearMap.comp (ModTwo.fixed (ModFourResidues.unitAction E K)).subtype).codRestrict _ (by
    intro w g
    apply (equiv E).injective
    change principalClasses E (ModTwoResidues.action E K g ((equiv E).symm w.1)) = _
    rw [principalClasses_equivariant]
    change ModTwo.map (ModFourResidues.unitAction E K g).toAddMonoidHom
      ((equiv E) ((equiv E).symm w.1)) = (equiv E) ((equiv E).symm w.1)
    rw [LinearEquiv.apply_symm_apply]
    exact w.property g)

theorem fixedToTwo_injective : Function.Injective (fixedToTwo E K) := by
  intro x y h
  apply Subtype.ext
  apply (equiv E).symm.injective
  exact congrArg Subtype.val h

variable [FiniteDimensional K E] [IsGalois K E]

theorem fixed_finrank_le (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (ModTwo.fixed (ModFourResidues.unitAction E K)) ≤ Module.finrank ℚ K := by
  exact (LinearMap.finrank_le_finrank_of_injective (fixedToTwo_injective E K)).trans
    (ModTwoResidues.fixed_finrank_le E K hunram)

end LocalResidueSquareclasses



namespace VirtualUnitResidues
open NumberField PrincipalInvolutionSequences GaloisCocycleActions
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable (E K : Type) [Field E] [Field K] [NumberField E] [NumberField K] [Algebra K E]

theorem integralClass_action (g : Gal(E/K)) (a : 𝓞 E) (ha : a ≠ 0) :
    integralClass E (RingOfIntegers.mapAlgEquiv g a) (by
      simpa only [map_zero] using (RingOfIntegers.mapAlgEquiv g).injective.ne ha) =
      ModTwo.map (fieldAction K E g).toAddMonoidHom (integralClass E a ha) := by
  unfold integralClass
  rw [ModTwo.map_mk]
  apply congrArg ModTwo.mk
  apply Additive.toMul.injective
  apply Units.ext
  rfl

theorem residue_fixed (v : VirtualClassObstruction.virtualFixed K E) :
    residue E (fromFixed E K v) ∈ ModTwo.fixed (ModFourResidues.unitAction E K) := by
  intro g
  let r := (exists_representative E (fromFixed E K v)).some
  let s : Representative E v.1.1 := {
    a := RingOfIntegers.mapAlgEquiv g r.a
    ne_zero := by simpa only [map_zero] using (RingOfIntegers.mapAlgEquiv g).injective.ne r.ne_zero
    unit := by
      rw [← ModFourResidues.action_reduce E K]
      exact r.unit.map (ModFourResidues.action E K g).toMonoidHom
    class_eq := by
      rw [integralClass_action E K g r.a r.ne_zero,r.class_eq]
      exact v.1.property g }
  have hr := residue_of_representative E (fromFixed E K v) r
  have hs := residue_of_representative E (fromFixed E K v) s
  rw [hr]
  change ModTwo.map (ModFourResidues.unitAction E K g).toAddMonoidHom
    (ModFourResidues.squareclass E r.a r.unit) = ModFourResidues.squareclass E r.a r.unit
  rw [← ModFourResidues.squareclass_action E K g r.a r.unit]
  exact hs.symm.trans hr

noncomputable def fixedResidue : VirtualClassObstruction.virtualFixed K E →ₗ[ZMod 2]
    ModTwo.fixed (ModFourResidues.unitAction E K) :=
  ((residueLinear E).comp (fromFixed E K)).codRestrict _ (residue_fixed E K)

variable [IsTotallyReal E] [FiniteDimensional K E] [IsGalois K E]

noncomputable def localFixedSigns : VirtualClassObstruction.virtualFixed K E →ₗ[ZMod 2]
    ModTwo.fixed (ModFourResidues.unitAction E K) × ((K →+* ℂ) → ZMod 2) :=
  (fixedResidue E K).prod
    ((SquareclassSigns.fixedSigns E K).comp (VirtualClassObstruction.virtualFixed K E).subtype)

theorem localFixedSigns_injective (hterm : SquareCriterion E) :
    Function.Injective (localFixedSigns E K) := by
  intro x y h
  apply localSigns_injective E K hterm
  apply Prod.ext
  · exact congrArg (fun z : ModTwo.fixed (ModFourResidues.unitAction E K) × ((K →+* ℂ) → ZMod 2) => z.1.1) h
  · exact congrArg (fun z : ModTwo.fixed (ModFourResidues.unitAction E K) × ((K →+* ℂ) → ZMod 2) => z.2) h

/-- The arithmetic virtual-unit bound at a terminal unramified layer. -/
theorem virtualFixed_finrank_le (hterm : SquareCriterion E)
    [IsReduced (ModTwoResidues.R E)]
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) :
    Module.finrank (ZMod 2) (VirtualClassObstruction.virtualFixed K E) ≤ 2*Module.finrank ℚ K := by
  letI : Finite (ModTwo.V (Additive (ModFourResidues.R E)ˣ)) :=
    Finite.of_surjective ModTwo.mk ModTwo.mk_surjective
  letI : FiniteDimensional (ZMod 2) (ModTwo.fixed (ModFourResidues.unitAction E K)) :=
    Module.Finite.of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (localFixedSigns_injective E K hterm)
  rw [Module.finrank_prod,SquareclassSigns.signs_finrank] at h
  have hres := LocalResidueSquareclasses.fixed_finrank_le E K hunram
  omega

/-- Terminality also supplies the finiteness needed by the cohomological bound. -/
theorem virtualFixed_finiteDimensional (hterm : SquareCriterion E) :
    FiniteDimensional (ZMod 2) (VirtualClassObstruction.virtualFixed K E) := by
  letI : Finite (ModTwo.V (Additive (ModFourResidues.R E)ˣ)) :=
    Finite.of_surjective ModTwo.mk ModTwo.mk_surjective
  letI : FiniteDimensional (ZMod 2) (ModTwo.fixed (ModFourResidues.unitAction E K)) :=
    Module.Finite.of_finite
  exact FiniteDimensional.of_injective (localFixedSigns E K) (localFixedSigns_injective E K hterm)

end VirtualUnitResidues


namespace VirtualClassObstruction
open NumberField PrincipalInvolutionSequences
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [IsTotallyReal K] [IsTotallyReal E]

/-- The constant arithmetic relation bound at a terminal unramified layer. -/
theorem terminal_relation_bound (hG : IsPGroup 2 Gal(E/K))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤)
    (hterm : VirtualUnitResidues.SquareCriterion E)
    [IsReduced (ModTwoResidues.R E)] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Gal(E/K) (ZMod 2)) 2) ≤
      Module.finrank (ZMod 2) (ModTwo.V (C K))+2*Module.finrank ℚ K := by
  letI := VirtualUnitResidues.virtualFixed_finiteDimensional E K hterm
  exact (relation_bound K E hG hunram).trans
    (Nat.add_le_add_left (VirtualUnitResidues.virtualFixed_finrank_le E K hterm hunram) _)

end VirtualClassObstruction



/- The finite p-group algebra form of the Golod--Shafarevich bound. -/


/- Minimal free presentations of finite modular p-group representations. -/


/- Nonzero representations of finite p-groups over F_p have invariant
vectors and nonzero invariant linear functionals. -/

namespace PGroupRepresentation
open scoped Classical

variable (p : ℕ) [Fact p.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

/-- The orbit-counting proof of the fixed-vector property. -/
theorem exists_fixed [Nontrivial V] (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  letI : Finite V := Finite.of_equiv (Fin (Module.finrank (ZMod p) V) → ZMod p)
    (Module.finBasis (ZMod p) V).equivFun.symm.toEquiv
  letI : MulAction G V := {
    smul := fun g v => ρ g v
    one_smul := fun v => by change ρ 1 v = v; rw [map_one]; rfl
    mul_smul := fun g h v => by change ρ (g*h) v = ρ g (ρ h v); rw [map_mul]; rfl }
  have hpV : p ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_eq_fintype_card,ZMod.card]
    have hd : 0 < Module.finrank (ZMod p) V := Module.finrank_pos
    rw [← Nat.succ_pred_eq_of_pos hd,pow_succ]
    exact dvd_mul_left _ _
  have hz : (0 : V) ∈ MulAction.fixedPoints G V := by
    apply MulAction.mem_fixedPoints.mpr
    intro g
    exact (ρ g).map_zero
  obtain ⟨v,hv,hv0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV hz
  exact ⟨v,hv0.symm,MulAction.mem_fixedPoints.mp hv⟩

/-- Dualizing gives a nonzero trivial quotient. -/
theorem exists_invariant_functional [Nontrivial V] (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V) :
    ∃ f : Module.Dual (ZMod p) V, f ≠ 0 ∧ ∀ g : G, ∀ v : V, f (ρ g v) = f v := by
  obtain ⟨f,hf,hfix⟩ := exists_fixed p hG ρ.dual
  refine ⟨f,hf,?_⟩
  intro g v
  have hh := congrArg (fun f : Module.Dual (ZMod p) V => f v) (hfix g⁻¹)
  simpa only [Representation.dual_apply,Module.Dual.transpose_apply,inv_inv,LinearMap.coe_comp,Function.comp_apply] using hh

end PGroupRepresentation

namespace AugmentationModule
open scoped Classical

variable (k G : Type*) [Field k] [Group G]

noncomputable def augmentation : MonoidAlgebra k G →ₐ[k] k := MonoidAlgebra.lift k k G (1 : G →* k)

noncomputable def ideal : Ideal (MonoidAlgebra k G) := RingHom.ker (augmentation k G).toRingHom

instance : (ideal k G).IsTwoSided := inferInstanceAs (RingHom.ker (augmentation k G).toRingHom).IsTwoSided

@[simp] theorem augmentation_single (g : G) (r : k) : augmentation k G (MonoidAlgebra.single g r) = r := by
  simp [augmentation,MonoidAlgebra.lift_single]

@[simp] theorem augmentation_of (g : G) : augmentation k G (MonoidAlgebra.of k G g) = 1 := by
  exact augmentation_single k G g 1

theorem mem_ideal (a : MonoidAlgebra k G) : a ∈ ideal k G ↔ augmentation k G a = 0 := Iff.rfl

theorem ideal_ne_top : ideal k G ≠ ⊤ := by
  intro h
  have hh : (1 : MonoidAlgebra k G) ∈ ideal k G := by rw [h]; trivial
  change augmentation k G 1 = 0 at hh
  simp at hh

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]

/-- An invariant linear functional transforms group-algebra multiplication
by the augmentation character. -/
theorem map_smul (f : M →ₗ[k] k)
    (hf : ∀ g : G, ∀ v : M, f (MonoidAlgebra.of k G g • v) = f v)
    (a : MonoidAlgebra k G) (v : M) : f (a • v) = augmentation k G a * f v := by
  induction a using MonoidAlgebra.induction_on with
  | hM g => simpa only [augmentation_of,one_mul] using hf g v
  | hadd a b ha hb => rw [add_smul,map_add,ha,hb,map_add,add_mul]
  | hsmul r a ha =>
    have hau : augmentation k G (r • a) = r • augmentation k G a :=
      (augmentation k G).toLinearMap.map_smul r a
    rw [smul_assoc,f.map_smul,ha,hau]
    simp only [smul_eq_mul,mul_assoc]

/-- The augmentation ideal of a p-group cannot generate a nonzero finite
F_p-module. This is the modular Nakayama property proved by orbit counting. -/
theorem smul_ne_top (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] [Module (MonoidAlgebra (ZMod p) G) M]
    [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
    [FiniteDimensional (ZMod p) M] [Nontrivial M] (hG : IsPGroup p G) :
    ideal (ZMod p) G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) M) ≠ ⊤ := by
  obtain ⟨f,hf,hfix⟩ := PGroupRepresentation.exists_invariant_functional p hG (Representation.ofModule' M)
  have hfi : ∀ g : G, ∀ v : M, f (MonoidAlgebra.of (ZMod p) G g • v) = f v := hfix
  intro he
  apply hf
  ext v
  have hv : v ∈ ideal (ZMod p) G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) M) := by rw [he]; trivial
  change f v = 0
  exact Submodule.smul_induction_on hv (fun a ha v _ => by
    rw [map_smul (ZMod p) G f hfi, (mem_ideal _ _ _).mp ha,zero_mul])
    (fun x y hx hy => by rw [_root_.map_add,hx,hy,add_zero])

end AugmentationModule

namespace AugmentationModule
open scoped Classical

variable (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
  [Module (MonoidAlgebra (ZMod p) G) M]
  [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
  [FiniteDimensional (ZMod p) M]

/-- Nakayama's lemma for finite modular representations of a p-group. -/
theorem eq_top_of_sup_smul_eq_top (hG : IsPGroup p G)
    (N : Submodule (MonoidAlgebra (ZMod p) G) M)
    (hN : N ⊔ ideal (ZMod p) G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) M) = ⊤) :
    N = ⊤ := by
  by_contra hne
  letI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.mpr hne
  letI : FiniteDimensional (ZMod p) (M ⧸ N) := Module.Finite.of_surjective
    (N.mkQ.restrictScalars (ZMod p)) N.mkQ_surjective
  have hh : Submodule.map N.mkQ (ideal (ZMod p) G • (⊤ : Submodule (MonoidAlgebra (ZMod p) G) M)) = ⊤ :=
    (Submodule.map_mkQ_eq_top N _).mpr hN
  rw [Submodule.map_smul'',Submodule.map_top,Submodule.range_mkQ] at hh
  exact smul_ne_top G p hG hh

end AugmentationModule


/- Quotient-dimension inequalities for a filtered exact sequence. -/

namespace FilteredExactDimension

variable {k M N P : Type*} [Field k] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module k M] [Module k N] [Module k P]

/-- Quotienting an exact sequence remains exact in the middle if the image
of the first filtration piece is exactly the last filtration piece. -/
theorem quotient_exact (f : M →ₗ[k] N) (g : P →ₗ[k] M)
    (hex : f.ker = g.range) (D : Submodule k M) (E : Submodule k N) (F : Submodule k P)
    (hf : D.map f = E) (hg : F ≤ D.comap g) :
    Function.Exact (F.mapQ D g hg) (D.mapQ E f (by rw [← hf]; exact Submodule.le_comap_map f D)) := by
  rw [LinearMap.exact_iff]
  ext v
  obtain ⟨x,rfl⟩ := D.mkQ_surjective v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have hfx : f x ∈ E := (Submodule.Quotient.mk_eq_zero E).mp hx
    rw [← hf] at hfx
    obtain ⟨y,hy,hxy⟩ := hfx
    have hker : x-y ∈ f.ker := by simp only [LinearMap.mem_ker,map_sub,hxy,sub_self]
    rw [hex] at hker
    obtain ⟨z,hz⟩ := hker
    refine ⟨F.mkQ z,?_⟩
    change D.mkQ (g z) = D.mkQ x
    rw [hz,map_sub]
    have hy0 : D.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero D).mpr hy
    rw [hy0,sub_zero]
  · rintro ⟨z,hz⟩
    obtain ⟨p,rfl⟩ := F.mkQ_surjective z
    have hgp : f (g p) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hex]
      exact LinearMap.mem_range_self _ _
    rw [← hz]
    change E.mkQ (f (g p)) = 0
    rw [hgp,map_zero]

/-- The filtered GS recurrence is a consequence of this elementary
finite-dimensional quotient inequality. -/
theorem quotient_finrank_le [FiniteDimensional k M] [FiniteDimensional k N] [FiniteDimensional k P]
    (f : M →ₗ[k] N) (g : P →ₗ[k] M)
    (hex : f.ker = g.range) (D : Submodule k M) (E : Submodule k N) (F : Submodule k P)
    (hf : D.map f = E) (hg : F ≤ D.comap g) :
    Module.finrank k (M ⧸ D) ≤ Module.finrank k (N ⧸ E)+Module.finrank k (P ⧸ F) := by
  let f' := D.mapQ E f (by rw [← hf]; exact Submodule.le_comap_map f D)
  let g' := F.mapQ D g hg
  have he : f'.ker = g'.range := LinearMap.exact_iff.mp (quotient_exact f g hex D E F hf hg)
  have hh := f'.finrank_range_add_finrank_ker
  rw [he] at hh
  have h₁ : Module.finrank k f'.range ≤ Module.finrank k (N ⧸ E) := Submodule.finrank_le _
  have h₂ := g'.finrank_range_le
  omega

end FilteredExactDimension

namespace GSFiltration
open scoped Classical BigOperators

variable {A : Type*} [Ring A]

/-- On a finite free module, ideal multiplication gives the coordinatewise
ideal filtration. Two-sidedness is essential here. -/
theorem smul_top_eq_pi (I : Ideal A) [I.IsTwoSided] (ι : Type*) [Fintype ι] :
    I • (⊤ : Submodule A (ι → A)) = Submodule.pi Set.univ (fun _ : ι => I) := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro r hr v _
    apply Submodule.mem_pi.mpr
    intro i _
    exact I.mul_mem_right (v i) hr
  · intro v hv
    rw [pi_eq_sum_univ v]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem_smul ((Submodule.mem_pi.mp hv) i trivial) Submodule.mem_top

variable (k : Type*) [Field k] [Algebra k A] [FiniteDimensional k A]

theorem quotient_free_finrank (I : Ideal A) [I.IsTwoSided] (d : ℕ) :
    Module.finrank k ((Fin d → A) ⧸ (I • (⊤ : Submodule A (Fin d → A))).restrictScalars k) =
      d*Module.finrank k (A ⧸ I.restrictScalars k) := by
  rw [smul_top_eq_pi]
  change Module.finrank k ((Fin d → A) ⧸ Submodule.pi Set.univ (fun _ : Fin d => I.restrictScalars k)) = _
  rw [(Submodule.quotientPi (fun _ : Fin d => I.restrictScalars k)).finrank_eq]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

/-- A minimal two-step free presentation forces the GS recurrence on
successive augmentation quotients. -/
theorem quotient_recurrence (I : Ideal A) [I.IsTwoSided] (d r : ℕ)
    (f : (Fin d → A) →ₗ[A] A) (g : (Fin r → A) →ₗ[A] (Fin d → A))
    (hI : f.range = I) (hex : f.ker = g.range)
    (hmin : f.ker ≤ I • (⊤ : Submodule A (Fin d → A))) (n : ℕ) :
    d*Module.finrank k (A ⧸ (I^(n+1)).restrictScalars k) ≤
      Module.finrank k (A ⧸ (I^(n+2)).restrictScalars k)+
        r*Module.finrank k (A ⧸ (I^n).restrictScalars k) := by
  let D := (I^(n+1) • (⊤ : Submodule A (Fin d → A))).restrictScalars k
  let E := (I^(n+2)).restrictScalars k
  let F := (I^n • (⊤ : Submodule A (Fin r → A))).restrictScalars k
  have hf : D.map (f.restrictScalars k) = E := by
    dsimp only [D,E]
    rw [← Submodule.restrictScalars_map,Submodule.map_smul'',Submodule.map_top,hI,Ideal.smul_eq_mul]
    congr 1
  have hg : F ≤ D.comap (g.restrictScalars k) := by
    apply Submodule.map_le_iff_le_comap.mp
    dsimp only [D,F]
    rw [← Submodule.restrictScalars_map,Submodule.map_smul'',Submodule.map_top,← hex]
    apply Submodule.restrictScalars_mono k
    calc
      I^n • f.ker ≤ I^n • (I • (⊤ : Submodule A (Fin d → A))) := Submodule.smul_mono le_rfl hmin
      _ = I^(n+1) • (⊤ : Submodule A (Fin d → A)) := by rw [← Submodule.mul_smul,← Submodule.pow_succ]
  have hhex : (f.restrictScalars k).ker = (g.restrictScalars k).range := by
    rw [LinearMap.ker_restrictScalars,LinearMap.range_restrictScalars,hex]
  have hh := FilteredExactDimension.quotient_finrank_le (f.restrictScalars k) (g.restrictScalars k)
    hhex D E F hf hg
  simpa only [D,E,F,quotient_free_finrank] using hh

end GSFiltration

namespace MinimalPGroupModule
open scoped Classical BigOperators

variable (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
variable (M : Type*) [AddCommGroup M] [Module (ZMod p) M]
  [Module (MonoidAlgebra (ZMod p) G) M]
  [IsScalarTower (ZMod p) (MonoidAlgebra (ZMod p) G) M]
  [FiniteDimensional (ZMod p) M]

noncomputable def coinvariantKernel : Submodule (MonoidAlgebra (ZMod p) G) M :=
  AugmentationModule.ideal (ZMod p) G • ⊤

noncomputable instance : Module.Finite (ZMod p) (M ⧸ coinvariantKernel G p M) :=
  Module.Finite.of_surjective ((coinvariantKernel G p M).mkQ.restrictScalars (ZMod p))
    (coinvariantKernel G p M).mkQ_surjective

noncomputable def generatorRank : ℕ := Module.finrank (ZMod p) (M ⧸ coinvariantKernel G p M)

omit [FiniteDimensional (ZMod p) M] in
/-- Scalars act on coinvariants through augmentation. -/
theorem quotient_smul (a : MonoidAlgebra (ZMod p) G) (v : M) :
    (coinvariantKernel G p M).mkQ (a • v) =
      AugmentationModule.augmentation (ZMod p) G a • (coinvariantKernel G p M).mkQ v := by
  let ε := AugmentationModule.augmentation (ZMod p) G
  let N := coinvariantKernel G p M
  have ha : a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a) ∈ AugmentationModule.ideal (ZMod p) G := by
    rw [AugmentationModule.mem_ideal,map_sub,AlgHom.commutes]; simp only [Algebra.algebraMap_self,RingHom.id_apply,ε,sub_self]
  have hv : (a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a)) • v ∈ N :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  have hq : N.mkQ ((a-algebraMap (ZMod p) (MonoidAlgebra (ZMod p) G) (ε a)) • v) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr hv
  rw [sub_smul,map_sub,algebraMap_smul] at hq
  have hs : N.mkQ (ε a • v) = ε a • N.mkQ v := (N.mkQ.restrictScalars (ZMod p)).map_smul _ _
  rw [hs,sub_eq_zero] at hq
  exact hq

/-- Lifts of a basis of the coinvariants give a minimal free cover. -/
theorem exists_minimal_surjection (hG : IsPGroup p G) :
    ∃ f : (Fin (generatorRank G p M) → MonoidAlgebra (ZMod p) G) →ₗ[MonoidAlgebra (ZMod p) G] M,
      Function.Surjective f ∧
      f.ker ≤ AugmentationModule.ideal (ZMod p) G •
        (⊤ : Submodule (MonoidAlgebra (ZMod p) G) (Fin (generatorRank G p M) → MonoidAlgebra (ZMod p) G)) := by
  let A := MonoidAlgebra (ZMod p) G
  let ε := AugmentationModule.augmentation (ZMod p) G
  let N := coinvariantKernel G p M
  let B := Module.finBasis (ZMod p) (M ⧸ N)
  have hlift : ∀ i : Fin (generatorRank G p M), ∃ x : M, N.mkQ x = B i :=
    fun i => N.mkQ_surjective (B i)
  choose lift hlift using hlift
  let f : (Fin (generatorRank G p M) → A) →ₗ[A] M := Fintype.linearCombination A lift
  have hq (c : Fin (generatorRank G p M) → A) :
      N.mkQ (f c) = ∑ i, ε (c i) • B i := by
    rw [Fintype.linearCombination_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [quotient_smul,hlift]
  have hsurj : Function.Surjective (N.mkQ.comp f) := by
    intro v
    refine ⟨fun i => algebraMap (ZMod p) A (B.repr v i),?_⟩
    change N.mkQ (f _) = v
    rw [hq]
    simp only [A,ε,AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply]
    exact B.sum_repr v
  have ht : f.range = ⊤ := by
    apply AugmentationModule.eq_top_of_sup_smul_eq_top G p hG
    rw [sup_comm]
    apply (Submodule.map_mkQ_eq_top N f.range).mp
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr hsurj
  refine ⟨f,LinearMap.range_eq_top.mp ht,?_⟩
  rw [GSFiltration.smul_top_eq_pi]
  intro c hc
  have hz : ∑ i, ε (c i) • B i = 0 := by
    rw [← hq,LinearMap.mem_ker.mp hc,map_zero]
  have hzero := Fintype.linearIndependent_iff.mp B.linearIndependent _ hz
  apply Submodule.mem_pi.mpr
  intro i _
  exact (AugmentationModule.mem_ideal _ _ _).mpr (hzero i)

end MinimalPGroupModule


/- The numerical heart of the Golod--Shafarevich inequality. This file does
not yet supply the group-algebra or arithmetic hypotheses. -/

namespace GolodShafarevichArithmetic

/-- Uniform growth forced by the GS recurrence. -/
theorem growth_of_recurrence (d r : ℕ) (hr : 4*r ≤ d^2)
    (a : ℕ → ℕ) (ha1 : d*a 0 ≤ 2*a 1)
    (hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n) : ∀ n, d*a n ≤ 2*a (n+1) := by
  intro n
  induction n with
  | zero => exact ha1
  | succ n ih =>
    have h₁ := Nat.mul_le_mul_left d ih
    have h₂ := Nat.mul_le_mul_right (a n) hr
    have h₃ := Nat.mul_le_mul_left (2*d) (hrec n)
    have hn := hrec n
    have ht : 2*r*a n ≤ d*a (n+1) := by nlinarith
    nlinarith

/-- A nonnegative coefficient sequence satisfying the Golod--Shafarevich
recurrence cannot terminate when the relation count is at most d²/4. -/
theorem positive_of_recurrence (d r : ℕ) (hd : 0 < d) (hr : 4*r ≤ d^2)
    (a : ℕ → ℕ) (ha0 : 0 < a 0) (ha1 : d*a 0 ≤ 2*a 1)
    (hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n) : ∀ n, 0 < a n := by
  have hg := growth_of_recurrence d r hr a ha1 hrec
  intro n
  induction n with
  | zero => exact ha0
  | succ n ih =>
    have hh : 0 < d*a n := Nat.mul_pos hd ih
    have hle := hg n
    omega

/-- The finite-dimensional version of the numerical GS obstruction. -/
theorem strict_relation_bound (d r : ℕ) (hd : 0 < d)
    (a : ℕ → ℕ) (ha0 : 0 < a 0) (ha1 : d*a 0 ≤ 2*a 1)
    (hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n) (hfinite : ∃ n, a n = 0) :
    d^2 < 4*r := by
  by_contra h
  have hp := positive_of_recurrence d r hd (Nat.le_of_not_gt h) a ha0 ha1 hrec
  obtain ⟨n,hn⟩ := hfinite
  have hh := hp n
  omega

/-- The usual arithmetic relation-rank upper bound contradicts finiteness
once the generator rank exceeds the GS threshold. -/
theorem infinite_of_relation_bound (d r N : ℕ) (hd : 0 < d)
    (hrel : r ≤ d+N) (hthreshold : 4*(d+N) ≤ d^2)
    (a : ℕ → ℕ) (ha0 : 0 < a 0) (ha1 : d*a 0 ≤ 2*a 1)
    (hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n) :
    ∀ n, a n ≠ 0 := by
  exact fun n => Nat.ne_of_gt (positive_of_recurrence d r hd (by omega) a ha0 ha1 hrec n)

/-- Cumulative Hilbert coefficients cannot stay bounded above when the
GS threshold is violated. This form avoids assumptions about homogeneity
or about the individual associated-graded coefficients. -/
theorem unbounded_of_recurrence (d r : ℕ) (hd : 3 ≤ d) (hr : 4*r ≤ d^2)
    (a : ℕ → ℕ) (ha0 : 0 < a 0) (ha1 : d*a 0 ≤ 2*a 1)
    (hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n) : ∀ n, n < a n := by
  have hg := growth_of_recurrence d r hr a ha1 hrec
  intro n
  induction n with
  | zero => exact ha0
  | succ n ih =>
    have hh := hg n
    have hm := Nat.mul_le_mul_right (a n) hd
    omega

end GolodShafarevichArithmetic

namespace GSAlgebra
open scoped Classical

/-- The Golod--Shafarevich inequality for a finite-dimensional algebra with
a proper two-sided ideal and a minimal two-step free presentation. -/
theorem relation_bound {A : Type*} [Ring A] (k : Type*) [Field k] [Algebra k A]
    [FiniteDimensional k A] (I : Ideal A) [I.IsTwoSided] (hIproper : I ≠ ⊤)
    (d r : ℕ) (hd : 3 ≤ d)
    (f : (Fin d → A) →ₗ[A] A) (g : (Fin r → A) →ₗ[A] (Fin d → A))
    (hI : f.range = I) (hex : f.ker = g.range)
    (hmin : f.ker ≤ I • (⊤ : Submodule A (Fin d → A))) : d^2 < 4*r := by
  let a := fun n : ℕ => Module.finrank k (A ⧸ (I^(n+1)).restrictScalars k)
  have hc (n : ℕ) := GSFiltration.quotient_recurrence k I d r f g hI hex hmin n
  have ha0 : 0 < a 0 := by
    have hp : I.restrictScalars k ≠ ⊤ := by
      intro h
      apply hIproper
      apply top_unique
      intro x _
      change x ∈ I.restrictScalars k
      rw [h]
      trivial
    letI : Nontrivial (A ⧸ I.restrictScalars k) := Submodule.Quotient.nontrivial_iff.mpr hp
    change 0 < Module.finrank k (A ⧸ (I^1).restrictScalars k)
    rw [Submodule.pow_one]
    exact Module.finrank_pos
  have ha1 : d*a 0 ≤ 2*a 1 := by
    have hh := hc 0
    have hz : Module.finrank k (A ⧸ (I^0).restrictScalars k) = 0 := by
      have he : I^0 = ⊤ := by rw [Submodule.pow_zero]; exact Ideal.one_eq_top
      rw [he,Submodule.restrictScalars_top]
      exact Module.finrank_zero_of_subsingleton
    rw [hz,mul_zero,add_zero] at hh
    change d*a 0 ≤ a 1 at hh
    omega
  have hrec : ∀ n, d*a (n+1) ≤ a (n+2)+r*a n := by
    intro n
    exact hc (n+1)
  by_contra h
  have hg := GolodShafarevichArithmetic.unbounded_of_recurrence d r hd (Nat.le_of_not_gt h) a ha0 ha1 hrec
  have hh := hg (Module.finrank k A)
  have hb := ((I^(Module.finrank k A+1)).restrictScalars k).finrank_quotient_le
  exact (not_lt_of_ge hb) hh

end GSAlgebra

namespace GSGroupAlgebra
open scoped Classical

variable (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- Any minimal free cover of the augmentation ideal of a finite p-group
has a relation module satisfying the Golod--Shafarevich inequality. -/
theorem relation_bound (hG : IsPGroup p G) (d : ℕ) (hd : 3 ≤ d)
    (f : (Fin d → MonoidAlgebra (ZMod p) G) →ₗ[MonoidAlgebra (ZMod p) G]
      AugmentationModule.ideal (ZMod p) G)
    (hf : Function.Surjective f)
    (hmin : f.ker ≤ AugmentationModule.ideal (ZMod p) G •
      (⊤ : Submodule (MonoidAlgebra (ZMod p) G) (Fin d → MonoidAlgebra (ZMod p) G))) :
    d^2 < 4*MinimalPGroupModule.generatorRank G p f.ker := by
  let A := MonoidAlgebra (ZMod p) G
  let I := AugmentationModule.ideal (ZMod p) G
  let f' : (Fin d → A) →ₗ[A] A := I.subtype.comp f
  have hker : f'.ker = f.ker := by
    ext v
    change ((f v : I) : A) = 0 ↔ f v = 0
    exact Submodule.coe_eq_zero
  have hf' : f'.range = I := by
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr hf,Submodule.map_top,Submodule.range_subtype]
  letI : FiniteDimensional (ZMod p) f.ker := inferInstanceAs
    (FiniteDimensional (ZMod p) (f.ker.restrictScalars (ZMod p)))
  obtain ⟨g,hg,_⟩ := MinimalPGroupModule.exists_minimal_surjection G p f.ker hG
  let g' := f.ker.subtype.comp g
  have hg' : g'.range = f'.ker := by
    rw [hker,LinearMap.range_comp,LinearMap.range_eq_top.mpr hg,Submodule.map_top,Submodule.range_subtype]
  exact GSAlgebra.relation_bound (ZMod p) I (AugmentationModule.ideal_ne_top _ _) d
    (MinimalPGroupModule.generatorRank G p f.ker) hd f' g' hf' hg'.symm (hker ▸ hmin)

/-- Existence of a minimal presentation at the generator rank. This is the
form that will need to be related to arithmetic generator/relation ranks. -/
theorem exists_minimal_presentation (hG : IsPGroup p G)
    (hd : 3 ≤ MinimalPGroupModule.generatorRank G p (AugmentationModule.ideal (ZMod p) G)) :
    ∃ f : (Fin (MinimalPGroupModule.generatorRank G p (AugmentationModule.ideal (ZMod p) G)) →
      MonoidAlgebra (ZMod p) G) →ₗ[MonoidAlgebra (ZMod p) G] AugmentationModule.ideal (ZMod p) G,
      Function.Surjective f ∧
      (MinimalPGroupModule.generatorRank G p (AugmentationModule.ideal (ZMod p) G))^2 <
        4*MinimalPGroupModule.generatorRank G p f.ker := by
  obtain ⟨f,hf,hmin⟩ := MinimalPGroupModule.exists_minimal_surjection G p (AugmentationModule.ideal (ZMod p) G) hG
  exact ⟨f,hf,relation_bound G p hG _ hd f hf hmin⟩

end GSGroupAlgebra

/- A direct representation wrapper for modules over a group algebra. -/

noncomputable section
namespace RepModule
open CategoryTheory
universe u
variable (k G : Type u) [Field k] [Group G]
variable (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]

abbrev of : Rep k G := Rep.of (Representation.ofModule' M)

def asModuleEquiv : (of k G M).ρ.asModule ≃ₗ[MonoidAlgebra k G] M :=
  { (of k G M).ρ.asModuleEquiv.toAddEquiv with
    map_smul' := fun a x => by
      change (of k G M).ρ.asModuleEquiv (a • x) = a • (of k G M).ρ.asModuleEquiv x
      rw [Representation.asModuleEquiv_map_smul]
      change (Representation.ofModule' M).asAlgebraHom a _ = _
      simp [Representation.ofModule',Representation.asAlgebraHom] }

instance [Module.Free (MonoidAlgebra k G) M] : Projective (of k G M) := by
  apply Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective
  exact ModuleCat.projective_of_free
    ((Module.Free.chooseBasis (MonoidAlgebra k G) M).map (asModuleEquiv k G M).symm)

variable {M}
variable {N : Type u} [AddCommGroup N] [Module k N] [Module (MonoidAlgebra k G) N]
  [IsScalarTower k (MonoidAlgebra k G) N]

def map (f : M →ₗ[MonoidAlgebra k G] N) : of k G M ⟶ of k G N where
  hom := ModuleCat.ofHom (f.restrictScalars k)
  comm g := by
    ext x
    exact f.map_smul (MonoidAlgebra.of k G g) x

@[simp] theorem map_hom_apply (f : M →ₗ[MonoidAlgebra k G] N) (x : M) :
    (map k G f).hom x = f x := rfl

end RepModule

namespace RepModule
open CategoryTheory
universe u
variable (k G : Type u) [Field k] [Group G]
variable (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
  [IsScalarTower k (MonoidAlgebra k G) M]

noncomputable def coinvariantKernel : Submodule (MonoidAlgebra k G) M :=
  AugmentationModule.ideal k G • ⊤

theorem hom_vanish (f : of k G M ⟶ Rep.trivial k G k)
    {v : M} (hv : v ∈ coinvariantKernel k G M) : f.hom v = 0 := by
  have hf : ∀ g : G, ∀ v : M, f.hom (MonoidAlgebra.of k G g • v) = f.hom v :=
    fun g v => Rep.hom_comm_apply f g v
  exact Submodule.smul_induction_on hv (fun a ha v _ => by
    rw [AugmentationModule.map_smul k G f.hom.hom hf,
      (AugmentationModule.mem_ideal _ _ _).mp ha,zero_mul])
    (fun x y hx hy => by rw [map_add,hx,hy,add_zero])

theorem quotient_smul (a : MonoidAlgebra k G) (v : M) :
    (coinvariantKernel k G M).mkQ (a • v) =
      AugmentationModule.augmentation k G a • (coinvariantKernel k G M).mkQ v := by
  let ε := AugmentationModule.augmentation k G
  let N := coinvariantKernel k G M
  have ha : a-algebraMap k (MonoidAlgebra k G) (ε a) ∈ AugmentationModule.ideal k G := by
    rw [AugmentationModule.mem_ideal,map_sub,AlgHom.commutes]
    simp only [Algebra.algebraMap_self,RingHom.id_apply,ε,sub_self]
  have hv : (a-algebraMap k (MonoidAlgebra k G) (ε a)) • v ∈ N :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  have hq : N.mkQ ((a-algebraMap k (MonoidAlgebra k G) (ε a)) • v) = 0 :=
    (Submodule.Quotient.mk_eq_zero N).mpr hv
  rw [sub_smul,map_sub,algebraMap_smul] at hq
  have hs : N.mkQ (ε a • v) = ε a • N.mkQ v := (N.mkQ.restrictScalars k).map_smul _ _
  rw [hs,sub_eq_zero] at hq
  exact hq

noncomputable def toCoinvariantDual (f : of k G M ⟶ Rep.trivial k G k) :
    Module.Dual k (M ⧸ coinvariantKernel k G M) :=
  (coinvariantKernel k G M).restrictScalars k |>.liftQ f.hom.hom
    (fun _ hv => hom_vanish k G M f hv)

noncomputable def fromCoinvariantDual (f : Module.Dual k (M ⧸ coinvariantKernel k G M)) :
    of k G M ⟶ Rep.trivial k G k where
  hom := ModuleCat.ofHom (f.comp ((coinvariantKernel k G M).mkQ.restrictScalars k))
  comm g := by
    ext v
    change f ((coinvariantKernel k G M).mkQ (MonoidAlgebra.of k G g • v)) =
      f ((coinvariantKernel k G M).mkQ v)
    rw [quotient_smul,AugmentationModule.augmentation_of,one_smul]

noncomputable def homCoinvariantDual :
    (of k G M ⟶ Rep.trivial k G k) ≃ₗ[k] Module.Dual k (M ⧸ coinvariantKernel k G M) where
  toFun := toCoinvariantDual k G M
  invFun := fromCoinvariantDual k G M
  left_inv f := by
    apply Action.Hom.ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    rfl
  right_inv f := by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := (coinvariantKernel k G M).mkQ_surjective v
    rfl
  map_add' f g := by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := (coinvariantKernel k G M).mkQ_surjective v
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro v
    obtain ⟨x,rfl⟩ := (coinvariantKernel k G M).mkQ_surjective v
    rfl

theorem hom_finrank_eq :
    Module.finrank k (of k G M ⟶ Rep.trivial k G k) =
      Module.finrank k (M ⧸ coinvariantKernel k G M) := by
  rw [(homCoinvariantDual k G M).finrank_eq,Subspace.dual_finrank_eq]

theorem free_coinvariant_finrank (d : ℕ) :
    Module.finrank k ((Fin d → MonoidAlgebra k G) ⧸ coinvariantKernel k G (Fin d → MonoidAlgebra k G)) = d := by
  classical
  let A := MonoidAlgebra k G
  let I := AugmentationModule.ideal k G
  let ε := (AugmentationModule.augmentation k G).toLinearMap
  have hsurj : Function.Surjective ε := by
    intro x
    exact ⟨MonoidAlgebra.single 1 x,AugmentationModule.augmentation_single k G 1 x⟩
  letI : FiniteDimensional k (A ⧸ I.restrictScalars k) :=
    (ε.quotKerEquivOfSurjective hsurj).symm.finiteDimensional
  have hq : Module.finrank k (A ⧸ I.restrictScalars k) = 1 := by
    change Module.finrank k (A ⧸ ε.ker) = 1
    rw [(ε.quotKerEquivOfSurjective hsurj).finrank_eq,Module.finrank_self]
  have he : coinvariantKernel k G (Fin d → A) = Submodule.pi Set.univ (fun _ : Fin d => I) := by
    apply le_antisymm
    · apply Submodule.smul_le.mpr
      intro r hr v _
      apply Submodule.mem_pi.mpr
      intro i _
      exact I.mul_mem_right (v i) hr
    · intro v hv
      rw [pi_eq_sum_univ v]
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem_smul ((Submodule.mem_pi.mp hv) i trivial) Submodule.mem_top
  rw [he]
  change Module.finrank k ((Fin d → A) ⧸ Submodule.pi Set.univ (fun _ : Fin d => I.restrictScalars k)) = d
  rw [(Submodule.quotientPi (fun _ : Fin d => I.restrictScalars k)).finrank_eq]
  simp only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change d*Module.finrank k (A ⧸ I.restrictScalars k) = d
  rw [hq,mul_one]

theorem free_hom_finrank (d : ℕ) :
    Module.finrank k (of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) = d := by
  rw [hom_finrank_eq,free_coinvariant_finrank]

end RepModule



/- Extending a prescribed length-two projective presentation to a resolution. -/

noncomputable section
namespace SelectedResolution
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
local infixr:80 " ≫ " => CategoryStruct.comp

variable {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {X₀ X₁ X₂ Z : C} (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (h : CategoryStruct.comp d₁ d₀ = 0)

def complex : ChainComplex C ℕ :=
  ChainComplex.mk X₀ X₁ X₂ d₀ d₁ h (fun S => ⟨_, Projective.d S.f, by simp⟩)

@[simp] theorem complex_d_1_0 : (complex d₀ d₁ h).d 1 0 = d₀ := by
  simp [complex]

@[simp] theorem complex_d_2_1 : (complex d₀ d₁ h).d 2 1 = d₁ := by
  simp [complex]

@[simp] theorem complex_d_3_2 : (complex d₀ d₁ h).d 3 2 = Projective.d d₁ := by
  change CategoryStruct.comp (𝟙 _) (Projective.d d₁) = _
  simp

theorem exactAt_succ (hex : (ShortComplex.mk d₁ d₀ h).Exact) (n : ℕ) :
    (complex d₀ d₁ h).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  dsimp [complex,HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',ChainComplex.mk]
  simp only [ChainComplex.of_d]
  match n with
  | 0 => exact hex
  | n+1 => apply CategoryTheory.exact_d_f

instance [Projective X₀] [Projective X₁] [Projective X₂] (n : ℕ) :
    Projective ((complex d₀ d₁ h).X n) := by
  obtain (_|_|_|n) := n
  · exact ‹Projective X₀›
  · exact ‹Projective X₁›
  · exact ‹Projective X₂›
  · apply Projective.projective_over

variable [Projective X₀] [Projective X₁] [Projective X₂]

def resolution (π : X₀ ⟶ Z) (hπ : CategoryStruct.comp d₀ π = 0) [Epi π]
    (hex₀ : (ShortComplex.mk d₀ π hπ).Exact)
    (hex₁ : (ShortComplex.mk d₁ d₀ h).Exact) : ProjectiveResolution Z where
  complex := complex d₀ d₁ h
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨π,by simpa using hπ⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨hex₀,inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [complex]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact exactAt_succ d₀ d₁ h hex₁ n
      · apply ChainComplex.exactAt_succ_single_obj⟩

end SelectedResolution



/- Homology when both adjacent differentials vanish. -/
noncomputable section
open CategoryTheory
namespace HomologyZeros
variable {C : Type*} [Category C] [Abelian C]

def iso (K : CochainComplex C ℕ) (n : ℕ)
    (hleft : K.d n (n+1) = 0) (hright : K.d (n+1) (n+2) = 0) :
    K.homology (n+1) ≅ K.X (n+1) :=
  K.homologyIsoSc' n (n+1) (n+2) (by simp) (by simp) ≪≫
    (ShortComplex.LeftHomologyData.ofZeros (K.sc' n (n+1) (n+2)) hleft hright).homologyIso

end HomologyZeros

namespace GSResolution
open CategoryTheory
local infixr:80 " ≫ₙ " => CategoryStruct.comp

variable (k G : Type) [Field k] [Group G]

noncomputable def augmentation : RepModule.of k G (MonoidAlgebra k G) ⟶ Rep.trivial k G k where
  hom := ModuleCat.ofHom (AugmentationModule.augmentation k G).toLinearMap
  comm g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change AugmentationModule.augmentation k G ((MonoidAlgebra.of k G g)*x) =
      AugmentationModule.augmentation k G x
    rw [map_mul,AugmentationModule.augmentation_of,one_mul]

instance : Epi (augmentation k G) := by
  rw [Rep.epi_iff_surjective]
  intro x
  exact ⟨MonoidAlgebra.single 1 x,AugmentationModule.augmentation_single k G 1 x⟩

variable {k G} {d r : ℕ}
variable (f : (Fin d → (MonoidAlgebra k G)) →ₗ[(MonoidAlgebra k G)] (AugmentationModule.ideal k G))
variable (g : (Fin r → (MonoidAlgebra k G)) →ₗ[(MonoidAlgebra k G)] f.ker)

noncomputable def d₀ : RepModule.of k G (Fin d → (MonoidAlgebra k G)) ⟶ RepModule.of k G (MonoidAlgebra k G) :=
  RepModule.map k G (((AugmentationModule.ideal k G)).subtype.comp f)

noncomputable def d₁ : RepModule.of k G (Fin r → (MonoidAlgebra k G)) ⟶ RepModule.of k G (Fin d → (MonoidAlgebra k G)) :=
  RepModule.map k G (f.ker.subtype.comp g)

theorem d₀_comp_augmentation : d₀ f ≫ₙ augmentation k G = 0 := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (AugmentationModule.mem_ideal k G _).mp (f x).property

theorem d₁_comp_d₀ : d₁ f g ≫ₙ d₀ f = 0 := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f (g x) : (MonoidAlgebra k G)) = 0
  rw [LinearMap.mem_ker.mp (g x).property]
  rfl

theorem exact₀ (hf : Function.Surjective f) :
    (ShortComplex.mk (d₀ f) (augmentation k G) (d₀_comp_augmentation f)).Exact := by
  apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  change AugmentationModule.augmentation k G x = 0 at hx
  obtain ⟨v,hv⟩ := hf ⟨x,(AugmentationModule.mem_ideal k G x).mpr hx⟩
  exact ⟨v,congrArg Subtype.val hv⟩

theorem exact₁ (hg : Function.Surjective g) :
    (ShortComplex.mk (d₁ f g) (d₀ f) (d₁_comp_d₀ f g)).Exact := by
  apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hfx : f x = 0 := Subtype.ext hx
  obtain ⟨v,hv⟩ := hg ⟨x,LinearMap.mem_ker.mpr hfx⟩
  exact ⟨v,congrArg Subtype.val hv⟩

noncomputable def resolution (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ProjectiveResolution (Rep.trivial k G k) :=
  SelectedResolution.resolution (d₀ f) (d₁ f g) (d₁_comp_d₀ f g)
    (augmentation k G) (d₀_comp_augmentation f) (exact₀ f hf) (exact₁ f g hg)

end GSResolution

namespace GSResolution
open CategoryTheory
local infixr:80 " ≫ₙ " => CategoryStruct.comp
variable {k G : Type} [Field k] [Group G] {d r : ℕ}
variable (f : (Fin d → MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] AugmentationModule.ideal k G)
variable (g : (Fin r → MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] f.ker)
variable (hf : Function.Surjective f) (hg : Function.Surjective g)
variable (hminf : f.ker ≤ RepModule.coinvariantKernel k G (Fin d → MonoidAlgebra k G))
variable (hming : g.ker ≤ RepModule.coinvariantKernel k G (Fin r → MonoidAlgebra k G))

theorem comp_d₀_zero (φ : RepModule.of k G (MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    d₀ f ≫ₙ φ = 0 := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change φ.hom (f x : MonoidAlgebra k G) = 0
  apply RepModule.hom_vanish
  have h : (f x : MonoidAlgebra k G) • (1 : MonoidAlgebra k G) ∈
      RepModule.coinvariantKernel k G (MonoidAlgebra k G) := Submodule.smul_mem_smul (f x).property
    (Submodule.mem_top : (1 : MonoidAlgebra k G) ∈ (⊤ : Submodule (MonoidAlgebra k G) (MonoidAlgebra k G)))
  simpa only [smul_eq_mul,mul_one] using h

include hminf in
theorem comp_d₁_zero (φ : RepModule.of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    d₁ f g ≫ₙ φ = 0 := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change φ.hom (g x : Fin d → MonoidAlgebra k G) = 0
  exact RepModule.hom_vanish k G _ φ (hminf (g x).property)

include hming in
theorem comp_d₂_zero (φ : RepModule.of k G (Fin r → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :
    Projective.d (d₁ f g) ≫ₙ φ = 0 := by
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change φ.hom ((Projective.d (d₁ f g)).hom x) = 0
  apply RepModule.hom_vanish k G _ φ
  apply hming
  apply LinearMap.mem_ker.mpr
  have he : (Projective.d (d₁ f g)) ≫ₙ d₁ f g = 0 := by simp
  have hx := congrArg (fun h => h.hom x) he
  apply Subtype.ext
  exact hx

theorem cochain_d₀_zero :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 0 1 = 0 := by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change d₀ f ≫ₙ φ = 0
  exact comp_d₀_zero f φ

include hminf in
theorem cochain_d₁_zero :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 1 2 = 0 := by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change d₁ f g ≫ₙ φ = 0
  exact comp_d₁_zero f g hminf φ

include hming in
theorem cochain_d₂_zero :
    ((resolution f g hf hg).complex.linearYonedaObj k (Rep.trivial k G k)).d 2 3 = 0 := by
  rw [ChainComplex.linearYonedaObj_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  change (SelectedResolution.complex (d₀ f) (d₁ f g) (d₁_comp_d₀ f g)).d 3 2 ≫ₙ φ = 0
  rw [SelectedResolution.complex_d_3_2]
  exact comp_d₂_zero f g hming φ

noncomputable def H1Iso :
    groupCohomology (Rep.trivial k G k) 1 ≅
      ModuleCat.of k (RepModule.of k G (Fin d → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :=
  groupCohomologyIso _ 1 (resolution f g hf hg) ≪≫
    HomologyZeros.iso _ 0 (cochain_d₀_zero f g hf hg) (cochain_d₁_zero f g hf hg hminf)

noncomputable def H2Iso :
    groupCohomology (Rep.trivial k G k) 2 ≅
      ModuleCat.of k (RepModule.of k G (Fin r → MonoidAlgebra k G) ⟶ Rep.trivial k G k) :=
  groupCohomologyIso _ 2 (resolution f g hf hg) ≪≫
    HomologyZeros.iso _ 1 (cochain_d₁_zero f g hf hg hminf) (cochain_d₂_zero f g hf hg hming)

include hf hg hminf in
theorem H1_finrank : Module.finrank k (groupCohomology (Rep.trivial k G k) 1) = d := by
  rw [(H1Iso f g hf hg hminf).toLinearEquiv.finrank_eq]
  exact RepModule.free_hom_finrank k G d

include hf hg hminf hming in
theorem H2_finrank : Module.finrank k (groupCohomology (Rep.trivial k G k) 2) = r := by
  rw [(H2Iso f g hf hg hminf hming).toLinearEquiv.finrank_eq]
  exact RepModule.free_hom_finrank k G r

end GSResolution

namespace GSCohomology
open CategoryTheory
open scoped Classical

variable (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- The cohomological Golod--Shafarevich inequality for finite p-groups. -/
theorem relation_bound (hG : IsPGroup p G)
    (hd : 3 ≤ Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1)) :
    (Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1))^2 <
      4*Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2) := by
  obtain ⟨f,hf,hminf⟩ := MinimalPGroupModule.exists_minimal_surjection G p
    (AugmentationModule.ideal (ZMod p) G) hG
  letI : FiniteDimensional (ZMod p) f.ker := inferInstanceAs
    (FiniteDimensional (ZMod p) (f.ker.restrictScalars (ZMod p)))
  obtain ⟨g,hg,hming⟩ := MinimalPGroupModule.exists_minimal_surjection G p f.ker hG
  have he₁ := GSResolution.H1_finrank f g hf hg hminf
  have he₂ := GSResolution.H2_finrank f g hf hg hminf hming
  rw [he₁,he₂]
  rw [he₁] at hd
  exact GSGroupAlgebra.relation_bound G p hG _ hd f hf hminf

/-- A finite p-group with large first cohomology cannot have too few relations. -/
theorem not_finite_of_rank_bound (hG : IsPGroup p G)
    (hd : 3 ≤ Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1))
    (hr : 4*Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2) ≤
      (Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1))^2) : False :=
  (relation_bound G p hG hd).not_ge hr

end GSCohomology

namespace LargeTowerCriterion
open NumberField
open scoped Classical

/-- A finite totally real, unramified Galois 2-extension whose first
cohomology has a prescribed lower rank bound. -/
structure Layer (B : Type) [Field B] [NumberField B] (d : ℕ) where
  carrier : Type
  field : Field carrier
  numberField : NumberField carrier
  real : IsTotallyReal carrier
  algebra : Algebra B carrier
  galois : IsGalois B carrier
  pGroup : IsPGroup 2 Gal(carrier/B)
  unramified : differentIdeal (𝓞 B) (𝓞 carrier) = ⊤
  generator_rank : d ≤ Module.finrank (ZMod 2)
    (groupCohomology (Rep.trivial (ZMod 2) Gal(carrier/B) (ZMod 2)) 1)

attribute [instance] Layer.field Layer.numberField Layer.real Layer.algebra Layer.galois

variable {B : Type} [Field B] [NumberField B] {d : ℕ}

/-- Degree-maximality among all eligible finite layers. This predicate only
arises under the temporary assumption that the degrees are bounded. -/
def IsDegreeMaximal (M : Layer B d) : Prop :=
  ∀ N : Layer B d, Module.finrank B N.carrier ≤ Module.finrank B M.carrier

/-- A uniform terminal relation bound incompatible with the initial rank. -/
def TerminalRelationBound (B : Type) [Field B] [NumberField B] (d R : ℕ) : Prop :=
  ∀ M : Layer B d, IsDegreeMaximal M →
    Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(M.carrier/B) (ZMod 2)) 2) ≤ R

/-- Golod--Shafarevich rules out terminality under the numerical inequality. -/
theorem not_degreeMaximal {R : ℕ} (hd : 3 ≤ d) (hnum : 4*R ≤ d^2)
    (hrel : TerminalRelationBound B d R) (M : Layer B d) : ¬ IsDegreeMaximal M := by
  intro hmax
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hgs := GSCohomology.relation_bound Gal(M.carrier/B) 2 M.pGroup
    (hd.trans M.generator_rank)
  have hr := hrel M hmax
  have hM := M.generator_rank
  nlinarith

/-- Bounded nonempty subsets of natural degrees attain their maximum. -/
theorem exists_degreeMaximal (h₀ : Nonempty (Layer B d))
    (hbound : ∃ n : ℕ, ∀ M : Layer B d, Module.finrank B M.carrier ≤ n) :
    ∃ M : Layer B d, IsDegreeMaximal M := by
  let s : Set ℕ := {n | ∃ M : Layer B d, Module.finrank B M.carrier = n}
  have hs : s.Nonempty := by
    obtain ⟨M⟩ := h₀
    exact ⟨_, M, rfl⟩
  have hb : BddAbove s := by
    obtain ⟨n,hn⟩ := hbound
    exact ⟨n, fun m ⟨M,hM⟩ => hM ▸ hn M⟩
  obtain ⟨M,hM⟩ := Nat.sSup_mem hs hb
  refine ⟨M, fun N => ?_⟩
  rw [hM]
  exact le_csSup hb (show Module.finrank B N.carrier ∈ s from ⟨N,rfl⟩)

/-- Once the missing arithmetic relation bound is supplied, no additional
infinite-extension or inverse-limit construction is necessary: finite layers
already have unbounded degree. -/
theorem exists_layer_degree_ge (h₀ : Nonempty (Layer B d))
    {R : ℕ} (hd : 3 ≤ d) (hnum : 4*R ≤ d^2) (hrel : TerminalRelationBound B d R) (n : ℕ) :
    ∃ M : Layer B d, n ≤ Module.finrank B M.carrier := by
  by_contra hn
  push_neg at hn
  obtain ⟨M,hM⟩ := exists_degreeMaximal h₀ ⟨n, fun N => (hn N).le⟩
  exact not_degreeMaximal hd hnum hrel M hM

/-- A selected family of finite layers with a prescribed power-of-two lower
bound on their degrees. All arithmetic hypotheses remain explicit. -/
theorem exists_family (h₀ : Nonempty (Layer B d)) {R : ℕ} (hd : 3 ≤ d) (hnum : 4*R ≤ d^2) (hrel : TerminalRelationBound B d R) :
    ∃ M : ℕ → Layer B d, ∀ n, 2^n ≤ Module.finrank B (M n).carrier := by
  exact Classical.skolem.mp (fun n => exists_layer_degree_ge h₀ hd hnum hrel (2^n))

end LargeTowerCriterion

namespace UnramifiedNormalClosure
open NumberField IntermediateField
open scoped Classical

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M] [Algebra K L] [Algebra K M]

/-- If a number field is generated by images of an unramified extension,
its inertia groups are trivial. -/
theorem inertia_eq_bot (hL : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hgen : normalClosure K L M = ⊤) (P : Ideal (𝓞 M)) (hP : P ≠ ⊤) :
    P.toAddSubgroup.inertia Gal(M/K) = ⊥ := by
  apply eq_bot_iff.mpr
  intro σ hσ
  change σ = 1
  let F : IntermediateField K M := {
    toSubalgebra := AlgHom.equalizer σ.toAlgHom (AlgHom.id K M)
    inv_mem' := fun x hx => by
      change σ x⁻¹ = x⁻¹
      change σ x = x at hx
      rw [map_inv₀,hx] }
  have hF : normalClosure K L M ≤ F := by
    apply normalClosure_le_iff.mpr
    intro f y hy
    obtain ⟨x,rfl⟩ := hy
    exact UnramifiedRigidity.inertia_fixes hL P hP σ hσ f x
  rw [hgen] at hF
  apply AlgEquiv.ext
  intro x
  exact hF (show x ∈ (⊤ : IntermediateField K M) from trivial)

/-- The normal closure of an everywhere-unramified number-field extension
is itself everywhere unramified. The ambient normal closure is arbitrary. -/
theorem different_eq_top [IsGalois K M]
    (hL : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (hgen : normalClosure K L M = ⊤) :
    differentIdeal (𝓞 K) (𝓞 M) = ⊤ := by
  by_contra hn
  obtain ⟨P,hP,hle⟩ := Ideal.exists_le_maximal (differentIdeal (𝓞 K) (𝓞 M)) hn
  letI : P.IsMaximal := hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField M)
  let p := P.under (𝓞 K)
  have hp0 : p ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal hp0
  letI : Field ((𝓞 K) ⧸ p) := Ideal.Quotient.field p
  letI : Field ((𝓞 M) ⧸ P) := Ideal.Quotient.field P
  letI : Finite ((𝓞 K) ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI : Finite ((𝓞 M) ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(M/K)) p hp0 P
  rw [inertia_eq_bot hL hgen P hP.ne_top] at hc
  have he : Ideal.ramificationIdx (algebraMap (𝓞 K) (𝓞 M)) p P = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(M/K),← hc]
    simp
  have hu : Algebra.IsUnramifiedAt (𝓞 K) P :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP0).mpr he
  exact (not_dvd_differentIdeal_iff.mpr hu) (Ideal.dvd_iff_le.mpr hle)

end UnramifiedNormalClosure



/- Normal closures of totally real number fields are totally real. -/
namespace RealNormalClosure
open NumberField IntermediateField

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M] [Algebra K L] [Algebra K M]

/-- Generation by images of a totally real field preserves total reality. -/
theorem totally_real [IsTotallyReal L] (hgen : normalClosure K L M = ⊤) : IsTotallyReal M := by
  letI : IsTotallyReal K := IsTotallyReal.of_algebra K L
  let F : IntermediateField K M := {
    carrier := {x | ∀ σ : M →+* ℂ, star (σ x) = σ x}
    add_mem' := fun hx hy σ => by rw [map_add,star_add,hx,hy]
    mul_mem' := fun hx hy σ => by rw [map_mul,star_mul,hx,hy,mul_comm]
    zero_mem' := fun σ => by simp
    one_mem' := fun σ => by simp
    algebraMap_mem' := fun x σ =>
      RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (σ.comp (algebraMap K M))) x
    inv_mem' := fun x hx σ => by rw [map_inv₀,star_inv₀,hx] }
  have hF : normalClosure K L M ≤ F := by
    apply normalClosure_le_iff.mpr
    intro f y hy
    obtain ⟨x,rfl⟩ := hy
    intro σ
    exact RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal (σ.comp f.toRingHom)) x
  rw [hgen] at hF
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hF (show x ∈ (⊤ : IntermediateField K M) from trivial) w.embedding

end RealNormalClosure



/- An extensionality principle for generators of a normal closure. -/
namespace NormalClosureExt
open IntermediateField
variable {K L M T : Type*} [Field K] [Field L] [Field M] [Field T]
  [Algebra K L] [Algebra K M] [Algebra K T]

theorem hom_ext (hgen : normalClosure K L M = ⊤) {f g : M →ₐ[K] T}
    (h : ∀ φ : L →ₐ[K] M, f.comp φ = g.comp φ) : f = g := by
  let F : IntermediateField K M := {
    toSubalgebra := AlgHom.equalizer f g
    inv_mem' := fun x hx => by
      change f x⁻¹ = g x⁻¹
      change f x = g x at hx
      rw [map_inv₀,map_inv₀,hx] }
  have hF : normalClosure K L M ≤ F := by
    apply normalClosure_le_iff.mpr
    intro φ y hy
    obtain ⟨x,rfl⟩ := hy
    exact AlgHom.congr_fun (h φ) x
  rw [hgen] at hF
  apply AlgHom.ext
  intro x
  exact hF (show x ∈ (⊤ : IntermediateField K M) from trivial)

end NormalClosureExt
namespace QuadraticNormalPGroup
open IntermediateField

variable {B K L M : Type*} [Field B] [Field K] [Field L] [Field M]
  [Algebra B K] [Algebra B L] [Algebra B M] [Algebra K L] [Algebra K M]
  [IsScalarTower B K L] [IsScalarTower B K M] [Normal B K]

/-- An automorphism in the kernel of restriction fixes the embedded base. -/
theorem fixes_base (σ : Gal(M/B)) (hσ : AlgEquiv.restrictNormalHom K σ = 1) (x : K) :
    σ (algebraMap K M x) = algebraMap K M x := by
  rw [← σ.restrictNormal_commutes K x]
  change algebraMap K M ((AlgEquiv.restrictNormalHom K σ) x) = _
  rw [hσ]
  rfl

/-- The kernel over K of the normal closure of a radical quadratic extension
has exponent two. -/
theorem kernel_sq (u : L) (a : K) (hu : u^2 = algebraMap K L a)
    (hgenL : Algebra.adjoin K {u} = ⊤) (hgenM : normalClosure B L M = ⊤)
    (σ : Gal(M/B)) (hσ : AlgEquiv.restrictNormalHom K σ = 1) : σ^2 = 1 := by
  have hfix (f : L →ₐ[B] M) (x : K) : σ (f (algebraMap K L x)) = f (algebraMap K L x) := by
    rw [← f.restrictNormal_commutes K x]
    exact fixes_base σ hσ _
  apply AlgEquiv.coe_algHom_injective
  apply NormalClosureExt.hom_ext hgenM
  intro f
  let F : Subalgebra K L := {
    carrier := {x | σ (σ (f x)) = f x}
    add_mem' := fun hx hy => by simpa only [Set.mem_setOf_eq,map_add] using congrArg₂ (· + ·) hx hy
    mul_mem' := fun hx hy => by simpa only [Set.mem_setOf_eq,map_mul] using congrArg₂ (· * ·) hx hy
    zero_mem' := by simp
    one_mem' := by simp
    algebraMap_mem' := fun x => by
      change σ (σ (f (algebraMap K L x))) = f (algebraMap K L x)
      rw [hfix,hfix] }
  have hF : Algebra.adjoin K {u} ≤ F := by
    apply Algebra.adjoin_le
    intro x hx
    have hx' := Set.mem_singleton_iff.mp hx
    subst x
    have hs : (σ (f u))^2 = (f u)^2 := by
      rw [← map_pow,← map_pow,hu,hfix]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · change σ (σ (f u)) = f u
      rw [h,h]
    · change σ (σ (f u)) = f u
      rw [h,map_neg,h,neg_neg]
  rw [hgenL] at hF
  apply AlgHom.ext
  intro x
  change σ (σ (f x)) = f x
  exact hF (show x ∈ (⊤ : Subalgebra K L) from trivial)

/-- Taking the normal closure of a quadratic step over a Galois 2-extension
still gives a Galois 2-extension of the original base. -/
theorem isPGroup (hK : IsPGroup 2 Gal(K/B))
    (u : L) (a : K) (hu : u^2 = algebraMap K L a)
    (hgenL : Algebra.adjoin K {u} = ⊤) (hgenM : normalClosure B L M = ⊤) :
    IsPGroup 2 Gal(M/B) := by
  intro σ
  obtain ⟨n,hn⟩ := hK (AlgEquiv.restrictNormalHom K σ)
  refine ⟨n+1,?_⟩
  rw [pow_succ,pow_mul]
  exact kernel_sq u a hu hgenL hgenM (σ^(2^n)) (by rw [map_pow,hn])

end QuadraticNormalPGroup



/- First-cohomology rank is monotone under finite group quotients. -/
namespace H1Quotient
open CategoryTheory

variable {G H : Type} [Group G] [Group H] [Finite G] (p : ℕ) [Fact p.Prime]

/-- Pullback of homomorphisms along a surjection is injective. -/
theorem finrank_le (f : G →* H) (hf : Function.Surjective f) :
    Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) H (ZMod p)) 1) ≤
      Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1) := by
  rw [(groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) H (ZMod p))).toLinearEquiv.finrank_eq,
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) G (ZMod p))).toLinearEquiv.finrank_eq]
  let φ : (Additive H →+ ZMod p) →ₗ[ZMod p] (Additive G →+ ZMod p) := {
    toFun := fun χ => χ.comp (MonoidHom.toAdditive f)
    map_add' := fun χ ψ => rfl
    map_smul' := fun r χ => rfl }
  have hφ : Function.Injective φ := by
    intro χ ψ h
    apply AddMonoidHom.ext
    intro x
    obtain ⟨y,hy⟩ := hf x.toMul
    have he := congrArg (fun χ : Additive G →+ ZMod p => χ (Additive.ofMul y)) h
    change χ (Additive.ofMul (f y)) = ψ (Additive.ofMul (f y)) at he
    simpa only [hy] using he
  letI : Finite (Additive G →+ ZMod p) := Finite.of_injective
    (fun χ : Additive G →+ ZMod p => (χ : Additive G → ZMod p)) DFunLike.coe_injective
  letI : Module.Finite (ZMod p) (Additive G →+ ZMod p) := Module.Finite.of_finite
  exact LinearMap.finrank_le_finrank_of_injective hφ

end H1Quotient

namespace LargeTowerCriterion
open NumberField IntermediateField
open scoped Classical

variable {B : Type} [Field B] [NumberField B] {d : ℕ} (M : Layer B d)
variable (L : Type) [Field L] [NumberField L] [IsTotallyReal L]
  [Algebra M.carrier L] [Algebra B L] [IsScalarTower B M.carrier L]

/-- A nontrivial totally real unramified radical quadratic step always lies
inside a larger eligible Galois layer. -/
theorem exists_larger_of_quadratic
    (hunram : differentIdeal (𝓞 M.carrier) (𝓞 L) = ⊤)
    (u : L) (a : M.carrier) (hu : u^2 = algebraMap M.carrier L a)
    (hgen : Algebra.adjoin M.carrier {u} = ⊤)
    (hdegree : 1 < Module.finrank M.carrier L) :
    ∃ N : Layer B d, Module.finrank B M.carrier < Module.finrank B N.carrier := by
  let Ω := AlgebraicClosure L
  let N := normalClosure B L Ω
  letI : NumberField N := NumberField.of_module_finite B N
  let f : M.carrier →ₐ[B] N := (IsScalarTower.toAlgHom B L N).comp
    (IsScalarTower.toAlgHom B M.carrier L)
  letI : Algebra M.carrier N := f.toRingHom.toAlgebra
  letI : IsScalarTower B M.carrier N := IsScalarTower.of_algHom f
  letI : IsScalarTower M.carrier L N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois B N := {}
  have hN : normalClosure B L N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp (inferInstance : IsNormalClosure B L N)).2
  letI : IsTotallyReal N := RealNormalClosure.totally_real hN
  have hBL : differentIdeal (𝓞 B) (𝓞 L) = ⊤ := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 B) (𝓞 M.carrier) (𝓞 L),
      M.unramified,hunram,Ideal.map_top,Ideal.top_mul]
  have hBN := UnramifiedNormalClosure.different_eq_top hBL hN
  have hpN : IsPGroup 2 Gal(N/B) := QuadraticNormalPGroup.isPGroup M.pGroup u a hu hgen hN
  have hdN : d ≤ Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(N/B) (ZMod 2)) 1) := by
    exact M.generator_rank.trans (H1Quotient.finrank_le 2
      (AlgEquiv.restrictNormalHom M.carrier) (AlgEquiv.restrictNormalHom_surjective N))
  let N₀ : Layer B d := {
    carrier := N
    field := inferInstance
    numberField := inferInstance
    real := inferInstance
    algebra := inferInstance
    galois := inferInstance
    pGroup := hpN
    unramified := hBN
    generator_rank := hdN }
  refine ⟨N₀,?_⟩
  change Module.finrank B M.carrier < Module.finrank B N
  have hLN : Module.finrank M.carrier L ≤ Module.finrank M.carrier N :=
    LinearMap.finrank_le_finrank_of_injective
      (f := (IsScalarTower.toAlgHom M.carrier L N).toLinearMap)
      (IsScalarTower.toAlgHom M.carrier L N).injective
  have hd := Module.finrank_mul_finrank B M.carrier N
  have hp : 0 < Module.finrank B M.carrier := Module.finrank_pos
  nlinarith

/-- A degree-maximal layer has no nontrivial totally real unramified
radical quadratic extension. -/
theorem no_quadratic_of_degreeMaximal (hM : IsDegreeMaximal M)
    (hunram : differentIdeal (𝓞 M.carrier) (𝓞 L) = ⊤)
    (u : L) (a : M.carrier) (hu : u^2 = algebraMap M.carrier L a)
    (hgen : Algebra.adjoin M.carrier {u} = ⊤) :
    Module.finrank M.carrier L = 1 := by
  by_contra hn
  have hp : 0 < Module.finrank M.carrier L := Module.finrank_pos
  have hd : 1 < Module.finrank M.carrier L := by omega
  obtain ⟨N,hN⟩ := exists_larger_of_quadratic M L hunram u a hu hgen hd
  exact hN.not_ge (hM N)

end LargeTowerCriterion



/- Squareclasses under one quadratic radical adjunction. -/
namespace QuadraticSquareclass
open scoped Classical

variable (K : Type*) [Field K] [CharZero K] (a b : K)

/-- A base-field element which becomes a square after adjoining sqrt(a) is
either already a square, or a times a square. -/
theorem square_cases
    (h : IsSquare (algebraMap K (QuadraticAlgebra K a 0) b)) :
    IsSquare b ∨ ∃ y : K, b = a*y^2 := by
  obtain ⟨z,hz⟩ := h
  have hr := congrArg QuadraticAlgebra.re hz
  have hi := congrArg QuadraticAlgebra.im hz
  change b = z.re*z.re+a*z.im*z.im at hr
  change (0 : K) = z.re*z.im+z.im*z.re+0*z.im*z.im at hi
  have hh : 2*z.re*z.im = 0 := by linear_combination -hi
  have hz' : z.re = 0 ∨ z.im = 0 := by
    simpa only [mul_eq_zero,show (2 : K) ≠ 0 from by norm_num,false_or] using hh
  rcases hz' with hz' | hz'
  · right
    exact ⟨z.im,by simpa [hz',pow_two,mul_assoc] using hr⟩
  · left
    exact ⟨z.re,by simpa [hz'] using hr⟩

end QuadraticSquareclass
namespace QuadraticSquareclass
open scoped Classical
variable (K : Type*) [Field K] [CharZero K] (a b : K)

/-- Multiplicative squareclass form, convenient for induction over radicals. -/
theorem squareclass_cases
    (h : IsSquare (algebraMap K (QuadraticAlgebra K a 0) b)) :
    IsSquare b ∨ IsSquare (b*a) := by
  rcases square_cases K a b h with hb | ⟨y,hy⟩
  · exact Or.inl hb
  · right
    refine ⟨a*y,?_⟩
    rw [hy]
    ring

/-- The distinguished quadratic generator. -/
def root : QuadraticAlgebra K a 0 := ⟨0,1⟩

omit [CharZero K] in
theorem root_sq : (root K a)^2 = algebraMap K (QuadraticAlgebra K a 0) a := by
  ext <;> simp [root,pow_two,← QuadraticAlgebra.C_eq_algebraMap]

omit [CharZero K] in
theorem adjoin_root : Algebra.adjoin K {root K a} = ⊤ := by
  apply top_unique
  intro z _
  have hr : root K a ∈ Algebra.adjoin K {root K a} := Algebra.subset_adjoin (Set.mem_singleton _)
  have hmem := Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ z.re)
    (Subalgebra.smul_mem _ hr z.im)
  have he : algebraMap K (QuadraticAlgebra K a 0) z.re+z.im • root K a = z := by
    ext <;> simp [root,← QuadraticAlgebra.C_eq_algebraMap]
  simpa only [he] using hmem

end QuadraticSquareclass



/- Adjoining square roots of nonnegative rationals preserves total reality. -/
namespace TotallyRealRadicals
open NumberField
open scoped Classical

/-- Every complex square root of a nonnegative real is fixed by conjugation. -/
theorem star_eq_of_sq (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : z^2 = r) : star z = z := by
  have hs : ((Real.sqrt r : ℂ))^2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hz.trans hs.symm) with h | h
  · simp [h]
  · simp [h]

variable (K L : Type*) [Field K] [Field L] [NumberField L]
  [Algebra K L] [IsTotallyReal K]

private def realSubalgebra : Subalgebra K L where
  carrier := {x | ∀ σ : L →+* ℂ, star (σ x) = σ x}
  add_mem' hx hy σ := by rw [map_add,star_add,hx,hy]
  mul_mem' hx hy σ := by rw [map_mul,star_mul,hx,hy,mul_comm]
  zero_mem' σ := by simp
  one_mem' σ := by simp
  algebraMap_mem' x σ := by
    have h := IsTotallyReal.complexEmbedding_isReal (σ.comp (algebraMap K L))
    exact RingHom.congr_fun h x

/-- Total reality for a field generated by square roots of nonnegative rationals. -/
theorem of_adjoin (S : Set L) (hgen : Algebra.adjoin K S = ⊤)
    (hS : ∀ u ∈ S, ∃ r : ℚ, 0 ≤ r ∧ u^2 = algebraMap ℚ L r) : IsTotallyReal L := by
  have hs : Algebra.adjoin K S ≤ realSubalgebra K L := by
    apply Algebra.adjoin_le
    intro u hu σ
    obtain ⟨r,hr,he⟩ := hS u hu
    apply star_eq_of_sq (σ u) (r : ℝ) (by exact_mod_cast hr)
    have hm := congrArg σ he
    simpa using hm
  have hall : ∀ x : L, ∀ σ : L →+* ℂ, star (σ x) = σ x := by
    intro x
    apply hs
    rw [hgen]
    trivial
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hall x w.embedding

theorem of_adjoin_singleton (u : L) (r : ℚ) (hr : 0 ≤ r)
    (hu : u^2 = algebraMap ℚ L r) (hgen : Algebra.adjoin K {u} = ⊤) : IsTotallyReal L := by
  apply of_adjoin K L {u} hgen
  intro v hv
  exact Set.mem_singleton_iff.mp hv ▸ ⟨r,hr,hu⟩

end TotallyRealRadicals
namespace TotallyRealRadicals
open NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L] [IsTotallyReal K]

/-- Square roots of elements nonnegative at every real embedding preserve
total reality, when they generate the extension. -/
theorem of_adjoin_positive (S : Set L) (hgen : Algebra.adjoin K S = ⊤)
    (hS : ∀ u ∈ S, ∃ a : K, u^2 = algebraMap K L a ∧
      ∀ σ : K →+* ℂ, 0 ≤ (σ a).re) : IsTotallyReal L := by
  have hs : Algebra.adjoin K S ≤ realSubalgebra K L := by
    apply Algebra.adjoin_le
    intro u hu σ
    obtain ⟨a,ha,hpos⟩ := hS u hu
    let τ := σ.comp (algebraMap K L)
    have hr : ((τ a).re : ℂ) = τ a :=
      Complex.conj_eq_iff_re.mp (RingHom.congr_fun (IsTotallyReal.complexEmbedding_isReal τ) a)
    apply star_eq_of_sq (σ u) (τ a).re (hpos τ)
    rw [← map_pow,ha,hr]
    rfl
  rw [hgen] at hs
  constructor
  intro w
  rw [← InfinitePlace.mk_embedding w,InfinitePlace.isReal_mk_iff]
  apply ComplexEmbedding.isReal_iff.mpr
  ext x
  exact hs (show x ∈ (⊤ : Subalgebra K L) from trivial) w.embedding

end TotallyRealRadicals



/- Elementary different-ideal bounds for a quadratic generator. -/

namespace UnitQuadraticUnramified
open NumberField Polynomial

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- An integral half-generator for a radicand congruent to a square modulo four. -/
theorem half_integral (a b c : 𝓞 K) (hab : a = b^2+4*c)
    (u : L) (hu : u^2 = algebraMap K L (a : K)) :
    IsIntegral ℤ ((u+algebraMap K L (b : K))/2) := by
  apply isIntegral_trans (A := 𝓞 K)
  refine ⟨X^2-C b*X-C c,?_,?_⟩
  · apply Monic.sub_of_left (Monic.sub_of_left (monic_X.pow 2) (by compute_degree!))
    rw [degree_sub_eq_left_of_degree_lt (by compute_degree!)]
    compute_degree!
  · simp only [eval₂_sub,eval₂_pow,eval₂_mul,eval₂_X,eval₂_C]
    have hab' : algebraMap K L (a : K) =
        (algebraMap K L (b : K))^2+4*algebraMap K L (c : K) := by
      exact congrArg (algebraMap (𝓞 K) L) hab |>.trans (by
        simp only [map_add,map_pow,map_mul,map_ofNat]
        rfl)
    change ((u+algebraMap K L (b : K))/2)^2 -
      algebraMap K L (b : K)*((u+algebraMap K L (b : K))/2)-algebraMap K L (c : K) = 0
    field_simp
    linear_combination hu.trans hab'

/-- An integral unit radicand congruent to a square modulo four gives an
extension unramified at every finite prime. -/
theorem different_eq_top (a : (𝓞 K)ˣ) (b c : 𝓞 K) (hab : (a : 𝓞 K) = b^2+4*c)
    (u : L) (hu : u^2 = algebraMap K L ((a : 𝓞 K) : K))
    (hgen : Algebra.adjoin K {u} = ⊤) : differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let v : 𝓞 L := ⟨(u+algebraMap K L (b : K))/2,half_integral K L a b c hab u hu⟩
  have hvgen : Algebra.adjoin K {(v : L)} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro x hx
    have hx' : x = u := Set.mem_singleton_iff.mp hx
    subst x
    have hv : (v : L) ∈ Algebra.adjoin K {(v : L)} := Algebra.subset_adjoin (Set.mem_singleton _)
    have he : u = 2*(v : L)-algebraMap K L (b : K) := by dsimp [v]; field_simp; ring
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2) hv)
      (Subalgebra.algebraMap_mem _ _)
  have hvrel : v^2-algebraMap (𝓞 K) (𝓞 L) b*v-algebraMap (𝓞 K) (𝓞 L) c = 0 := by
    apply RingOfIntegers.coe_injective
    change ((u+algebraMap K L (b : K))/2)^2 -
      algebraMap K L (b : K)*((u+algebraMap K L (b : K))/2)-algebraMap K L (c : K) = 0
    have hab' : algebraMap K L ((a : 𝓞 K) : K) =
        (algebraMap K L (b : K))^2+4*algebraMap K L (c : K) := by
      exact congrArg (algebraMap (𝓞 K) L) hab |>.trans (by
        simp only [map_add,map_pow,map_mul,map_ofNat]
        rfl)
    field_simp
    linear_combination hu.trans hab'
  have hd := QuadraticDifferent.derivative_mem K L v hvgen (X^2-C b*X-C c)
    (by simpa using hvrel)
  let z : 𝓞 L := 2*v-algebraMap (𝓞 K) (𝓞 L) b
  have hz : z ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    simpa [z,derivative_sub,derivative_pow,derivative_mul,derivative_X,derivative_C,map_ofNat] using hd
  have hzu : (z : L) = u := by dsimp [z,v]; change 2*((u+algebraMap K L (b : K))/2)-algebraMap K L (b : K) = u; field_simp; ring
  have hzsq : z^2 = algebraMap (𝓞 K) (𝓞 L) a := by
    apply RingOfIntegers.coe_injective
    change (z : L)^2 = algebraMap K L ((a : 𝓞 K) : K)
    rw [hzu,hu]
  apply Ideal.eq_top_of_isUnit_mem _ (x := algebraMap (𝓞 K) (𝓞 L) (a : 𝓞 K))
  · rw [← hzsq,pow_two]
    exact Ideal.mul_mem_left _ _ hz
  · exact a.isUnit.map (algebraMap (𝓞 K) (𝓞 L))

end UnitQuadraticUnramified


namespace VirtualQuadraticUnramified
open NumberField Polynomial
open scoped Classical nonZeroDivisors
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

theorem radicand_mem (a : 𝓞 K) (b c : 𝓞 K) (hab : a = b^2+4*c)
    (u : L) (hu : u^2 = algebraMap K L ((a : 𝓞 K) : K))
    (hgen : Algebra.adjoin K {u} = ⊤) : algebraMap (𝓞 K) (𝓞 L) a ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  let v : 𝓞 L := ⟨(u+algebraMap K L (b : K))/2,UnitQuadraticUnramified.half_integral K L a b c hab u hu⟩
  have hvgen : Algebra.adjoin K {(v : L)} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    intro x hx
    have hx' : x = u := Set.mem_singleton_iff.mp hx
    subst x
    have hv : (v : L) ∈ Algebra.adjoin K {(v : L)} := Algebra.subset_adjoin (Set.mem_singleton _)
    have he : u = 2*(v : L)-algebraMap K L (b : K) := by dsimp [v]; field_simp; ring
    rw [he]
    exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2) hv)
      (Subalgebra.algebraMap_mem _ _)
  have hvrel : v^2-algebraMap (𝓞 K) (𝓞 L) b*v-algebraMap (𝓞 K) (𝓞 L) c = 0 := by
    apply RingOfIntegers.coe_injective
    change ((u+algebraMap K L (b : K))/2)^2 -
      algebraMap K L (b : K)*((u+algebraMap K L (b : K))/2)-algebraMap K L (c : K) = 0
    have hab' : algebraMap K L ((a : 𝓞 K) : K) =
        (algebraMap K L (b : K))^2+4*algebraMap K L (c : K) := by
      exact congrArg (algebraMap (𝓞 K) L) hab |>.trans (by
        simp only [map_add,map_pow,map_mul,map_ofNat]
        rfl)
    field_simp
    linear_combination hu.trans hab'
  have hd := QuadraticDifferent.derivative_mem K L v hvgen (X^2-C b*X-C c)
    (by simpa using hvrel)
  let z : 𝓞 L := 2*v-algebraMap (𝓞 K) (𝓞 L) b
  have hz : z ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    simpa [z,derivative_sub,derivative_pow,derivative_mul,derivative_X,derivative_C,map_ofNat] using hd
  have hzu : (z : L) = u := by dsimp [z,v]; change 2*((u+algebraMap K L (b : K))/2)-algebraMap K L (b : K) = u; field_simp; ring
  have hzsq : z^2 = algebraMap (𝓞 K) (𝓞 L) a := by
    apply RingOfIntegers.coe_injective
    change (z : L)^2 = algebraMap K L ((a : 𝓞 K) : K)
    rw [hzu,hu]
  rw [← hzsq,pow_two]
  exact Ideal.mul_mem_left _ _ hz

/-- A virtual-unit radicand, prime to two and a square modulo four, gives
an everywhere-unramified quadratic extension. -/
theorem different_eq_top (a b c : 𝓞 K) (ha0 : a ≠ 0) (ha2 : IsCoprime a 2)
    (hab : a = b^2+4*c) (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (hvirtual : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) = I*I)
    (u : L) (hu : u^2 = algebraMap K L (a : K))
    (hgen : Algebra.adjoin K {u} = ⊤) : differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  have haD := radicand_mem K L a b c hab u hu hgen
  by_cases hau : IsUnit a
  · exact Ideal.eq_top_of_isUnit_mem _ haD (hau.map (algebraMap (𝓞 K) (𝓞 L)))
  have hp0 : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by simpa using ha0
  have hp1 : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊤ := by
    intro he
    exact hau (Ideal.span_singleton_eq_top.mp he)
  obtain ⟨x,hx,r,hr,hcop⟩ := VirtualLocalNormalization.exists_coprime_representative K
    (Ideal.span {a}) hp0 hp1 (a : K) I hI hvirtual
  have hvsq : (algebraMap K L x*u)^2 = algebraMap K L (r : K) := by
    rw [mul_pow,hu,hr,map_mul,map_pow]
    ring
  have hvi : IsIntegral ℤ (algebraMap K L x*u) :=
    IsIntegral.of_pow (by norm_num : 0 < 2)
      (hvsq ▸ (algebraMap (𝓞 K) (𝓞 L) r).property)
  let v : 𝓞 L := ⟨algebraMap K L x*u,hvi⟩
  have hvgen : Algebra.adjoin K {(v : L)} = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro y ⟨rfl⟩
    have hv : (v : L) ∈ Algebra.adjoin K {(v : L)} := Algebra.subset_adjoin (Set.mem_singleton _)
    have he : u = algebraMap K L x⁻¹*(v : L) := by
      change u = algebraMap K L x⁻¹*(algebraMap K L x*u)
      rw [map_inv₀,← mul_assoc,inv_mul_cancel₀ (by simpa only [map_zero] using (algebraMap K L).injective.ne hx),one_mul]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hv
  have hvrel : v^2 = algebraMap (𝓞 K) (𝓞 L) r := RingOfIntegers.coe_injective hvsq
  have hvD := QuadraticDifferent.two_mul_mem K L r v hvgen hvrel
  have h4r : algebraMap (𝓞 K) (𝓞 L) (4*r) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
    have he : (2*v)^2 = algebraMap (𝓞 K) (𝓞 L) (4*r) := by
      rw [mul_pow,hvrel,map_mul,map_ofNat]
      norm_num
    rw [← he,pow_two]
    exact Ideal.mul_mem_left _ _ hvD
  have har : IsCoprime a r := (Ideal.isCoprime_span_singleton_iff a r).mp hcop
  have ha4 : IsCoprime a 4 := by
    have he := ha2.pow_right (n := 2)
    norm_num at he ⊢
    exact he
  obtain ⟨s,t,hst⟩ := ha4.mul_right har
  have hh := Ideal.add_mem (differentIdeal (𝓞 K) (𝓞 L))
    (Ideal.mul_mem_left _ (algebraMap (𝓞 K) (𝓞 L) s) haD)
    (Ideal.mul_mem_left _ (algebraMap (𝓞 K) (𝓞 L) t) h4r)
  have he := congrArg (algebraMap (𝓞 K) (𝓞 L)) hst
  simp only [map_add,map_mul,map_one] at he
  apply (Ideal.eq_top_iff_one _).mpr
  rw [map_mul,he] at hh
  exact hh

end VirtualQuadraticUnramified


namespace LargeTowerCriterion
open NumberField
open scoped Classical
variable {B : Type} [Field B] [NumberField B] {d : ℕ} (M : Layer B d)

/-- The virtual-unit square criterion follows from degree-maximality. -/
theorem squareCriterion_of_degreeMaximal (hM : IsDegreeMaximal M) :
    VirtualUnitResidues.SquareCriterion M.carrier := by
  intro a b c ha0 hcop hbc I hI hvirt hpos
  by_contra hn
  let aK : M.carrier := (a : M.carrier)
  letI : Fact (∀ x : M.carrier, x^2 ≠ aK+0*x) :=
    ⟨fun x hx => hn ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let L := QuadraticAlgebra M.carrier aK 0
  letI : NumberField L := NumberField.of_module_finite M.carrier L
  letI : Algebra B L := inferInstance
  letI : IsScalarTower B M.carrier L := inferInstance
  let u : L := QuadraticSquareclass.root M.carrier aK
  have hu : u^2 = algebraMap M.carrier L aK := QuadraticSquareclass.root_sq M.carrier aK
  have hgen : Algebra.adjoin M.carrier {u} = ⊤ := QuadraticSquareclass.adjoin_root M.carrier aK
  letI : IsTotallyReal L := TotallyRealRadicals.of_adjoin_positive M.carrier L {u} hgen (by
    intro x hx
    have hx' : x = u := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨aK,hu,hpos⟩)
  have hunram := VirtualQuadraticUnramified.different_eq_top M.carrier L a b c ha0 hcop hbc I hI hvirt u hu hgen
  have hd := no_quadratic_of_degreeMaximal M L hM hunram u aK hu hgen
  have he : Module.finrank M.carrier L = 2 := QuadraticAlgebra.finrank_eq_two aK 0
  omega

end LargeTowerCriterion


namespace ModTwoResidues
open NumberField
open scoped Classical
variable (E : Type*) [Field E] [NumberField E]

/-- Absence of ramification over two makes the residue ring reduced. -/
theorem reduced_of_coprime_different (hcop : IsCoprime (differentIdeal ℤ (𝓞 E)) (modulus E)) :
    IsReduced (R E) := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hp0 : p ≠ ⊥ := by simp [p]
  letI : p.IsPrime := (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
    (by norm_num [Int.prime_iff_natAbs_prime])
  letI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
  have hs : Squarefree (modulus E) := by
    apply (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero (by simp [modulus])).mpr
    intro P hP hsq
    have hd := pow_sub_one_dvd_differentIdeal ℤ P 2 hp0 (by
      simpa only [p,Ideal.map_span,Set.image_singleton,map_ofNat,pow_two,modulus] using hsq)
    simp only [Nat.reduceSub,pow_one] at hd
    exact hP.not_isUnit (hcop.isUnit_of_dvd' hd (dvd_trans (dvd_mul_right P P) hsq))
  apply (Ideal.isRadical_iff_quotient_reduced (modulus E)).mp
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by norm_num)).mpr
  intro x hx
  apply Ideal.dvd_span_singleton.mp
  apply (hs.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [Ideal.span_singleton_pow]
  exact Ideal.dvd_span_singleton.mpr hx

/-- Coprimality of the absolute discriminant with two is sufficient. -/
theorem reduced_of_odd_discr (hcop : IsCoprime (NumberField.discr E) (2 : ℤ)) :
    IsReduced (R E) := by
  apply reduced_of_coprime_different E
  obtain ⟨a,b,hab⟩ := hcop
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a*NumberField.discr E,Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)),
    b*2,Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),?_⟩
  exact_mod_cast hab

end ModTwoResidues


namespace ModTwoResidues
open NumberField
variable (K E : Type*) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]

theorem coprime_different_two (hcop : IsCoprime (NumberField.discr E) (2 : ℤ)) :
    IsCoprime (differentIdeal ℤ (𝓞 E)) (modulus E) := by
  obtain ⟨a,b,hab⟩ := hcop
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a*NumberField.discr E,Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)),
    b*2,Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),?_⟩
  exact_mod_cast hab

/-- Oddness at the base suffices throughout an unramified tower. -/
theorem reduced_of_unramified_base_odd
    (hcop : IsCoprime (NumberField.discr K) (2 : ℤ))
    (hunram : differentIdeal (𝓞 K) (𝓞 E) = ⊤) : IsReduced (R E) := by
  apply reduced_of_coprime_different E
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E),hunram,Ideal.top_mul]
  have h := (coprime_different_two K hcop).map (Ideal.mapHom (algebraMap (𝓞 K) (𝓞 E)))
  simpa only [Ideal.mapHom_apply,modulus,Ideal.map_span,Set.image_singleton,map_ofNat] using h

end ModTwoResidues


namespace LargeTowerCriterion
open NumberField PrincipalInvolutionSequences
open scoped Classical
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable (B : Type) [Field B] [NumberField B] [IsTotallyReal B] (d : ℕ)

/-- The terminal relation estimate is a theorem, with no remaining arithmetic
hypothesis beyond odd absolute discriminant. -/
theorem terminalRelationBound (hodd : IsCoprime (NumberField.discr B) (2 : ℤ)) :
    TerminalRelationBound B d
      (Module.finrank (ZMod 2) (ModTwo.V (C B))+2*Module.finrank ℚ B) := by
  intro M hM
  letI : IsReduced (ModTwoResidues.R M.carrier) :=
    ModTwoResidues.reduced_of_unramified_base_odd B M.carrier hodd M.unramified
  exact VirtualClassObstruction.terminal_relation_bound B M.carrier M.pGroup M.unramified
    (squareCriterion_of_degreeMaximal M hM)

/-- A sufficiently high-rank finite genus extension forces unbounded degrees
in the totally real everywhere-unramified 2-tower. -/
theorem arithmetic_family (hodd : IsCoprime (NumberField.discr B) (2 : ℤ))
    (h₀ : Nonempty (Layer B d)) (hd : 3 ≤ d)
    (hnum : 4*(Module.finrank (ZMod 2) (ModTwo.V (C B))+2*Module.finrank ℚ B) ≤ d^2) :
    ∃ M : ℕ → Layer B d, ∀ n, 2^n ≤ Module.finrank B (M n).carrier :=
  exists_family h₀ hd hnum (terminalRelationBound B d hodd)

end LargeTowerCriterion

namespace QuarticClassNumber
open NumberField
open scoped Classical nonZeroDivisors
variable (K : Type*) [Field K] [NumberField K] [IsTotallyReal K]

/-- A deliberately coarse but uniform class-number bound in real degree four. -/
theorem card_le (hdeg : Module.finrank ℚ K = 4) :
    Nat.card (ClassGroup (𝓞 K)) ≤ 16*(NumberField.discr K).natAbs := by
  have hex (C : ClassGroup (𝓞 K)) : ∃ I : (Ideal (𝓞 K))⁰,
      ClassGroup.mk0 I = C ∧ (Ideal.absNorm I.1 : ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := by
    obtain ⟨I,hI,hbound⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    refine ⟨I,hI,hbound.trans ?_⟩
    rw [IsTotallyReal.nrComplexPlaces_eq_zero,hdeg]
    norm_num
    nlinarith [Real.sqrt_nonneg |(NumberField.discr K : ℝ)|]
  choose f hf hb using hex
  let S : Finset (Ideal (𝓞 K)) := Finset.univ.image (fun C => (f C).1)
  let N : ℕ := ⌊Real.sqrt |(NumberField.discr K : ℝ)|⌋₊
  have hinj : Function.Injective (fun C => (f C).1) := by
    intro C D h
    have he : f C = f D := Subtype.ext h
    rw [← hf C,← hf D,he]
  have hcard : S.card = Nat.card (ClassGroup (𝓞 K)) := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Nat.card_eq_fintype_card]
  have hcount : S.card ≤ 2^(Module.finrank ℚ K)*N^2 := by
    apply IdealCounting.card_le K S N
    · intro I hI
      obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp hI
      exact mem_nonZeroDivisors_iff_ne_zero.mp (f C).2
    · intro I hI
      obtain ⟨C,_,rfl⟩ := Finset.mem_image.mp hI
      exact (Nat.le_floor_iff (Real.sqrt_nonneg _)).mpr (hb C)
  rw [hcard,hdeg] at hcount
  have hN : (N : ℝ)^2 ≤ (NumberField.discr K).natAbs := by
    have hle : (N : ℝ) ≤ Real.sqrt |(NumberField.discr K : ℝ)| := Nat.floor_le (Real.sqrt_nonneg _)
    have hsq := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ N) (Real.sqrt_nonneg |(NumberField.discr K : ℝ)|) |>.mpr hle
    rw [Real.sq_sqrt (abs_nonneg _)] at hsq
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hsq
  have hN' : N^2 ≤ (NumberField.discr K).natAbs := by exact_mod_cast hN
  exact hcount.trans (by norm_num; omega)

end QuarticClassNumber

namespace QuarticClassNumber
open NumberField PrincipalInvolutionSequences
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [IsTotallyReal K]

theorem pow_classRank_le (hdeg : Module.finrank ℚ K = 4) :
    2^Module.finrank (ZMod 2) (ModTwo.V (C K)) ≤ 16*(NumberField.discr K).natAbs := by
  letI : Finite (C K) := Finite.of_equiv (FractionalClasses.Classes K) Additive.ofMul
  letI : Finite (ModTwo.V (C K)) := Finite.of_surjective ModTwo.mk ModTwo.mk_surjective
  letI : FiniteDimensional (ZMod 2) (ModTwo.V (C K)) := Module.Finite.of_finite
  have h := Nat.card_le_card_of_surjective (ModTwo.mk (A := C K)) ModTwo.mk_surjective
  have hc : Nat.card (C K) = Nat.card (ClassGroup (𝓞 K)) :=
    (Nat.card_congr (Additive.ofMul : FractionalClasses.Classes K ≃ C K)).symm.trans
      (Nat.card_congr (FractionalClasses.equiv K).toEquiv)
  rw [hc,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_eq_fintype_card,ZMod.card] at h
  exact h.trans (card_le K hdeg)

/-- An exponential discriminant estimate gives a linear bound on the2-class rank. -/
theorem classRank_le (hdeg : Module.finrank ℚ K = 4) (N : ℕ)
    (hdisc : 16*(NumberField.discr K).natAbs ≤ 2^N) :
    Module.finrank (ZMod 2) (ModTwo.V (C K)) ≤ N := by
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
  exact (pow_classRank_le K hdeg).trans hdisc

end QuarticClassNumber

/-! Finite arithmetic certificate for the real unramified tower. -/



/- Elementary different-ideal bounds for a quadratic generator. -/

namespace GenusUnramified
open NumberField Polynomial
open scoped Classical

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- The integral half-generator attached to a square root of 4*a+1. -/
theorem half_integral (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) :
    IsIntegral ℤ ((u+1)/2) := by
  refine ⟨X^2-X-C a,?_,?_⟩
  · apply Monic.sub_of_left (Monic.sub_of_left (monic_X.pow 2) (by simp))
    rw [degree_sub_eq_left_of_degree_lt (by simp)]
    exact lt_of_le_of_lt degree_C_le (by simp)
  · simp only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C]
    change ((u+1)/2)^2-(u+1)/2-(a : L) = 0
    have htwo : (2 : L) ≠ 0 := by norm_num
    field_simp
    linear_combination hu

noncomputable def half (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) : 𝓞 L :=
  ⟨(u+1)/2,half_integral L a u hu⟩

theorem half_relation (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) :
    (half L a u hu)^2-half L a u hu-a = 0 := by
  apply RingOfIntegers.coe_injective
  change ((u+1)/2)^2-(u+1)/2-(a : L) = 0
  field_simp
  linear_combination hu

omit [NumberField K] in
theorem half_adjoin (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1)
    (hgen : Algebra.adjoin K {u} = ⊤) :
    Algebra.adjoin K {((half L a u hu : 𝓞 L) : L)} = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Algebra.adjoin_le
  intro x hx
  have hx' : x = u := Set.mem_singleton_iff.mp hx
  subst x
  have ht : ((u+1)/2 : L) ∈ Algebra.adjoin K {((half L a u hu : 𝓞 L) : L)} :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have he : u = 2*((u+1)/2)-1 := by field_simp; ring
  have hmem := Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ 2) ht) (Subalgebra.one_mem _)
  simpa only [Nat.cast_ofNat,← he] using hmem

noncomputable def rootInteger (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) : 𝓞 L :=
  2*half L a u hu-1

@[simp] theorem coe_rootInteger (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) :
    (rootInteger L a u hu : L) = u := by
  change 2*((u+1)/2)-1 = u
  field_simp
  ring

theorem root_mem_different (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1)
    (hgen : Algebra.adjoin K {u} = ⊤) :
    rootInteger L a u hu ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hd := QuadraticDifferent.derivative_mem K L (half L a u hu) (half_adjoin K L a u hu hgen)
    (X^2-X-C (a : 𝓞 K)) (by simpa using half_relation L a u hu)
  simpa [rootInteger,derivative_sub,derivative_pow,derivative_X,derivative_C,map_ofNat] using hd

/-- The standard biquadratic genus extension is unramified whenever either
square root generates the relative extension and the two odd radicands are coprime. -/
theorem different_eq_top (a b : ℤ) (hcop : IsCoprime (4*a+1) (4*b+1))
    (u v : L) (hu : u^2 = 4*(a : L)+1) (hv : v^2 = 4*(b : L)+1)
    (hgenU : Algebra.adjoin K {u} = ⊤) (hgenV : Algebra.adjoin K {v} = ⊤) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  let D := differentIdeal (𝓞 K) (𝓞 L)
  have hU : rootInteger L a u hu ∈ D := root_mem_different K L a u hu hgenU
  have hV : rootInteger L b v hv ∈ D := root_mem_different K L b v hv hgenV
  have hUsq : (rootInteger L a u hu)^2 = (4*a+1 : ℤ) := by
    apply RingOfIntegers.coe_injective
    simpa using hu
  have hVsq : (rootInteger L b v hv)^2 = (4*b+1 : ℤ) := by
    apply RingOfIntegers.coe_injective
    simpa using hv
  obtain ⟨r,s,hrs⟩ := hcop
  have hA : ((4*a+1 : ℤ) : 𝓞 L) ∈ D := hUsq ▸ (show (rootInteger L a u hu)^2 ∈ D by rw [pow_two]; exact D.mul_mem_left _ hU)
  have hB : ((4*b+1 : ℤ) : 𝓞 L) ∈ D := hVsq ▸ (show (rootInteger L b v hv)^2 ∈ D by rw [pow_two]; exact D.mul_mem_left _ hV)
  apply (Ideal.eq_top_iff_one _).mpr
  have hm := D.add_mem (D.mul_mem_left (r : 𝓞 L) hA) (D.mul_mem_left (s : 𝓞 L) hB)
  convert hm using 1
  exact_mod_cast hrs.symm

end GenusUnramified


namespace OddRadicalDiscriminant
open NumberField
open scoped Classical
variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- A radicand congruent to one modulo four itself lies in the different. -/
theorem radicand_mem (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1)
    (hgen : Algebra.adjoin K {u} = ⊤) : ((4*a+1 : ℤ) : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  have hr := GenusUnramified.root_mem_different K L a u hu hgen
  have hs : (GenusUnramified.rootInteger L a u hu)^2 = ((4*a+1 : ℤ) : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    simpa only [map_pow,GenusUnramified.coe_rootInteger,map_intCast,Int.cast_add,Int.cast_mul,Int.cast_ofNat,Int.cast_one] using hu
  have h := Ideal.mul_mem_left (differentIdeal (𝓞 K) (𝓞 L)) (GenusUnramified.rootInteger L a u hu) hr
  rwa [← pow_two,hs] at h

theorem norm_span_int (a : ℤ) : Ideal.absNorm (Ideal.span {(a : 𝓞 L)}) = a.natAbs^Module.finrank ℚ L := by
  rw [Ideal.absNorm_span_singleton]
  have hn := Algebra.norm_algebraMap_of_basis (RingOfIntegers.basis L) a
  rw [← Module.finrank_eq_card_basis (RingOfIntegers.basis L),RingOfIntegers.rank] at hn
  simpa only [map_intCast,Int.cast_id,Int.natAbs_pow] using congrArg Int.natAbs hn

/-- A uniform divisibility bound; no quadratic discriminant formula is needed. -/
theorem discr_dvd (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1)
    (hgen : Algebra.adjoin K {u} = ⊤) :
    (NumberField.discr L).natAbs ∣ (4*a+1).natAbs^Module.finrank ℚ L *
      (NumberField.discr K).natAbs^Module.finrank K L := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem _).mpr (radicand_mem K L a u hu hgen))
  rw [norm_span_int] at hd
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)]
  exact mul_dvd_mul_right hd _

/-- Such a radical adjunction preserves odd absolute discriminant. -/
theorem odd (hodd : IsCoprime (NumberField.discr K) (2 : ℤ))
    (a : ℤ) (u : L) (hu : u^2 = 4*(a : L)+1) (hgen : Algebra.adjoin K {u} = ⊤) :
    IsCoprime (NumberField.discr L) (2 : ℤ) := by
  have ha : IsCoprime (4*a+1) (2 : ℤ) := ⟨1,-2*a,by ring⟩
  rw [Int.isCoprime_iff_nat_coprime] at hodd ha ⊢
  have hc := (ha.pow_left (Module.finrank ℚ L)).mul_left (hodd.pow_left (Module.finrank K L))
  exact hc.of_dvd_left (discr_dvd K L a u hu hgen)

end OddRadicalDiscriminant



/- Squareclasses under one quadratic radical adjunction. -/



/- Adjoining square roots of nonnegative rationals preserves total reality. -/


namespace BiquadraticBase
open NumberField
open scoped Classical

structure Data (D : ℕ) where
  B : Type
  field : Field B
  numberField : NumberField B
  real : IsTotallyReal B
  sqrtFive : B
  sqrtD : B
  five_sq : sqrtFive^2 = 5
  D_sq : sqrtD^2 = D
  degree : Module.finrank ℚ B = 4
  odd : IsCoprime (NumberField.discr B) (2 : ℤ)
  discr_bound : (NumberField.discr B).natAbs ≤ 625*D^4

attribute [instance] Data.field Data.numberField Data.real

/-- Two independent positive odd radicands give a real quartic base with
uniform odd-discriminant control. -/
theorem exists_data (D : ℕ) (hDpos : 0 < D) (a : ℤ) (hDa : (D : ℤ) = 4*a+1)
    (h5 : ¬ IsSquare (5 : ℚ)) (hD : ¬ IsSquare (D : ℚ)) (h5D : ¬ IsSquare (5*(D : ℚ))) :
    Nonempty (Data D) := by
  letI : Fact (∀ x : ℚ, x^2 ≠ (5 : ℚ)+0*x) :=
    ⟨fun x hx => h5 ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let F := QuadraticAlgebra ℚ (5 : ℚ) 0
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let u : F := QuadraticSquareclass.root ℚ 5
  have hu : u^2 = 5 := by simpa using QuadraticSquareclass.root_sq ℚ (5 : ℚ)
  have hgenF : Algebra.adjoin ℚ {u} = ⊤ := QuadraticSquareclass.adjoin_root ℚ (5 : ℚ)
  letI : IsTotallyReal F := TotallyRealRadicals.of_adjoin_singleton ℚ F u 5 (by norm_num) (by simpa using hu) hgenF
  have hDF : ¬ IsSquare (D : F) := by
    intro h
    have h' : IsSquare (algebraMap ℚ F (D : ℚ)) := by simpa using h
    rcases QuadraticSquareclass.squareclass_cases ℚ (5 : ℚ) (D : ℚ) h' with h' | h'
    · exact hD h'
    · exact h5D (by simpa only [mul_comm] using h')
  letI : Fact (∀ x : F, x^2 ≠ (D : F)+0*x) :=
    ⟨fun x hx => hDF ⟨x,by simpa only [zero_mul,add_zero,pow_two] using hx.symm⟩⟩
  let B := QuadraticAlgebra F (D : F) 0
  letI : NumberField B := NumberField.of_module_finite F B
  let v : B := QuadraticSquareclass.root F (D : F)
  have hv : v^2 = D := by simpa only [map_natCast] using QuadraticSquareclass.root_sq F (D : F)
  have hgenB : Algebra.adjoin F {v} = ⊤ := QuadraticSquareclass.adjoin_root F (D : F)
  letI : IsTotallyReal B := TotallyRealRadicals.of_adjoin_singleton F B v (D : ℚ)
    (by positivity) (by simpa using hv) hgenB
  have hdF : Module.finrank ℚ F = 2 := QuadraticAlgebra.finrank_eq_two 5 0
  have hdFB : Module.finrank F B = 2 := QuadraticAlgebra.finrank_eq_two (D : F) 0
  have hdB : Module.finrank ℚ B = 4 := by
    rw [← Module.finrank_mul_finrank ℚ F B,hdF,hdFB]
  have hu' : u^2 = 4*(1 : F)+1 := by norm_num; exact hu
  have hv' : v^2 = 4*(a : B)+1 := by rw [hv]; exact_mod_cast hDa
  have hoddQ : IsCoprime (NumberField.discr ℚ) (2 : ℤ) := by norm_num [Int.isCoprime_iff_nat_coprime]
  have hoddF := OddRadicalDiscriminant.odd ℚ F hoddQ 1 u hu' hgenF
  have hoddB := OddRadicalDiscriminant.odd F B hoddF a v hv' hgenB
  have hdiscF : (NumberField.discr F).natAbs ≤ 25 := by
    have hdiv := OddRadicalDiscriminant.discr_dvd ℚ F 1 u hu' hgenF
    norm_num [hdF] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hdiscB : (NumberField.discr B).natAbs ≤ 625*D^4 := by
    have hdiv := OddRadicalDiscriminant.discr_dvd F B a v hv' hgenB
    rw [← hDa,Int.natAbs_natCast,hdB,hdFB] at hdiv
    have hp : 0 < D^4*(NumberField.discr F).natAbs^2 := by
      exact mul_pos (pow_pos hDpos _) (pow_pos (Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)) _)
    apply (Nat.le_of_dvd hp hdiv).trans
    nlinarith [Nat.pow_le_pow_left hdiscF 2]
  refine ⟨{
    B := B
    field := inferInstance
    numberField := inferInstance
    real := inferInstance
    sqrtFive := algebraMap F B u
    sqrtD := v
    five_sq := by rw [← map_pow,hu,map_ofNat]
    D_sq := hv
    degree := hdB
    odd := hoddB
    discr_bound := hdiscB }⟩

end BiquadraticBase

namespace GenusStep
open NumberField
open scoped Classical

variable (K : Type*) [Field K] [NumberField K] (a b : ℤ)
variable [Fact (∀ x : K, x^2 ≠ (4*(a : K)+1)+0*x)]

abbrev L := QuadraticAlgebra K (4*(a : K)+1) 0

noncomputable instance : NumberField (L K a) := NumberField.of_module_finite K (L K a)

noncomputable def u : L K a := QuadraticSquareclass.root K (4*(a : K)+1)

@[simp] theorem u_sq : (u K a)^2 = 4*(a : L K a)+1 := by
  simpa only [map_add,map_mul,map_intCast,map_one,map_ofNat] using QuadraticSquareclass.root_sq K (4*(a : K)+1)

noncomputable def v (w : K) : L K a := algebraMap K (L K a) w / u K a

theorem u_ne_zero (ha : 4*a+1 ≠ 0) : u K a ≠ 0 := by
  intro h
  have hs := u_sq K a
  rw [h,zero_pow (by norm_num),eq_comm] at hs
  apply ha
  exact_mod_cast hs

theorem v_sq (w : K) (hw : w^2 = (4*(a : K)+1)*(4*(b : K)+1))
    (ha : 4*a+1 ≠ 0) : (v K a w)^2 = 4*(b : L K a)+1 := by
  have hw' : (algebraMap K (L K a) w)^2 =
      (4*(a : L K a)+1)*(4*(b : L K a)+1) := by
    simpa only [map_pow,map_mul,map_add,map_ofNat,map_intCast,map_one] using congrArg (algebraMap K (L K a)) hw
  rw [v,div_pow,u_sq]
  have ha' : (4*(a : L K a)+1) ≠ 0 := by exact_mod_cast ha
  apply (div_eq_iff ha').mpr
  simpa [mul_comm] using hw'

omit [NumberField K] in
theorem adjoin_u : Algebra.adjoin K {u K a} = ⊤ := QuadraticSquareclass.adjoin_root K _

theorem adjoin_v (w : K) (hw : w^2 = (4*(a : K)+1)*(4*(b : K)+1))
    (ha : 4*a+1 ≠ 0) (hb : 4*b+1 ≠ 0) : Algebra.adjoin K {v K a w} = ⊤ := by
  have hu0 := u_ne_zero K a ha
  have hb' : (4*(b : L K a)+1) ≠ 0 := by exact_mod_cast hb
  have hw' : (algebraMap K (L K a) w)^2 =
      (4*(a : L K a)+1)*(4*(b : L K a)+1) := by
    simpa only [map_pow,map_mul,map_add,map_ofNat,map_intCast,map_one] using congrArg (algebraMap K (L K a)) hw
  have he : u K a = algebraMap K (L K a) (w/(4*(b : K)+1))*v K a w := by
    rw [v,map_div₀,map_add,map_mul,map_ofNat,map_intCast,map_one]
    field_simp
    linear_combination (4*(b : L K a)+1)*(u_sq K a)-hw'
  apply top_unique
  rw [← adjoin_u K a]
  apply Algebra.adjoin_le
  intro x hx
  have hx' : x = u K a := Set.mem_singleton_iff.mp hx
  subst x
  rw [he]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin (Set.mem_singleton _))

theorem unramified (w : K) (hw : w^2 = (4*(a : K)+1)*(4*(b : K)+1))
    (ha : 4*a+1 ≠ 0) (hb : 4*b+1 ≠ 0) (hcop : IsCoprime (4*a+1) (4*b+1)) :
    differentIdeal (𝓞 K) (𝓞 (L K a)) = ⊤ :=
  GenusUnramified.different_eq_top K (L K a) a b hcop (u K a) (v K a w)
    (u_sq K a) (v_sq K a b w hw ha) (adjoin_u K a) (adjoin_v K a b w hw ha hb)

theorem totally_real [IsTotallyReal K] (ha : 0 ≤ 4*a+1) : IsTotallyReal (L K a) := by
  apply TotallyRealRadicals.of_adjoin_singleton K (L K a) (u K a) (4*a+1 : ℚ) (by exact_mod_cast ha) ?_ (adjoin_u K a)
  simp

end GenusStep

namespace GenusStepExistence
open NumberField
open scoped Classical
universe u
variable (K : Type u) [Field K] [NumberField K] (a b : ℤ)

/-- One possibly-trivial unramified square-root adjunction, together with
the complementary product radical needed for iterating the construction. -/
structure Data where
  carrier : Type u
  instField : Field carrier
  instNumberField : NumberField carrier
  instAlgebra : Algebra K carrier
  instReal : IsTotallyReal carrier
  root : carrier
  remainder : carrier
  root_sq : root^2 = 4*(a : carrier)+1
  remainder_sq : remainder^2 = 4*(b : carrier)+1
  adjoin_root : Algebra.adjoin K {root} = ⊤
  unramified : differentIdeal (𝓞 K) (𝓞 carrier) = ⊤

attribute [instance] Data.instField Data.instNumberField Data.instAlgebra Data.instReal

variable [IsTotallyReal K]

theorem exists_data (w : K) (hw : w^2 = (4*(a : K)+1)*(4*(b : K)+1))
    (ha : 0 < 4*a+1) (hb : 0 < 4*b+1) (hcop : IsCoprime (4*a+1) (4*b+1)) :
    Nonempty (Data K a b) := by
  classical
  by_cases hs : IsSquare (4*(a : K)+1)
  · obtain ⟨x,hx⟩ := hs
    have hx' : x^2 = 4*(a : K)+1 := by simpa [pow_two] using hx.symm
    have ha' : (4*(a : K)+1) ≠ 0 := by exact_mod_cast ha.ne'
    have hrem : (w/x)^2 = 4*(b : K)+1 := by
      rw [div_pow,hx',hw]
      exact mul_div_cancel_left₀ _ ha'
    refine ⟨{
      carrier := K
      instField := inferInstance
      instNumberField := inferInstance
      instAlgebra := inferInstance
      instReal := inferInstance
      root := x
      remainder := w/x
      root_sq := hx'
      remainder_sq := hrem
      adjoin_root := Subsingleton.elim _ _
      unramified := ?_ }⟩
    apply (Ideal.eq_top_iff_one _).mpr
    have hd := QuadraticDifferent.derivative_mem K K (0 : 𝓞 K) (Subsingleton.elim _ _) Polynomial.X (by simp)
    simpa using hd
  · letI : Fact (∀ x : K, x^2 ≠ (4*(a : K)+1)+0*x) :=
      ⟨fun x hx => hs ⟨x,by simpa [pow_two] using hx.symm⟩⟩
    letI : IsTotallyReal (GenusStep.L K a) := GenusStep.totally_real K a ha.le
    exact ⟨{
      carrier := GenusStep.L K a
      instField := inferInstance
      instNumberField := inferInstance
      instAlgebra := inferInstance
      instReal := inferInstance
      root := GenusStep.u K a
      remainder := GenusStep.v K a w
      root_sq := GenusStep.u_sq K a
      remainder_sq := GenusStep.v_sq K a b w hw ha.ne'
      adjoin_root := GenusStep.adjoin_u K a
      unramified := GenusStep.unramified K a b w hw ha.ne' hb.ne' hcop }⟩

end GenusStepExistence



/- Elementary helper lemmas for iterated unramified radical adjunctions. -/
namespace GenusTowerHelpers
open NumberField
open scoped Classical BigOperators

variable (K E L : Type*) [Field K] [Field E] [Field L]
  [NumberField K] [NumberField E] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

theorem unramified_trans
    (hE : differentIdeal (𝓞 K) (𝓞 E) = ⊤) (hL : differentIdeal (𝓞 E) (𝓞 L) = ⊤) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) (𝓞 E) (𝓞 L),hE,hL,Ideal.map_top]
  simp

omit [NumberField K] [NumberField E] [NumberField L] in
/-- Adjoining a generating set at each level gives a generating set at the bottom. -/
theorem adjoin_trans (S : Set E) (T : Set L)
    (hS : Algebra.adjoin K S = ⊤) (hT : Algebra.adjoin E T = ⊤) :
    Algebra.adjoin K ((algebraMap E L '' S) ∪ T) = ⊤ := by
  rw [← Algebra.adjoin_eq_adjoin_union K S T hS,hT,Subalgebra.restrictScalars_top]

/-- Finite products of integers congruent to1 modulo4 have the same form. -/
theorem prod_four_add_one {ι : Type*} (a : ι → ℤ) (s : Finset ι) :
    ∃ b : ℤ, ∏ i ∈ s, (4*a i+1) = 4*b+1 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨b,hb⟩ := ih
    refine ⟨4*a i*b+a i+b,?_⟩
    rw [Finset.prod_insert hi,hb]
    ring

end GenusTowerHelpers

namespace UnramifiedRadicalData
open NumberField
open scoped BigOperators Classical
universe u v
variable (K : Type u) [Field K] [NumberField K] {ι : Type v} (a : ι → ℤ) (s : Finset ι)

/-- A totally real unramified field generated by prescribed square roots. -/
structure Data where
  carrier : Type u
  instField : Field carrier
  instNumberField : NumberField carrier
  instAlgebra : Algebra K carrier
  instReal : IsTotallyReal carrier
  roots : ι → carrier
  roots_sq : ∀ i ∈ s, (roots i)^2 = 4*(a i : carrier)+1
  adjoin_roots : Algebra.adjoin K (roots '' (s : Set ι)) = ⊤
  unramified : differentIdeal (𝓞 K) (𝓞 carrier) = ⊤

attribute [instance] Data.instField Data.instNumberField Data.instAlgebra Data.instReal

/-- The genus-field construction: when a base contains the product radical,
all pairwise-coprime odd prime-discriminant radicals can be adjoined unramified. -/
theorem exists_data [IsTotallyReal K]
    (hpos : ∀ i ∈ s, 0 < 4*a i+1)
    (hcop : Set.Pairwise (s : Set ι) (fun i j => IsCoprime (4*a i+1) (4*a j+1)))
    (w : K) (hw : w^2 = ∏ i ∈ s, (4*(a i : K)+1)) :
    Nonempty (Data K a s) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
    refine ⟨{
      carrier := K
      instField := inferInstance
      instNumberField := inferInstance
      instAlgebra := inferInstance
      instReal := inferInstance
      roots := fun _ => 0
      roots_sq := by simp
      adjoin_roots := Subsingleton.elim _ _
      unramified := ?_ }⟩
    apply (Ideal.eq_top_iff_one _).mpr
    have hd := QuadraticDifferent.derivative_mem K K (0 : 𝓞 K) (Subsingleton.elim _ _) Polynomial.X (by simp)
    simpa using hd
  | @insert j s hjs ih =>
    obtain ⟨b,hb⟩ := GenusTowerHelpers.prod_four_add_one a s
    have hjpos : 0 < 4*a j+1 := hpos j (Finset.mem_insert_self _ _)
    have hbpos : 0 < 4*b+1 := by
      rw [← hb]
      exact Finset.prod_pos (fun i hi => hpos i (Finset.mem_insert_of_mem hi))
    have hjcop : IsCoprime (4*a j+1) (4*b+1) := by
      rw [← hb]
      apply IsCoprime.prod_right
      intro i hi
      exact hcop (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hi) (fun he => hjs (he ▸ hi))
    have hw' : w^2 = (4*(a j : K)+1)*(4*(b : K)+1) := by
      rw [Finset.prod_insert hjs] at hw
      have hb' : (∏ i ∈ s, (4*(a i : K)+1)) = 4*(b : K)+1 := by exact_mod_cast hb
      rwa [hb'] at hw
    obtain ⟨E⟩ := GenusStepExistence.exists_data K (a j) b w hw' hjpos hbpos hjcop
    let F := E.carrier
    have hpos' : ∀ i ∈ s, 0 < 4*a i+1 := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
    have hcop' : Set.Pairwise (s : Set ι) (fun i j => IsCoprime (4*a i+1) (4*a j+1)) :=
      hcop.mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
    have hrem : E.remainder^2 = ∏ i ∈ s, (4*(a i : F)+1) := by
      have hb' : (∏ i ∈ s, (4*(a i : F)+1)) = 4*(b : F)+1 := by exact_mod_cast hb
      rw [hb']
      exact E.remainder_sq
    obtain ⟨D⟩ := ih F hpos' hcop' E.remainder hrem
    let L := D.carrier
    letI : Algebra K L := Algebra.compHom L (algebraMap K F)
    letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
    let roots : ι → L := fun i => if i=j then algebraMap F L E.root else D.roots i
    have hroots (i : ι) (hi : i ∈ insert j s) : (roots i)^2 = 4*(a i : L)+1 := by
      by_cases hij : i=j
      · subst i
        simp only [roots,if_pos rfl,← map_pow,E.root_sq,map_add,map_mul,map_intCast,map_ofNat,map_one]
      · exact (show roots i = D.roots i from if_neg hij) ▸ D.roots_sq i ((Finset.mem_insert.mp hi).resolve_left hij)
    have hgen : Algebra.adjoin K (roots '' (↑(insert j s) : Set ι)) = ⊤ := by
      have hg := GenusTowerHelpers.adjoin_trans K F L {E.root} (D.roots '' (s : Set ι)) E.adjoin_root D.adjoin_roots
      apply top_unique
      rw [← hg]
      apply Algebra.adjoin_mono
      rintro x (hx|hx)
      · obtain ⟨y,hy,rfl⟩ := hx
        have hy' := Set.mem_singleton_iff.mp hy
        subst y
        exact ⟨j,Finset.mem_insert_self _ _,by simp [roots]⟩
      · obtain ⟨i,hi,rfl⟩ := hx
        exact ⟨i,Finset.mem_insert_of_mem hi,by simp [roots,show i ≠ j from fun he => hjs (he ▸ hi)]⟩
    exact ⟨{
      carrier := L
      instField := inferInstance
      instNumberField := inferInstance
      instAlgebra := inferInstance
      instReal := inferInstance
      roots := roots
      roots_sq := hroots
      adjoin_roots := hgen
      unramified := GenusTowerHelpers.unramified_trans K F L E.unramified D.unramified }⟩

end UnramifiedRadicalData

namespace FiniteRadicalExtension
open scoped Classical BigOperators
universe u v
variable (K : Type u) [Field K] {ι : Type v} (a : ι → K) (s : Finset ι)

/-- A finite multiquadratic extension, with degree and squareclass control. -/
structure Data where
  carrier : Type u
  instField : Field carrier
  instAlgebra : Algebra K carrier
  instFinite : Module.Finite K carrier
  roots : ι → carrier
  roots_sq : ∀ i ∈ s, (roots i)^2 = algebraMap K carrier (a i)
  adjoin_roots : Algebra.adjoin K (roots '' (s : Set ι)) = ⊤
  degree : Module.finrank K carrier = 2^s.card
  squareclass : ∀ b : K, IsSquare (algebraMap K carrier b) →
    ∃ t : Finset ι, t ⊆ s ∧ IsSquare (b*∏ i ∈ t, a i)

attribute [instance] Data.instField Data.instAlgebra Data.instFinite

variable [CharZero K]

/-- Independent squareclasses give the expected finite multiquadratic extension. -/
theorem exists_data
    (hind : ∀ t : Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅) :
    Nonempty (Data K a s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨{
      carrier := K
      instField := inferInstance
      instAlgebra := inferInstance
      instFinite := inferInstance
      roots := fun _ => 0
      roots_sq := by simp
      adjoin_roots := Subsingleton.elim _ _
      degree := by simp
      squareclass := fun b hb => ⟨∅,by simp,by simpa using hb⟩ }⟩
  | @insert j s hjs ih =>
    have hsind : ∀ t : Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅ :=
      fun t ht => hind t (ht.trans (Finset.subset_insert j s))
    obtain ⟨E⟩ := ih hsind
    let F := E.carrier
    let c : F := algebraMap K F (a j)
    have hc : ¬ IsSquare c := by
      intro h
      obtain ⟨t,ht,hsq⟩ := E.squareclass (a j) h
      have hjt : j ∉ t := fun hj => hjs (ht hj)
      have he := hind (insert j t) (Finset.insert_subset_insert j ht)
        (by simpa [Finset.prod_insert hjt] using hsq)
      exact Finset.insert_ne_empty j t he
    letI : Fact (∀ x : F, x^2 ≠ c+0*x) := ⟨fun x hx => hc ⟨x,by simpa [pow_two] using hx.symm⟩⟩
    let L := QuadraticAlgebra F c 0
    letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
    letI : FiniteDimensional K L := Module.Finite.trans F L
    let root : ι → L := fun i => if i=j then QuadraticSquareclass.root F c else algebraMap F L (E.roots i)
    have hroots (i : ι) (hi : i ∈ insert j s) : (root i)^2 = algebraMap K L (a i) := by
      by_cases hij : i=j
      · subst i
        simp only [root,if_pos rfl]
        exact QuadraticSquareclass.root_sq F c
      · have his : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hij
        simp only [root,if_neg hij,← map_pow,E.roots_sq i his]
        rfl
    have hgen : Algebra.adjoin K (root '' (↑(insert j s) : Set ι)) = ⊤ := by
      let S := Algebra.adjoin K (root '' (↑(insert j s) : Set ι))
      let φ : F →ₐ[K] L := IsScalarTower.toAlgHom K F L
      have hold : Algebra.adjoin K (E.roots '' (s : Set ι)) ≤ S.comap φ := by
        apply Algebra.adjoin_le
        rintro x ⟨i,hi,rfl⟩
        change algebraMap F L (E.roots i) ∈ S
        have hij : i ≠ j := fun he => hjs (he ▸ hi)
        have hx := Algebra.subset_adjoin (R := K) (Set.mem_image_of_mem root (show i ∈ (↑(insert j s) : Set ι) from Finset.mem_insert_of_mem hi))
        simpa only [root,if_neg hij] using hx
      have hF (x : F) : algebraMap F L x ∈ S := by
        apply hold
        rw [E.adjoin_roots]
        trivial
      have hr : QuadraticSquareclass.root F c ∈ S := by
        have hx := Algebra.subset_adjoin (R := K) (Set.mem_image_of_mem root (show j ∈ (↑(insert j s) : Set ι) from Finset.mem_insert_self _ _))
        simpa only [root,if_pos rfl] using hx
      apply top_unique
      intro z _
      have hz := S.add_mem (hF z.re) (S.mul_mem (hF z.im) hr)
      have he : algebraMap F L z.re+algebraMap F L z.im*QuadraticSquareclass.root F c = z := by
        change QuadraticAlgebra.mk (z.re+(z.im*0+c*0*1)) (0+(z.im*1+0*0+0*0*1)) = z
        ext <;> simp
      simpa only [he] using hz
    refine ⟨{
      carrier := L
      instField := inferInstance
      instAlgebra := inferInstance
      instFinite := inferInstance
      roots := root
      roots_sq := hroots
      adjoin_roots := hgen
      degree := ?_
      squareclass := ?_ }⟩
    · have he := Module.finrank_mul_finrank K F L
      rw [QuadraticAlgebra.finrank_eq_two,E.degree] at he
      simpa [Finset.card_insert_of_notMem hjs,pow_succ] using he.symm
    · intro b hb
      have hb' : IsSquare (algebraMap F L (algebraMap K F b)) := hb
      rcases QuadraticSquareclass.squareclass_cases F c (algebraMap K F b) hb' with h | h
      · obtain ⟨t,ht,hsq⟩ := E.squareclass b h
        exact ⟨t,ht.trans (Finset.subset_insert _ _),hsq⟩
      · have he : IsSquare (algebraMap K F (b*a j)) := by simpa [map_mul,c] using h
        obtain ⟨t,ht,hsq⟩ := E.squareclass (b*a j) he
        have hjt : j ∉ t := fun hj => hjs (ht hj)
        exact ⟨insert j t,Finset.insert_subset_insert j ht,by simpa [Finset.prod_insert hjt,mul_assoc] using hsq⟩

end FiniteRadicalExtension

namespace FiniteRadicalExtension
open Polynomial
open scoped Classical BigOperators
universe u v
variable (K : Type u) [Field K] {ι : Type v} (a : ι → K) (s : Finset ι) (E : Data K a s)

noncomputable def polynomial : K[X] := ∏ i ∈ s, (X^2-C (a i))

private theorem polynomial_monic : (polynomial K a s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C (a i) (by norm_num))

instance splittingField : Polynomial.IsSplittingField K E.carrier (polynomial K a s) where
  splits' := by
    rw [polynomial,Polynomial.map_prod]
    apply Polynomial.Splits.prod
    intro i hi
    simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C]
    have he : (X^2-C (algebraMap K E.carrier (a i)) : E.carrier[X]) =
        (X-C (E.roots i))*(X-C (-E.roots i)) := by
      rw [map_neg]
      calc
        X^2-C (algebraMap K E.carrier (a i)) = X^2-C ((E.roots i)^2) := by rw [E.roots_sq i hi]
        _ = _ := by rw [map_pow]; ring
    rw [he]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)
  adjoin_rootSet' := by
    apply top_unique
    rw [← E.adjoin_roots]
    apply Algebra.adjoin_mono
    rintro x ⟨i,hi,rfl⟩
    apply (polynomial_monic K a s).mem_rootSet.mpr
    rw [polynomial,map_prod]
    apply Finset.prod_eq_zero hi
    simp [E.roots_sq i hi]

instance [CharZero K] : IsGalois K E.carrier := by
  letI : Normal K E.carrier := Normal.of_isSplittingField (polynomial K a s)
  exact {}

theorem is_two_group [CharZero K] : IsPGroup 2 Gal(E.carrier/K) := by
  apply IsPGroup.of_card (n := s.card)
  rw [IsGalois.card_aut_eq_finrank,E.degree]

end FiniteRadicalExtension

namespace FiniteRadicalExtension
open NumberField
open scoped Classical BigOperators
variable {ι : Type*} (a : ι → ℚ) (s : Finset ι) (E : Data ℚ a s)

noncomputable instance : NumberField E.carrier := NumberField.of_module_finite ℚ E.carrier

theorem totally_real (ha : ∀ i ∈ s, 0 ≤ a i) : IsTotallyReal E.carrier := by
  letI : Algebra ℚ E.carrier := E.instAlgebra
  apply TotallyRealRadicals.of_adjoin ℚ E.carrier (E.roots '' (s : Set ι)) E.adjoin_roots
  rintro x ⟨i,hi,rfl⟩
  refine ⟨a i,ha i hi,?_⟩
  have hh := E.roots_sq i hi
  rw [Subsingleton.elim E.instAlgebra (DivisionRing.toRatAlgebra : Algebra ℚ E.carrier)] at hh
  exact hh

end FiniteRadicalExtension



/- Distinct rational primes represent independent squareclasses. -/
namespace IndependentPrimes
open scoped BigOperators Classical

variable {ι : Type*} (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)

include hp hinj in
theorem independent (s : Finset ι) (hs : IsSquare (∏ i ∈ s, (p i : ℚ))) : s = ∅ := by
  have hsq : IsSquare (∏ i ∈ s, p i) := by
    apply Rat.isSquare_natCast_iff.mp
    simpa using hs
  have hfree : Squarefree (∏ i ∈ s, p i) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Nat.coprime_iff_isRelPrime.mp ((hp i).coprime_iff_not_dvd.mpr (by
        intro h
        exact hij (hinj ((Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp h)))))
    · intro i hi
      exact (hp i).squarefree
  obtain ⟨x,hx⟩ := hsq
  have hunit : IsUnit x := hfree x (by rw [hx])
  have hx1 : x = 1 := Nat.isUnit_iff.mp hunit
  have hprod : ∏ i ∈ s, p i = 1 := by simpa [hx1] using hx
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hd := Finset.dvd_prod_of_mem p hi
  rw [hprod] at hd
  exact (hp i).not_dvd_one hd

end IndependentPrimes



/- Explicit finite prime data for the large genus certificate. -/
namespace LargePrimes
open scoped Classical BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def p : Fin 256 → ℕ := ![5,13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,197,229,233,241,257,269,277,281,293,313,317,337,349,353,373,389,397,401,409,421,433,449,457,461,509,521,541,557,569,577,593,601,613,617,641,653,661,673,677,701,709,733,757,761,769,773,797,809,821,829,853,857,877,881,929,937,941,953,977,997,1009,1013,1021,1033,1049,1061,1069,1093,1097,1109,1117,1129,1153,1181,1193,1201,1213,1217,1229,1237,1249,1277,1289,1297,1301,1321,1361,1373,1381,1409,1429,1433,1453,1481,1489,1493,1549,1553,1597,1601,1609,1613,1621,1637,1657,1669,1693,1697,1709,1721,1733,1741,1753,1777,1789,1801,1861,1873,1877,1889,1901,1913,1933,1949,1973,1993,1997,2017,2029,2053,2069,2081,2089,2113,2129,2137,2141,2153,2161,2213,2221,2237,2269,2273,2281,2293,2297,2309,2333,2341,2357,2377,2381,2389,2393,2417,2437,2441,2473,2477,2521,2549,2557,2593,2609,2617,2621,2633,2657,2677,2689,2693,2713,2729,2741,2749,2753,2777,2789,2797,2801,2833,2837,2857,2861,2897,2909,2917,2953,2957,2969,3001,3037,3041,3049,3061,3089,3109,3121,3137,3169,3181,3209,3217,3221,3229,3253,3257,3301,3313,3329,3361,3373,3389,3413,3433,3449,3457,3461,3469,3517,3529,3533,3541,3557,3581,3593,3613,3617,3637,3673,3677,3697,3701,3709,3733]
def a (i : Fin 256) : ℤ := (p i / 4 : ℕ)

theorem properties (i : Fin 256) : (p i).Prime ∧ p i % 4 = 1 ∧ p i ≤ 2^14 := by
  fin_cases i <;> norm_num [p]

theorem prime (i : Fin 256) : (p i).Prime := (properties i).1
theorem injective : Function.Injective p := by decide

theorem p_eq (i : Fin 256) : (p i : ℤ) = 4*a i+1 := by
  have h := Nat.mod_add_div (p i) 4
  rw [(properties i).2.1] at h
  dsimp only [a]
  exact_mod_cast (by omega : p i = 4*(p i/4)+1)

def rest : Finset (Fin 256) := Finset.univ.erase 0
noncomputable def D : ℕ := ∏ i ∈ rest, p i

theorem D_pos : 0 < D := Finset.prod_pos (fun i _ => (prime i).pos)

theorem prod_eq : ∏ i : Fin 256, p i = 5*D := by
  have he := Finset.mul_prod_erase Finset.univ p (show (0 : Fin 256) ∈ Finset.univ by simp)
  simpa only [D,rest,show p 0 = 5 from rfl] using he.symm

theorem pos (i : Fin 256) : 0 < 4*a i+1 := by rw [← p_eq]; exact_mod_cast (prime i).pos

theorem coprime : Set.Pairwise (Set.univ : Set (Fin 256)) (fun i j => IsCoprime (4*a i+1) (4*a j+1)) := by
  intro i _ j _ hij
  rw [← p_eq,← p_eq]
  apply Nat.isCoprime_iff_coprime.mpr
  apply (prime i).coprime_iff_not_dvd.mpr
  intro h
  exact hij (injective ((Nat.prime_dvd_prime_iff_eq (prime i) (prime j)).mp h))

theorem D_bound : D ≤ (2^14)^255 := by
  have h := Finset.prod_le_prod (s := rest) (f := p) (g := fun _ => 2^14)
    (fun i _ => Nat.zero_le _) (fun i _ => (properties i).2.2)
  simpa only [D,Finset.prod_const,rest,Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ,Fintype.card_fin,Nat.reduceSub] using h

end LargePrimes

namespace LargePrimes
set_option maxRecDepth 100000
open scoped Classical BigOperators

theorem five_nonsquare : ¬ IsSquare (5 : ℚ) := by
  intro h
  have he := IndependentPrimes.independent p prime injective ({0} : Finset (Fin 256)) (by simpa [p] using h)
  simp at he

theorem D_nonsquare : ¬ IsSquare (D : ℚ) := by
  intro h
  have he := IndependentPrimes.independent p prime injective rest (by simpa [D] using h)
  have hm : (1 : Fin 256) ∈ rest := by simp [rest]
  rw [he] at hm
  exact Finset.notMem_empty _ hm

theorem five_D_nonsquare : ¬ IsSquare (5*(D : ℚ)) := by
  intro h
  have hp : (∏ i : Fin 256, (p i : ℚ)) = 5*(D : ℚ) := by exact_mod_cast prod_eq
  have he := IndependentPrimes.independent p prime injective Finset.univ (hp ▸ h)
  have hm : (0 : Fin 256) ∈ (Finset.univ : Finset (Fin 256)) := Finset.mem_univ _
  rw [he] at hm
  exact Finset.notMem_empty _ hm

end LargePrimes

namespace LargePrimes
set_option maxRecDepth 100000
open scoped Classical

theorem D_form : ∃ a₀ : ℤ, (D : ℤ) = 4*a₀+1 := by
  obtain ⟨b,hb⟩ := GenusTowerHelpers.prod_four_add_one a rest
  refine ⟨b,?_⟩
  dsimp only [D]
  push_cast
  simpa only [← p_eq] using hb

end LargePrimes



/- Splitting fields generated by a finite family of square roots. -/
namespace SquareRootSplitting
open Polynomial
open scoped Classical BigOperators
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  {ι : Type*} (a : ι → K) (s : Finset ι) (roots : ι → L)

noncomputable def polynomial : K[X] := ∏ i ∈ s, (X^2-C (a i))

omit [Field L] [Algebra K L] in
theorem monic : (polynomial K a s).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C (a i) (by norm_num))

theorem splits (hroots : ∀ i ∈ s, (roots i)^2 = algebraMap K L (a i)) :
    ((polynomial K a s).map (algebraMap K L)).Splits := by
  rw [polynomial,Polynomial.map_prod]
  apply Polynomial.Splits.prod
  intro i hi
  simp only [Polynomial.map_sub,Polynomial.map_pow,map_X,map_C]
  have he : (X^2-C (algebraMap K L (a i)) : L[X]) = (X-C (roots i))*(X-C (-roots i)) := by
    rw [map_neg]
    calc
      X^2-C (algebraMap K L (a i)) = X^2-C ((roots i)^2) := by rw [hroots i hi]
      _ = _ := by rw [map_pow]; ring
  rw [he]
  exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)

theorem isSplittingField (hroots : ∀ i ∈ s, (roots i)^2 = algebraMap K L (a i))
    (hgen : Algebra.adjoin K (roots '' (s : Set ι)) = ⊤) :
    Polynomial.IsSplittingField K L (polynomial K a s) where
  splits' := splits K L a s roots hroots
  adjoin_rootSet' := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_mono
    rintro x ⟨i,hi,rfl⟩
    apply (monic K a s).mem_rootSet.mpr
    rw [polynomial,map_prod]
    apply Finset.prod_eq_zero hi
    simp [hroots i hi]

theorem isGalois [CharZero K] (hroots : ∀ i ∈ s, (roots i)^2 = algebraMap K L (a i))
    (hgen : Algebra.adjoin K (roots '' (s : Set ι)) = ⊤) : IsGalois K L := by
  letI : Polynomial.IsSplittingField K L (polynomial K a s) := isSplittingField K L a s roots hroots hgen
  letI : Normal K L := Normal.of_isSplittingField (polynomial K a s)
  exact {}

end SquareRootSplitting

namespace RadicalDegreeLower
open scoped Classical BigOperators

variable (K L : Type*) [Field K] [Field L] [CharZero K] [Algebra K L] [FiniteDimensional K L]
  {ι : Type*} (a : ι → K) (s : Finset ι)

theorem finrank_ge (hind : ∀ t : Finset ι, t ⊆ s → IsSquare (∏ i ∈ t, a i) → t = ∅)
    (roots : ι → L) (hroots : ∀ i ∈ s, (roots i)^2 = algebraMap K L (a i)) :
    2^s.card ≤ Module.finrank K L := by
  obtain ⟨E⟩ := FiniteRadicalExtension.exists_data K a s hind
  letI : Polynomial.IsSplittingField K E.carrier (SquareRootSplitting.polynomial K a s) :=
    SquareRootSplitting.isSplittingField K E.carrier a s E.roots E.roots_sq E.adjoin_roots
  let φ : E.carrier →ₐ[K] L := Polynomial.IsSplittingField.lift E.carrier
    (SquareRootSplitting.polynomial K a s) (SquareRootSplitting.splits K L a s roots hroots)
  rw [← E.degree]
  exact LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) φ.toRingHom.injective

end RadicalDegreeLower



/- A Galois group of a square-root generated field has exponent two. -/
namespace RadicalExponent
open scoped Classical

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

theorem aut_sq_eq_one (S : Set L) (hgen : Algebra.adjoin K S = ⊤)
    (hS : ∀ x ∈ S, ∃ a : K, x^2 = algebraMap K L a) (σ : Gal(L/K)) : σ^2 = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply AlgHom.ext_of_adjoin_eq_top hgen
  intro x hx
  obtain ⟨a,ha⟩ := hS x hx
  have hs : (σ x)^2 = x^2 := by
    rw [← map_pow,ha,σ.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · change σ (σ x) = x
    rw [h,h]
  · change σ (σ x) = x
    rw [h,map_neg,h,neg_neg]

end RadicalExponent



/- First cohomology of finite elementary 2-groups. -/
namespace ElementaryCohomology
open CategoryTheory
open scoped Classical

variable (G : Type) [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_sq (hs : ∀ g : G, g^2 = 1) (g h : G) : g*h = h*g := by
  have hinv (x : G) : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs x)
  calc
    g*h = (g*h)⁻¹ := (hinv _).symm
    _ = h⁻¹*g⁻¹ := mul_inv_rev _ _
    _ = h*g := by rw [hinv,hinv]


/-- The size of a finite exponent-two group is 2 to its first-cohomology rank. -/
theorem card_eq_pow_H1 (hs : ∀ g : G, g^2 = 1) :
    Nat.card G = 2^(Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) G (ZMod 2)) 1)) := by
  letI : CommGroup G := { ‹Group G› with mul_comm := comm_of_sq G hs }
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (n := 2)
    (fun x => show x.toMul^2 = 1 from hs x.toMul)
  let e : (Additive G →+ ZMod 2) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive G) := {
    toFun := fun f => f.toZModLinearMap 2
    invFun := fun f => f.toAddMonoidHom
    left_inv := fun f => rfl
    right_inv := fun f => rfl
    map_add' := fun f g => rfl
    map_smul' := fun r f => rfl }
  have he := (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod 2) G (ZMod 2))).toLinearEquiv.finrank_eq
  rw [he,e.finrank_eq,Subspace.dual_finrank_eq]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  simpa only [Nat.card_eq_fintype_card,ZMod.card] using hc

end ElementaryCohomology

namespace UnramifiedRadicalData
open NumberField
open scoped Classical
variable (K : Type*) [Field K] [NumberField K] {ι : Type*} (a : ι → ℤ) (s : Finset ι) (E : Data K a s)

theorem aut_sq (σ : Gal(E.carrier/K)) : σ^2 = 1 := by
  apply RadicalExponent.aut_sq_eq_one K E.carrier (E.roots '' (s : Set ι)) E.adjoin_roots ?_ σ
  rintro x ⟨i,hi,rfl⟩
  refine ⟨4*(a i : K)+1,?_⟩
  simpa only [map_add,map_mul,map_ofNat,map_intCast,map_one] using E.roots_sq i hi

theorem galois : IsGalois K E.carrier := by
  apply SquareRootSplitting.isGalois K E.carrier (fun i => 4*(a i : K)+1) s E.roots ?_ E.adjoin_roots
  intro i hi
  simpa only [map_add,map_mul,map_ofNat,map_intCast,map_one] using E.roots_sq i hi

end UnramifiedRadicalData


namespace LargeInitialGenusCertificate
set_option maxRecDepth 100000
open NumberField CategoryTheory
open scoped Classical BigOperators

/-- Finite starting data with explicit discriminant and generator-rank bounds. -/
structure Data where
  B : Type
  fieldB : Field B
  numberFieldB : NumberField B
  realB : IsTotallyReal B
  sqrtFive : B
  sqrtFive_sq : sqrtFive^2 = 5
  degreeB : Module.finrank ℚ B = 4
  oddB : IsCoprime (NumberField.discr B) (2 : ℤ)
  discrB : 16*(NumberField.discr B).natAbs ≤ 2^14294
  L : Type
  fieldL : Field L
  numberFieldL : NumberField L
  realL : IsTotallyReal L
  algebra : Algebra B L
  galois : IsGalois B L
  unramified : differentIdeal (𝓞 B) (𝓞 L) = ⊤
  elementary : ∀ σ : Gal(L/B), σ^2 = 1
  generator_rank : 254 ≤ Module.finrank (ZMod 2)
    (groupCohomology (Rep.trivial (ZMod 2) Gal(L/B) (ZMod 2)) 1)

attribute [instance] Data.fieldB Data.numberFieldB Data.realB Data.fieldL Data.numberFieldL
  Data.realL Data.algebra Data.galois

set_option maxHeartbeats 4000000 in
/-- A kernel-checked list of256 primes supplies all finite arithmetic data. -/
theorem exists_data : Nonempty Data := by
  obtain ⟨a₀,ha₀⟩ := LargePrimes.D_form
  obtain ⟨E⟩ := BiquadraticBase.exists_data LargePrimes.D LargePrimes.D_pos a₀ ha₀
    LargePrimes.five_nonsquare LargePrimes.D_nonsquare LargePrimes.five_D_nonsquare
  let B := E.B
  let w : B := E.sqrtFive*E.sqrtD
  have hw : w^2 = ∏ i : Fin 256, (4*(LargePrimes.a i : B)+1) := by
    have hp : (∏ i : Fin 256, (4*(LargePrimes.a i : B)+1)) = 5*(LargePrimes.D : B) := by
      have hz : (∏ i : Fin 256, (4*LargePrimes.a i+1)) = (5*LargePrimes.D : ℕ) := by
        simp_rw [← LargePrimes.p_eq]
        exact_mod_cast LargePrimes.prod_eq
      exact_mod_cast hz
    rw [hp]
    dsimp only [w]
    rw [mul_pow,E.five_sq,E.D_sq]
  obtain ⟨U⟩ := UnramifiedRadicalData.exists_data B LargePrimes.a Finset.univ
    (fun i _ => LargePrimes.pos i) (by simpa using LargePrimes.coprime) w hw
  let L := U.carrier
  let aB : Fin 256 → B := fun i => 4*(LargePrimes.a i : B)+1
  have hrootsB (i : Fin 256) (hi : i ∈ (Finset.univ : Finset (Fin 256))) :
      (U.roots i)^2 = algebraMap B L (aB i) := by
    simpa only [aB,map_add,map_mul,map_intCast,map_ofNat,map_one] using U.roots_sq i hi
  letI : IsGalois B L := SquareRootSplitting.isGalois B L aB Finset.univ U.roots hrootsB U.adjoin_roots
  have hexp : ∀ σ : Gal(L/B), σ^2 = 1 := UnramifiedRadicalData.aut_sq B LargePrimes.a Finset.univ U
  have hrootsQ (i : Fin 256) (hi : i ∈ (Finset.univ : Finset (Fin 256))) :
      (U.roots i)^2 = algebraMap ℚ L (LargePrimes.p i : ℚ) := by
    have hp : (LargePrimes.p i : L) = 4*(LargePrimes.a i : L)+1 := by exact_mod_cast LargePrimes.p_eq i
    simpa only [map_natCast,Rat.cast_natCast,hp] using U.roots_sq i hi
  have hdegreeL : 2^256 ≤ Module.finrank ℚ L := by
    have hd := RadicalDegreeLower.finrank_ge ℚ L (fun i => (LargePrimes.p i : ℚ)) Finset.univ
      (fun t _ ht => IndependentPrimes.independent LargePrimes.p LargePrimes.prime LargePrimes.injective t ht)
      U.roots hrootsQ
    simpa using hd
  have hdegreeBL : 2^254 ≤ Module.finrank B L := by
    have hd := Module.finrank_mul_finrank ℚ B L
    rw [E.degree] at hd
    norm_num1 at hdegreeL ⊢
    omega
  have hH1 : 254 ≤ Module.finrank (ZMod 2)
      (groupCohomology (Rep.trivial (ZMod 2) Gal(L/B) (ZMod 2)) 1) := by
    have hc := ElementaryCohomology.card_eq_pow_H1 Gal(L/B) hexp
    rw [IsGalois.card_aut_eq_finrank] at hc
    apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
    simpa only [← hc] using hdegreeBL
  have hdisc : 16*(NumberField.discr B).natAbs ≤ 2^14294 := by
    calc
      _ ≤ 16*(625*LargePrimes.D^4) := Nat.mul_le_mul_left 16 E.discr_bound
      _ ≤ 2^14*((2^14)^255)^4 := by
        have hp := Nat.pow_le_pow_left LargePrimes.D_bound 4
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul (by norm_num : 16*625 ≤ 2^14) hp
      _ = _ := by
        rw [← pow_mul,← pow_mul,← pow_add]
  exact ⟨{
    B := B
    fieldB := inferInstance
    numberFieldB := inferInstance
    realB := inferInstance
    sqrtFive := E.sqrtFive
    sqrtFive_sq := E.five_sq
    degreeB := E.degree
    oddB := E.odd
    discrB := hdisc
    L := L
    fieldL := inferInstance
    numberFieldL := inferInstance
    realL := inferInstance
    algebra := inferInstance
    galois := inferInstance
    unramified := U.unramified
    elementary := hexp
    generator_rank := hH1 }⟩

end LargeInitialGenusCertificate

namespace LargeInitialGenusCertificate

/-- The explicit genus extension meets the large-rank layer condition. -/
noncomputable def Data.layer (E : Data) : LargeTowerCriterion.Layer E.B 254 where
  carrier := E.L
  field := inferInstance
  numberField := inferInstance
  real := inferInstance
  algebra := inferInstance
  galois := inferInstance
  pGroup := fun σ => ⟨1,by simpa only [pow_one] using E.elementary σ⟩
  unramified := E.unramified
  generator_rank := E.generator_rank

end LargeInitialGenusCertificate

namespace Erdos1207
open NumberField PrincipalInvolutionSequences
open Filter
open scoped Classical

/-- The finite certificate satisfies the numerical tower criterion, giving
the bounded-root-discriminant family required by the planar construction. -/
theorem power_saving_of_large_initial_data (E : LargeInitialGenusCertificate.Data) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ)^(1-c) := by
  have hclass := QuarticClassNumber.classRank_le E.B E.degreeB 14294 E.discrB
  have hnum : 4*(Module.finrank (ZMod 2) (ModTwo.V (C E.B))+2*Module.finrank ℚ E.B) ≤ 254^2 := by
    rw [E.degreeB]
    omega
  obtain ⟨M,hM⟩ := LargeTowerCriterion.arithmetic_family E.B 254 E.oddB ⟨E.layer⟩ (by norm_num) hnum
  exact power_saving_of_unbounded_unramified_family E.B E.sqrtFive E.sqrtFive_sq
    (fun n => (M n).carrier) (fun n => (M n).pGroup) hM (fun n => (M n).unramified)

end Erdos1207
namespace Erdos1207

/--
Let $P_d(n)$ be such that in any set of $n$ points in $\mathbb{R}^d$ there exist at least $P_d(n)$ many points which do not contain an isosceles triangle. Estimate $P_d(n)$ - in particular, is it true that\[P_2(n)<n^{1-c}\]for some constant $c>0$?
-/
theorem erdos_1207 :
    (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)) := by
  exact power_saving_of_large_initial_data (Classical.choice LargeInitialGenusCertificate.exists_data)

end Erdos1207

#print axioms Erdos1207.erdos_1207

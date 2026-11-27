import WaringSiegel.WSL2UnitCounting
import Mathlib.Data.Int.Interval

/-!
# Uniform counting of generators in archimedean boxes

A nonzero algebraic integer with every archimedean magnitude at most L has
all weighted logarithms bounded by d log L: its absolute norm is a positive
integer. Ratios of two associated integers in the box are therefore units
in a logarithmic box independent of the chosen principal ideal.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- If the total sum is nonnegative, an upper bound on every summand also
bounds the negative part of each summand by the sum of the upper bounds. -/
theorem abs_term_le_sum_upper {ι : Type*} [Fintype ι] (t c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hbound : ∀ i, t i ≤ c i) (hsum : 0 ≤ ∑ i, t i) (i : ι) :
    |t i| ≤ ∑ j, c j := by
  have htc : ∑ j : {j : ι // j ≠ i}, t j ≤ ∑ j : {j : ι // j ≠ i}, c j :=
    Finset.sum_le_sum fun j _ => hbound j
  have hcn : 0 ≤ ∑ j : {j : ι // j ≠ i}, c j :=
    Finset.sum_nonneg fun j _ => hc j
  have hcs := Fintype.sum_eq_add_sum_subtype_ne c i
  rw [Fintype.sum_eq_add_sum_subtype_ne t i] at hsum
  apply abs_le.mpr
  constructor <;> linarith [hc i, hbound i]

/-- All weighted logarithms of a boxed nonzero integer are uniformly bounded. -/
theorem integer_weighted_log_abs_le {x : 𝓞 K} (hx : x ≠ 0)
    {L : ℝ} (hL : 1 ≤ L) (hbox : ∀ w : InfinitePlace K, w (x : K) ≤ L)
    (w : InfinitePlace K) :
    |(w.mult : ℝ) * Real.log (w (x : K))| ≤
      (Module.finrank ℚ K : ℝ) * Real.log L := by
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hpos (v : InfinitePlace K) : 0 < v (x : K) := pos_iff.mpr hxK
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hprod : ∏ v : InfinitePlace K, v (x : K) ^ v.mult = absNorm x := by
    rw [prod_eq_abs_norm]
    simpa only [fieldAbsNorm, Rat.cast_abs] using fieldAbsNorm_integer x
  have hlogs : ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v (x : K)) =
      Real.log (absNorm x) := by
    rw [← hprod, Real.log_prod]
    · simp only [Real.log_pow]
    · intro v _
      exact pow_ne_zero _ (hpos v).ne'
  have hs : 0 ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v (x : K)) := by
    rw [hlogs]
    exact Real.log_nonneg (one_le_absNorm_integer hx)
  have hc (v : InfinitePlace K) : 0 ≤ (v.mult : ℝ) * Real.log L :=
    mul_nonneg (Nat.cast_nonneg _) hlogL
  have hb (v : InfinitePlace K) : (v.mult : ℝ) * Real.log (v (x : K)) ≤
      (v.mult : ℝ) * Real.log L :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (hpos v) (hbox v)) (Nat.cast_nonneg _)
  have hh := abs_term_le_sum_upper _ _ hc hb hs w
  have hmult : (∑ v : InfinitePlace K, (v.mult : ℝ)) = Module.finrank ℚ K := by
    exact_mod_cast (sum_mult_eq (K := K))
  rwa [← Finset.sum_mul, hmult] at hh

/-- Ratios of associated nonzero boxed integers have bounded logarithmic unit
coordinates; the bound does not depend on their principal ideal. -/
theorem logEmbedding_le_of_integer_mul_unit {x y : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0)
    (u : (𝓞 K)ˣ) (hu : x * u = y) {L : ℝ} (hL : 1 ≤ L)
    (hboxx : ∀ w : InfinitePlace K, w (x : K) ≤ L)
    (hboxy : ∀ w : InfinitePlace K, w (y : K) ≤ L) :
    ‖logEmbedding K (Additive.ofMul u)‖ ≤
      2 * (Module.finrank ℚ K : ℝ) * Real.log L := by
  have hR : 0 ≤ 2 * (Module.finrank ℚ K : ℝ) * Real.log L := by
    exact mul_nonneg (by positivity) (Real.log_nonneg hL)
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro w
  rw [logEmbedding_component, Real.norm_eq_abs]
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx
  have hxu : (x : K) * (u : K) = (y : K) := by exact_mod_cast hu
  have hlog : Real.log (w.val (y : K)) =
      Real.log (w.val (x : K)) + Real.log (w.val (u : K)) := by
    rw [← hxu, map_mul, Real.log_mul (pos_iff.mpr hxK).ne' (Units.pos_at_place u w.val).ne']
  have he : (w.val.mult : ℝ) * Real.log (w.val (u : K)) =
      (w.val.mult : ℝ) * Real.log (w.val (y : K)) -
        (w.val.mult : ℝ) * Real.log (w.val (x : K)) := by rw [hlog]; ring
  rw [he]
  calc
    _ ≤ |(w.val.mult : ℝ) * Real.log (w.val (y : K))| +
        |(w.val.mult : ℝ) * Real.log (w.val (x : K))| := abs_sub _ _
    _ ≤ (Module.finrank ℚ K : ℝ) * Real.log L +
        (Module.finrank ℚ K : ℝ) * Real.log L :=
      add_le_add (integer_weighted_log_abs_le hy hL hboxy w.val)
        (integer_weighted_log_abs_le hx hL hboxx w.val)
    _ = _ := by ring

/-- A finite set of generators of any one nonzero principal ideal has uniform
polylogarithmic size when every archimedean magnitude is at most L. The constant
depends only on K, and the exponent is precisely its Dirichlet unit rank. -/
theorem exists_associated_box_count_constant (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ T : Finset (𝓞 K),
      (∀ x ∈ T, ∀ w : InfinitePlace K, w (x : K) ≤ L) →
      ∀ a : 𝓞 K, a ≠ 0 →
        ((T.filter (fun x => Associated x a)).card : ℝ) ≤
          C * (1 + Real.log L) ^ rank K := by
  obtain ⟨C, hC, hcount⟩ := exists_unit_log_count_constant K
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨C * (1 + 2 * d) ^ rank K, mul_pos hC (pow_pos (by positivity) _), ?_⟩
  intro L hL T hbox a ha
  let F := T.filter (fun x => Associated x a)
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hR : 0 ≤ 2 * d * Real.log L := by positivity
  by_cases hF : F.Nonempty
  · obtain ⟨x, hxF⟩ := hF
    have hxa : Associated x a := (Finset.mem_filter.mp hxF).2
    have hx : x ≠ 0 := hxa.ne_zero_iff.mpr ha
    have hpair (y : F) : Associated x y :=
      hxa.trans (Finset.mem_filter.mp y.property).2.symm
    let f : F → (𝓞 K)ˣ := fun y => Classical.choose (hpair y)
    have hf (y : F) : x * f y = (y : 𝓞 K) := Classical.choose_spec (hpair y)
    have hinj : Function.Injective f := by
      intro y z he
      apply Subtype.ext
      rw [← hf y, ← hf z, he]
    let U : Finset (𝓞 K)ˣ := Finset.univ.image f
    have hUcard : U.card = F.card := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hU : ∀ u ∈ U, ‖logEmbedding K (Additive.ofMul u)‖ ≤ 2 * d * Real.log L := by
      intro u hu
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hu
      have hya : Associated (y : 𝓞 K) a := (Finset.mem_filter.mp y.property).2
      exact logEmbedding_le_of_integer_mul_unit hx (hya.ne_zero_iff.mpr ha) (f y) (hf y) hL
        (hbox x (Finset.mem_filter.mp hxF).1)
        (hbox y (Finset.mem_filter.mp y.property).1)
    have hc := hcount (2 * d * Real.log L) hR U hU
    have hbase : 1 + 2 * d * Real.log L ≤ (1 + 2 * d) * (1 + Real.log L) := by
      nlinarith
    have hpow : (1 + 2 * d * Real.log L) ^ rank K ≤
        ((1 + 2 * d) * (1 + Real.log L)) ^ rank K :=
      pow_le_pow_left₀ (by positivity) hbase _
    calc
      ((T.filter (fun x => Associated x a)).card : ℝ) = (U.card : ℝ) := by rw [hUcard]
      _ ≤ C * (1 + 2 * d * Real.log L) ^ rank K := hc
      _ ≤ C * ((1 + 2 * d) * (1 + Real.log L)) ^ rank K :=
        mul_le_mul_of_nonneg_left hpow hC.le
      _ = (C * (1 + 2 * d) ^ rank K) * (1 + Real.log L) ^ rank K := by
        rw [mul_pow]
        ring
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_associated_box_count_constant

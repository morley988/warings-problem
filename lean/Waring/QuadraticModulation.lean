import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.Interval
import Waring.GeometricSums
import Mathlib.Tactic.Ring

/-!
# Removal of arbitrary real linear modulation by one difference

These are exact finite identities behind the uniform-in-modulation quadratic
estimate in the manuscript. They prove the disappearance of the linear phase
from the modulus of each fixed-shift correlation. The reciprocal-sum estimate
and the summation over shifts remain separate analytic obligations.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Waring.QuadraticModulation

/-- The additive exponential with the standard `2*pi*i` normalization. -/
def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp, Complex.mul_re]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem conj_e (x : ℝ) : conj (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem e_mul_conj (x y : ℝ) : e x * conj (e y) = e (x - y) := by
  rw [conj_e, ← e_add, sub_eq_add_neg]

/-- A linear modulation contributes only one unit-modulus factor to a fixed
shift correlation, for any underlying phase function. -/
theorem modulated_difference (g : ℤ → ℝ) (t : ℝ) (z u : ℤ) :
    e (g (z + u) + t * (z + u : ℤ)) * conj (e (g z + t * z)) =
      e (t * u) * e (g (z + u) - g z) := by
  rw [e_mul_conj, ← e_add]
  congr 1
  push_cast
  ring

/-- The common modulation factors out of the whole fixed-shift sum. No
restriction at all is imposed on the real value `t`. -/
theorem correlation_factor (s : Finset ℤ) (g : ℤ → ℝ) (t : ℝ) (u : ℤ) :
    (∑ z ∈ s, e (g (z + u) + t * (z + u : ℤ)) * conj (e (g z + t * z))) =
      e (t * u) * ∑ z ∈ s, e (g (z + u) - g z) := by
  simp_rw [modulated_difference]
  rw [Finset.mul_sum]

/-- The modulus of a fixed-shift correlation is exactly independent of an
arbitrary common real modulation. -/
theorem norm_correlation_independent (s : Finset ℤ) (g : ℤ → ℝ) (t : ℝ) (u : ℤ) :
    ‖∑ z ∈ s, e (g (z + u) + t * (z + u : ℤ)) * conj (e (g z + t * z))‖ =
      ‖∑ z ∈ s, e (g (z + u) - g z)‖ := by
  rw [correlation_factor, norm_mul, norm_e, one_mul]

/-- In the quadratic case, the remaining phase is linear in the summation
variable. This is the input to the geometric/reciprocal-sum estimate. -/
theorem quadratic_correlation (s : Finset ℤ) (β t : ℝ) (u : ℤ) :
    ‖∑ z ∈ s, e (β * (z + u : ℤ) ^ 2 + t * (z + u : ℤ)) *
      conj (e (β * (z : ℝ) ^ 2 + t * z))‖ =
      ‖∑ z ∈ s, e (2 * β * (u : ℝ) * z)‖ := by
  rw [norm_correlation_independent s (fun z => β * (z : ℝ) ^ 2) t u]
  have hphase (z : ℤ) :
      β * (z + u : ℤ) ^ 2 - β * (z : ℝ) ^ 2 =
        β * (u : ℝ) ^ 2 + 2 * β * (u : ℝ) * z := by
    push_cast
    ring
  simp_rw [hphase, e_add]
  rw [← Finset.mul_sum, norm_mul, norm_e, one_mul]

/-- The squared modulus of any finite complex sum expands as its pair sum. -/
theorem norm_sq_eq_pair_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ((‖∑ z ∈ s, f z‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ s ×ˢ s, f p.1 * conj (f p.2) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_product]

/-- The finite set of differences occurring in a summation set. -/
def differences (s : Finset ℤ) : Finset ℤ :=
  (s ×ˢ s).image (fun p => p.1 - p.2)

/-- The common domain of a sum and its translate by `u`. -/
def overlap (s : Finset ℤ) (u : ℤ) : Finset ℤ :=
  s.filter (fun z => z + u ∈ s)

theorem difference_fiber_sum (s : Finset ℤ) (f : ℤ → ℂ) (u : ℤ) :
    (∑ p ∈ (s ×ˢ s).filter (fun p => p.1 - p.2 = u), f p.1 * conj (f p.2)) =
      ∑ z ∈ overlap s u, f (z + u) * conj (f z) := by
  apply Finset.sum_bij (fun p _ => p.2)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hdiff⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    apply Finset.mem_filter.mpr
    exact ⟨hp2, by convert hp1 using 1; omega⟩
  · intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext
    · omega
    · exact heq
  · intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hz, hzu⟩
    refine ⟨(z + u, z), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzu, hz⟩, by simp⟩
  · intro p hp
    have hdiff := (Finset.mem_filter.mp hp).2
    have hp1 : p.1 = p.2 + u := by omega
    rw [hp1]

/-- Exact autocorrelation expansion, valid on every finite set of integers. -/
theorem norm_sq_eq_autocorrelations (s : Finset ℤ) (f : ℤ → ℂ) :
    ((‖∑ z ∈ s, f z‖ ^ 2 : ℝ) : ℂ) =
      ∑ u ∈ differences s, ∑ z ∈ overlap s u, f (z + u) * conj (f z) := by
  rw [norm_sq_eq_pair_sum]
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := s ×ˢ s) (t := differences s) (g := fun p => p.1 - p.2)
    (fun p hp => Finset.mem_image_of_mem (fun p => p.1 - p.2) hp)
    (fun p => f p.1 * conj (f p.2))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro u _hu
  exact difference_fiber_sum s f u

/-- A finite Weyl differencing bound before estimating the correlations. -/
theorem norm_sq_le_correlations (s : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ z ∈ s, f z‖ ^ 2 ≤
      ∑ u ∈ differences s, ‖∑ z ∈ overlap s u, f (z + u) * conj (f z)‖ := by
  calc
    ‖∑ z ∈ s, f z‖ ^ 2 = ‖((‖∑ z ∈ s, f z‖ ^ 2 : ℝ) : ℂ)‖ := by simp
    _ = ‖∑ u ∈ differences s, ∑ z ∈ overlap s u, f (z + u) * conj (f z)‖ :=
      congrArg norm (norm_sq_eq_autocorrelations s f)
    _ ≤ _ := norm_sum_le _ _

/-- The quadratic Weyl differencing bound is independent of every real
linear modulation `t`. Its remaining sums have linear phase `2*beta*u*z`. -/
theorem quadratic_norm_sq_le_linear_correlations (s : Finset ℤ) (β t : ℝ) :
    ‖∑ z ∈ s, e (β * (z : ℝ) ^ 2 + t * z)‖ ^ 2 ≤
      ∑ u ∈ differences s, ‖∑ z ∈ overlap s u, e (2 * β * (u : ℝ) * z)‖ := by
  have h := norm_sq_le_correlations s (fun z => e (β * (z : ℝ) ^ 2 + t * z))
  simpa only [quadratic_correlation] using h

/-- Intersecting an integer interval with its translate gives an interval. -/
theorem overlap_Icc (a b u : ℤ) :
    overlap (Finset.Icc a b) u =
      Finset.Icc (max a (a - u)) (min b (b - u)) := by
  ext z
  simp only [overlap, Finset.mem_filter, Finset.mem_Icc, max_le_iff, le_min_iff]
  omega

/-- The sharp total geometric-sum bound on an arbitrary integer interval. -/
theorem norm_linear_Icc_le (a b : ℤ) (α : ℝ) :
    ‖∑ z ∈ Finset.Icc a b, e (α * z)‖ ≤
      Waring.linearSumBound (b + 1 - a).toNat α := by
  have hid : (∑ z ∈ Finset.Icc a b, e (α * z)) =
      ∑ n ∈ Finset.range (b + 1 - a).toNat, e (α * ((n : ℝ) + a)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _hn
    congr 1
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    ring
  rw [hid]
  exact Waring.norm_exp_linear_sum_le a (b + 1 - a).toNat α

theorem linearSumBound_mono {M N : ℕ} (hMN : M ≤ N) (α : ℝ) :
    Waring.linearSumBound M α ≤ Waring.linearSumBound N α := by
  unfold Waring.linearSumBound
  split_ifs
  · exact_mod_cast hMN
  · exact min_le_min (by exact_mod_cast hMN) le_rfl

theorem linearSumBound_nonneg (N : ℕ) (α : ℝ) :
    0 ≤ Waring.linearSumBound N α := by
  unfold Waring.linearSumBound Waring.integerDistance
  split_ifs <;> positivity

/-- Full finite quadratic differencing estimate in reciprocal-distance form,
uniform for every real linear modulation and every integer interval.

The total bound uses the interval length at integral phases; it never invokes
Lean's zero-inverse convention as though it were an infinite reciprocal.
This is the finite analytic starting point of the manuscript's estimate Q1.
The height-dependent summation of these reciprocal terms is not asserted here.
-/
theorem quadratic_interval_reciprocal_bound (a b : ℤ) (β t : ℝ) :
    ‖∑ z ∈ Finset.Icc a b, e (β * (z : ℝ) ^ 2 + t * z)‖ ^ 2 ≤
      ∑ u ∈ Finset.Icc (a - b) (b - a),
        Waring.linearSumBound (b + 1 - a).toNat (2 * β * (u : ℝ)) := by
  have hsubset : differences (Finset.Icc a b) ⊆ Finset.Icc (a - b) (b - a) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    rcases Finset.mem_Icc.mp hp1 with ⟨ha1, hb1⟩
    rcases Finset.mem_Icc.mp hp2 with ⟨ha2, hb2⟩
    apply Finset.mem_Icc.mpr
    omega
  calc
    _ ≤ ∑ u ∈ differences (Finset.Icc a b),
        ‖∑ z ∈ overlap (Finset.Icc a b) u, e (2 * β * (u : ℝ) * z)‖ :=
      quadratic_norm_sq_le_linear_correlations _ β t
    _ ≤ ∑ u ∈ differences (Finset.Icc a b),
        Waring.linearSumBound (b + 1 - a).toNat (2 * β * (u : ℝ)) := by
      apply Finset.sum_le_sum
      intro u _hu
      have hcard : (overlap (Finset.Icc a b) u).card ≤ (b + 1 - a).toNat := by
        rw [← Int.card_Icc]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have hlinear :
          ‖∑ z ∈ overlap (Finset.Icc a b) u, e (2 * β * (u : ℝ) * z)‖ ≤
            Waring.linearSumBound (overlap (Finset.Icc a b) u).card
              (2 * β * (u : ℝ)) := by
        rw [overlap_Icc]
        simpa only [Int.card_Icc] using
          norm_linear_Icc_le (max a (a - u)) (min b (b - u)) (2 * β * (u : ℝ))
      exact hlinear.trans (linearSumBound_mono hcard _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun u _hu _hnot => linearSumBound_nonneg _ _)

#print axioms norm_correlation_independent
#print axioms quadratic_correlation
#print axioms norm_sq_eq_autocorrelations
#print axioms quadratic_norm_sq_le_linear_correlations
#print axioms quadratic_interval_reciprocal_bound

end Waring.QuadraticModulation

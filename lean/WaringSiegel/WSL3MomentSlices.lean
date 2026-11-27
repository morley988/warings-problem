import WaringSiegel.WSL3MomentKernelProjection
import WaringSiegel.WSL3MomentSystemEnergy

/-!
# Actual lower-coefficient moment slices

A slice is an actual Haar integral of an even Weyl moment. Its exact finite
Fourier expansion is proved, so positivity, kernel reproduction, and the
full-system energy bound can be joined without hypothetical orthogonality.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

def pairedTupleCoefficient (s : ℕ) (w : α → ℂ) (xy : (Fin s → α) × (Fin s → α)) : ℂ :=
  (∏ i, w (xy.1 i)) * conj (∏ i, w (xy.2 i))

theorem integral_norm_frequencySum_even_complex (v : α → ι → ℤ) (w : α → ℂ) (s : ℕ) :
    ((∫ θ, ‖frequencySum v w θ‖^(2*s) ∂latticeHaar : ℝ) : ℂ) =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if (∑ i, v (xy.1 i)) = (∑ i, v (xy.2 i)) then pairedTupleCoefficient s w xy else 0 := by
  calc
    _ = ∫ θ, frequencySum v w θ^s * conj (frequencySum v w θ^s) ∂latticeHaar := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with θ
      rw [Complex.mul_conj', norm_pow]
      push_cast
      rw [← pow_mul, Nat.mul_comm s]
    _ = _ := by
      simp_rw [frequencySum_pow]
      exact integral_frequencySum_mul_conj _ _ _ _

def sliceMoment (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ)
    (β : κ → AddCircle (1 : ℝ)) : ℝ :=
  ∫ θ, ‖frequencySum v (fun x => w x*latticeCharacter (u x) β) θ‖^(2*s) ∂latticeHaar

def sliceFrequency (s : ℕ) (u : α → κ → ℤ)
    (xy : (Fin s → α) × (Fin s → α)) : κ → ℤ :=
  (∑ i, u (xy.1 i)) - ∑ i, u (xy.2 i)

def sliceCoefficient (s : ℕ) (v : α → ι → ℤ) (w : α → ℂ)
    (xy : (Fin s → α) × (Fin s → α)) : ℂ :=
  if (∑ i, v (xy.1 i)) = (∑ i, v (xy.2 i)) then pairedTupleCoefficient s w xy else 0

theorem sliceMoment_complex (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ)
    (β : κ → AddCircle (1 : ℝ)) :
    (sliceMoment s v u w β : ℂ) =
      frequencySum (sliceFrequency s u) (sliceCoefficient s v w) β := by
  rw [sliceMoment, integral_norm_frequencySum_even_complex]
  unfold frequencySum
  apply Finset.sum_congr rfl
  intro xy hxy
  unfold sliceCoefficient
  split_ifs
  · simp only [pairedTupleCoefficient, Finset.prod_mul_distrib, map_mul,
      ← WaringSiegel.latticeCharacter_sum, sliceFrequency, latticeCharacter_sub]
    ring
  · simp

theorem sliceMoment_nonneg (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ)
    (β : κ → AddCircle (1 : ℝ)) : 0 ≤ sliceMoment s v u w β :=
  integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)

theorem sliceMoment_eq_re (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ)
    (β : κ → AddCircle (1 : ℝ)) :
    sliceMoment s v u w β = (frequencySum (sliceFrequency s u) (sliceCoefficient s v w) β).re := by
  simpa only [Complex.ofReal_re] using congrArg Complex.re (sliceMoment_complex s v u w β)

theorem sliceMoment_continuous (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ) :
    Continuous (sliceMoment s v u w) := by
  have h := Complex.continuous_re.comp
    (continuous_frequencySum (sliceFrequency s u) (sliceCoefficient s v w))
  exact h.congr (fun β => (sliceMoment_eq_re s v u w β).symm)

theorem sliceMoment_frequency_norm (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ)
    (β : κ → AddCircle (1 : ℝ)) :
    ‖frequencySum (sliceFrequency s u) (sliceCoefficient s v w) β‖ =
      (frequencySum (sliceFrequency s u) (sliceCoefficient s v w) β).re := by
  rw [← sliceMoment_complex, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re,
    abs_of_nonneg (sliceMoment_nonneg s v u w β)]

theorem sliceMoment_integral (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ) :
    (∫ β, sliceMoment s v u w β ∂latticeHaar) =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if (∑ i, v (xy.1 i)) = (∑ i, v (xy.2 i)) ∧
          (∑ i, u (xy.1 i)) = (∑ i, u (xy.2 i)) then (pairedTupleCoefficient s w xy).re else 0 := by
  have hc : ((∫ β, sliceMoment s v u w β ∂latticeHaar : ℝ) : ℂ) =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if (sliceFrequency s u xy)=0 then sliceCoefficient s v w xy else 0 := by
    rw [← integral_complex_ofReal]
    simp_rw [sliceMoment_complex]
    simpa only [frequencySum, sub_zero] using
      integral_weighted_lattice_sum Finset.univ (sliceCoefficient s v w) (sliceFrequency s u) 0
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re, Complex.zero_re,
    sliceFrequency, sub_eq_zero, sliceCoefficient] at hr
  apply hr.trans
  apply Finset.sum_congr rfl
  intro xy hxy
  by_cases hv : (∑ i, v (xy.1 i)) = (∑ i, v (xy.2 i))
  · by_cases hu : (∑ i, u (xy.1 i)) = (∑ i, u (xy.2 i))
    · simp only [if_pos hv, if_pos hu, and_self, if_pos (And.intro hv hu)]
    · simp only [if_pos hv, if_neg hu, if_neg (not_and_of_not_right _ hu)]
  · by_cases hu : (∑ i, u (xy.1 i)) = (∑ i, u (xy.2 i))
    · simp only [if_neg hv, if_pos hu, if_neg (not_and_of_not_left _ hv)]
    · simp only [if_neg hv, if_neg hu, if_neg (not_and_of_not_left _ hv)]

theorem sliceMoment_integral_le_energy {A : Type*} [AddCommMonoid A]
    (s : ℕ) (v : α → ι → ℤ) (u : α → κ → ℤ) (w : α → ℂ) (value : α → A)
    (heq : ∀ x y : Fin s → α,
      (∑ i, v (x i)) = (∑ i, v (y i)) → (∑ i, u (x i)) = (∑ i, u (y i)) →
      (∑ i, value (x i)) = (∑ i, value (y i))) :
    (∫ β, sliceMoment s v u w β ∂latticeHaar) ≤ weightedSystemEnergy s value (fun x => ‖w x‖) := by
  rw [sliceMoment_integral]
  unfold weightedSystemEnergy
  apply Finset.sum_le_sum
  intro xy hxy
  by_cases h : (∑ i, v (xy.1 i)) = (∑ i, v (xy.2 i)) ∧
      (∑ i, u (xy.1 i)) = (∑ i, u (xy.2 i))
  · rw [if_pos h, if_pos (heq xy.1 xy.2 h.1 h.2)]
    exact (Complex.re_le_norm _).trans_eq (by
      simp only [pairedTupleCoefficient, norm_mul, Complex.norm_conj, norm_prod])
  · rw [if_neg h]
    split_ifs
    · positivity
    · rfl

#print axioms sliceMoment_complex
#print axioms sliceMoment_integral_le_energy

end WaringSiegel.WSL3

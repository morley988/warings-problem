import WaringSiegel.WSL3MomentInsertion

/-!
# Exact frequency-kernel projection and finite shifted averaging

A kernel whose Fourier coefficient is one at each occurring frequency
reproduces the literal trigonometric polynomial. For a nonnegative real
polynomial, a uniform bound on the sum of translated kernel norms gives
its shifted average bound without a loss in the remaining moment.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {ι α β ζ : Type*} [Fintype ι] [Fintype α] [Fintype β] [Fintype ζ]

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

theorem latticeCharacter_argument_add (m : ι → ℤ) (θ η : ι → AddCircle (1 : ℝ)) :
    latticeCharacter m (θ+η) = latticeCharacter m θ * latticeCharacter m η := by
  unfold latticeCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  change (AddCircle.toCircle (m i • (θ i+η i)) : ℂ) =
    (AddCircle.toCircle (m i • θ i) : ℂ) * (AddCircle.toCircle (m i • η i) : ℂ)
  rw [smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem latticeCharacter_argument_neg (m : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter m (-θ) = conj (latticeCharacter m θ) := by
  have h (n : ℤ) (t : AddCircle (1 : ℝ)) : fourier n (-t) = conj (fourier n t) := by
    rw [fourier_apply, smul_neg, fourier_neg']
  simp only [latticeCharacter, Pi.neg_apply, h, map_prod]

theorem latticeCharacter_argument_sub (m : ι → ℤ) (θ η : ι → AddCircle (1 : ℝ)) :
    latticeCharacter m (θ-η) = latticeCharacter m θ * conj (latticeCharacter m η) := by
  rw [sub_eq_add_neg, latticeCharacter_argument_add, latticeCharacter_argument_neg]

def shiftedFrequencyKernel (u : β → ι → ℤ) (c : β → ℂ)
    (γ θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  frequencySum (fun b => -u b) (fun b => c b*latticeCharacter (u b) γ) θ

theorem shiftedFrequencyKernel_eq (u : β → ι → ℤ) (c : β → ℂ)
    (γ θ : ι → AddCircle (1 : ℝ)) :
    shiftedFrequencyKernel u c γ θ = frequencySum u c (γ-θ) := by
  simp only [shiftedFrequencyKernel, frequencySum, latticeCharacter_neg,
    latticeCharacter_argument_sub, mul_assoc]

theorem frequencySum_kernel_reproduces (v : α → ι → ℤ) (w : α → ℂ)
    (u : β → ι → ℤ) (c : β → ℂ)
    (hc : ∀ a, (∑ b, if v a=u b then c b else 0) = 1)
    (γ : ι → AddCircle (1 : ℝ)) :
    (∫ θ, frequencySum v w θ * shiftedFrequencyKernel u c γ θ ∂latticeHaar) =
      frequencySum v w γ := by
  have hk (θ : ι → AddCircle (1 : ℝ)) : shiftedFrequencyKernel u c γ θ =
      conj (frequencySum u (fun b => conj (c b*latticeCharacter (u b) γ)) θ) := by
    simp only [shiftedFrequencyKernel, frequencySum, map_sum, map_mul, starRingEnd_self_apply,
      latticeCharacter_neg]
  simp_rw [hk]
  rw [integral_frequencySum_mul_conj]
  simp only [Fintype.sum_prod_type, starRingEnd_self_apply]
  unfold frequencySum
  apply Finset.sum_congr rfl
  intro a ha
  calc
    _ = (w a*latticeCharacter (v a) γ) * ∑ b, if v a=u b then c b else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases he : v a=u b
      · simp only [he, ite_true]
        ring
      · simp only [if_neg he, mul_zero]
    _ = _ := by rw [hc, mul_one]

/-- The actual finite shifted-kernel estimate can now be used directly
against any nonnegative real trigonometric polynomial. -/
theorem frequencySum_shifted_kernel_average_le (v : α → ι → ℤ) (w : α → ℂ)
    (u : β → ι → ℤ) (c : β → ℂ)
    (hc : ∀ a, (∑ b, if v a=u b then c b else 0) = 1)
    (hreal : ∀ θ, ‖frequencySum v w θ‖ = (frequencySum v w θ).re)
    (γ : ζ → ι → AddCircle (1 : ℝ)) (C : ℝ)
    (hkernel : ∀ θ, (∑ z, ‖frequencySum u c (γ z-θ)‖) ≤ C) :
    (∑ z, (frequencySum v w (γ z)).re) ≤
      C * ∫ θ, (frequencySum v w θ).re ∂latticeHaar := by
  have hcontF := continuous_frequencySum v w
  have hcontK (z : ζ) : Continuous (fun θ => frequencySum u c (γ z-θ)) :=
    (continuous_frequencySum u c).comp (continuous_const.sub continuous_id)
  have hint (z : ζ) : Integrable
      (fun θ => (frequencySum v w θ).re * ‖frequencySum u c (γ z-θ)‖) latticeHaar :=
    ((Complex.continuous_re.comp hcontF).mul (hcontK z).norm).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz (z : ζ) : (frequencySum v w (γ z)).re ≤
      ∫ θ, (frequencySum v w θ).re * ‖frequencySum u c (γ z-θ)‖ ∂latticeHaar := by
    calc
      _ ≤ ‖frequencySum v w (γ z)‖ := Complex.re_le_norm _
      _ = ‖∫ θ, frequencySum v w θ * shiftedFrequencyKernel u c (γ z) θ ∂latticeHaar‖ :=
        congrArg norm (frequencySum_kernel_reproduces v w u c hc (γ z)).symm
      _ ≤ ∫ θ, ‖frequencySum v w θ * shiftedFrequencyKernel u c (γ z) θ‖ ∂latticeHaar :=
        norm_integral_le_integral_norm _
      _ = _ := by simp only [norm_mul, hreal, shiftedFrequencyKernel_eq]
  calc
    _ ≤ ∑ z, ∫ θ, (frequencySum v w θ).re * ‖frequencySum u c (γ z-θ)‖ ∂latticeHaar :=
      Finset.sum_le_sum (fun z hzmem => hz z)
    _ = ∫ θ, (frequencySum v w θ).re * ∑ z, ‖frequencySum u c (γ z-θ)‖ ∂latticeHaar := by
      rw [← integral_finset_sum _ (fun z _ => hint z)]
      simp only [Finset.mul_sum]
    _ ≤ ∫ θ, (frequencySum v w θ).re * C ∂latticeHaar := by
      apply integral_mono
      · exact ((Complex.continuous_re.comp hcontF).mul (continuous_finset_sum _ (fun z _ => (hcontK z).norm))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact ((Complex.continuous_re.comp hcontF).mul continuous_const).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro θ
        exact mul_le_mul_of_nonneg_left (hkernel θ) (by rw [← hreal]; exact norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

#print axioms frequencySum_kernel_reproduces
#print axioms frequencySum_shifted_kernel_average_le

end WaringSiegel.WSL3

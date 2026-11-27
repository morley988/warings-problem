import WaringSiegel.WSL2MomentFourier

/-!
# Weighted moment bounds from literal finite frequency fibers

The hypotheses below are finite cardinality bounds, not analytic estimates.
The next modules discharge them for actual algebraic power maps.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField

namespace WaringSiegel.WSL2

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- The actual fiber containing a specified index. -/
def frequencyFiber (v : α → ι → ℤ) (a : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun b => v a = v b)

/-- The actual number of equal-frequency ordered pairs. -/
def frequencyEnergy (v : α → ι → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : α × α => v p.1 = v p.2)).card

theorem twice_re_mul_conj_le (z w : ℂ) :
    2 * (z * conj w).re ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  have h := Complex.normSq_nonneg (z - w)
  rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  linarith

theorem sum_equal_frequency_left (v : α → ι → ℤ) (r : α → ℝ) :
    (∑ a, ∑ b, if v a = v b then r a else 0) =
      ∑ a, ((frequencyFiber v a).card : ℝ) * r a := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_filter]
  simp [frequencyFiber, nsmul_eq_mul]

theorem sum_equal_frequency_right (v : α → ι → ℤ) (r : α → ℝ) :
    (∑ a, ∑ b, if v a = v b then r b else 0) =
      ∑ a, ((frequencyFiber v a).card : ℝ) * r a := by
  classical
  rw [Finset.sum_comm]
  simpa only [eq_comm] using sum_equal_frequency_left v r

/-- A fiber-multiplicity bound implies the sharp weighted second-moment bound. -/
theorem integral_norm_frequencySum_sq_le (v : α → ι → ℤ) (w : α → ℂ)
    (M : ℕ) (hM : ∀ a, (frequencyFiber v a).card ≤ M) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 2 ∂latticeHaar) ≤ (M : ℝ) * ∑ a, ‖w a‖ ^ 2 := by
  classical
  let T : ℝ := ∑ a, ((frequencyFiber v a).card : ℝ) * ‖w a‖ ^ 2
  have hY : 2 * (∫ θ, ‖frequencySum v w θ‖ ^ 2 ∂latticeHaar) ≤ 2 * T := by
    rw [integral_norm_frequencySum_sq]
    simp only [Fintype.sum_prod_type]
    calc
      2 * (∑ a, ∑ b, if v a = v b then (w a * conj (w b)).re else 0) =
          ∑ a, ∑ b, 2 * (if v a = v b then (w a * conj (w b)).re else 0) := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ a, ∑ b, if v a = v b then ‖w a‖ ^ 2 + ‖w b‖ ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        by_cases h : v a = v b
        · simpa only [if_pos h] using twice_re_mul_conj_le (w a) (w b)
        · simp [h]
      _ = 2 * T := by
        simp only [ite_add_zero, Finset.sum_add_distrib]
        rw [sum_equal_frequency_left, sum_equal_frequency_right]
        dsimp [T]
        ring
  have hT : T ≤ (M : ℝ) * ∑ a, ‖w a‖ ^ 2 := by
    dsimp [T]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM a) (sq_nonneg _)
  linarith

/-- Bounded complex weights are dominated by the literal unweighted energy. -/
theorem integral_norm_frequencySum_sq_le_energy (v : α → ι → ℤ) (w : α → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 2 ∂latticeHaar) ≤
      (frequencyEnergy v : ℝ) * W ^ 2 := by
  classical
  rw [integral_norm_frequencySum_sq]
  calc
    (∑ p : α × α, if v p.1 = v p.2 then (w p.1 * conj (w p.2)).re else 0) ≤
        ∑ p : α × α, if v p.1 = v p.2 then W ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases h : v p.1 = v p.2
      · simp only [if_pos h]
        calc
          _ ≤ ‖w p.1 * conj (w p.2)‖ := Complex.re_le_norm _
          _ = ‖w p.1‖ * ‖w p.2‖ := by rw [norm_mul, Complex.norm_conj]
          _ ≤ W * W := mul_le_mul (hw _) (hw _) (norm_nonneg _) hW
          _ = W ^ 2 := (pow_two W).symm
      · simp [h]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [frequencyEnergy, nsmul_eq_mul]

/-- The fourth moment is bounded by the actual equal-difference energy. -/
theorem integral_norm_frequencySum_fourth_le_energy (v : α → ι → ℤ) (w : α → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 4 ∂latticeHaar) ≤
      (frequencyEnergy (fun p : α × α => v p.1 - v p.2) : ℝ) * W ^ 4 := by
  rw [integral_norm_frequencySum_fourth_difference]
  have h := integral_norm_frequencySum_sq_le_energy
    (fun p : α × α => v p.1 - v p.2) (fun p => w p.1 * conj (w p.2))
    (W ^ 2) (sq_nonneg W) (fun p => by
      rw [norm_mul, Complex.norm_conj, pow_two]
      exact mul_le_mul (hw _) (hw _) (norm_nonneg _) hW)
  convert h using 1 <;> ring

end WaringSiegel.WSL2

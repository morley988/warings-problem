import WaringSiegel.WSL2MomentBounds

/-!
# Weighted eighth moments are bounded by the literal unweighted eighth moment

The proof expands finite sums against actual Haar measure and uses character
orthogonality. It allows arbitrary complex weights and arbitrary repetitions
of frequencies; only the stated coefficient bound is needed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL2
variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- Unweighted second moment equals the actual equal-frequency count. -/
theorem integral_norm_frequencySum_sq_one (v : α → ι → ℤ) :
    (∫ θ, ‖frequencySum v (fun _ => 1) θ‖ ^ 2 ∂latticeHaar) =
      (frequencyEnergy v : ℝ) := by
  rw [integral_norm_frequencySum_sq]
  simp only [map_one, mul_one, Complex.one_re]
  rw [← Finset.sum_filter]
  simp [frequencyEnergy]

/-- Unweighted fourth moment equals the actual equal-difference count. -/
theorem integral_norm_frequencySum_fourth_one (v : α → ι → ℤ) :
    (∫ θ, ‖frequencySum v (fun _ => 1) θ‖ ^ 4 ∂latticeHaar) =
      (frequencyEnergy (fun p : α × α => v p.1 - v p.2) : ℝ) := by
  rw [integral_norm_frequencySum_fourth_difference]
  simp only [map_one, mul_one]
  exact integral_norm_frequencySum_sq_one _

theorem integral_norm_frequencySum_fourth_le_unweighted (v : α → ι → ℤ) (w : α → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 4 ∂latticeHaar) ≤
      W ^ 4 * (∫ θ, ‖frequencySum v (fun _ => 1) θ‖ ^ 4 ∂latticeHaar) := by
  rw [integral_norm_frequencySum_fourth_one, mul_comm]
  exact integral_norm_frequencySum_fourth_le_energy v w W hW hw

/-- Exact frequency squaring turns the eighth moment into a fourth moment. -/
theorem integral_norm_frequencySum_eighth_pair (v : α → ι → ℤ) (w : α → ℂ) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 8 ∂latticeHaar) =
      ∫ θ, ‖frequencySum (fun p : α × α => v p.1 + v p.2)
        (fun p => w p.1 * w p.2) θ‖ ^ 4 ∂latticeHaar := by
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [← frequencySum_sq, norm_pow]
  ring

/-- Arbitrary bounded complex coefficients cost at most their eighth power
in the actual eighth Haar moment. -/
theorem integral_norm_frequencySum_eighth_le_unweighted (v : α → ι → ℤ) (w : α → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 8 ∂latticeHaar) ≤
      W ^ 8 * (∫ θ, ‖frequencySum v (fun _ => 1) θ‖ ^ 8 ∂latticeHaar) := by
  rw [integral_norm_frequencySum_eighth_pair, integral_norm_frequencySum_eighth_pair]
  simp only [mul_one]
  have h := integral_norm_frequencySum_fourth_le_unweighted
    (fun p : α × α => v p.1 + v p.2) (fun p => w p.1 * w p.2) (W ^ 2) (sq_nonneg W) (by
      intro p
      rw [norm_mul, pow_two]
      exact mul_le_mul (hw _) (hw _) (norm_nonneg _) hW)
  convert h using 1 <;> ring

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.integral_norm_frequencySum_eighth_le_unweighted

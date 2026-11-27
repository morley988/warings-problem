import WaringSiegel.WSL2LocalFiniteFourier
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # WSL3: exact complex Gauss-sum norms for finite-field cubic estimates -/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]

theorem complex_gaussSum_conj (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    conj (gaussSum χ ψ) = gaussSum χ⁻¹ ψ⁻¹ := by
  simp only [gaussSum, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro x _
  change star (χ x) * conj (ψ x) = χ⁻¹ x * ψ⁻¹ x
  rw [MulChar.star_apply', ← AddChar.inv_apply_eq_conj, AddChar.inv_apply']

theorem complex_gaussSum_norm_sq (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← complex_gaussSum_conj χ ψ] at h
  rw [Complex.mul_conj'] at h
  exact_mod_cast h

theorem complex_gaussSum_norm (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  rw [← complex_gaussSum_norm_sq χ hχ ψ hψ, Real.sqrt_sq (norm_nonneg _)]

end WaringSiegel

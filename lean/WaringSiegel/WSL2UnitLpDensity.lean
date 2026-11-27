import WaringSiegel.WSL2UnitBoundedDensity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual L¹, L² and L∞ control of the archimedean density

The bounded-density theorem and finite total mass prove square integrability
without an assumed Fourier or oscillatory-integral estimate.
-/

noncomputable section
open MeasureTheory
open scoped NumberField Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- The genuine real-valued density is essentially bounded. -/
theorem archimedeanWaringDensity_memLp_top (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    MemLp (fun x : mixedSpace K => (archimedeanWaringDensity k s ρ R x).toReal) ⊤ := by
  obtain ⟨C, -, hC⟩ := exists_archimedeanWaringDensity_upper (K := K) k s hk ρ R hρ
  apply memLp_top_of_bound (archimedeanWaringDensity_measurable k s ρ R).ennreal_toReal.aestronglyMeasurable C
  filter_upwards [hC] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hx

/-- Finite mass and the actual essential bound imply an integrable square. -/
theorem archimedeanWaringDensity_square_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Integrable (fun x : mixedSpace K => (archimedeanWaringDensity k s ρ R x).toReal ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_archimedeanWaringDensity_upper (K := K) k s hk ρ R hρ
  have hfm := (archimedeanWaringDensity_measurable (K := K) k s ρ R).ennreal_toReal
  apply ((archimedeanWaringDensity_integrable (K := K) k s ρ R).const_mul C).mono'
    (hfm.pow_const 2).aestronglyMeasurable
  filter_upwards [hC] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right hx ENNReal.toReal_nonneg

/-- The actual density lies in L². A Plancherel or Fourier-integrability
bridge would be a further theorem, not part of this statement. -/
theorem archimedeanWaringDensity_memLp_two (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    MemLp (fun x : mixedSpace K => (archimedeanWaringDensity k s ρ R x).toReal) 2 :=
  (memLp_two_iff_integrable_sq
    (archimedeanWaringDensity_measurable k s ρ R).ennreal_toReal.aestronglyMeasurable).mpr
      (archimedeanWaringDensity_square_integrable k s hk ρ R hρ)

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.archimedeanWaringDensity_memLp_top
#print axioms WaringSiegel.WSL2.archimedeanWaringDensity_memLp_two

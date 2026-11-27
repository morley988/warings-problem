import WaringSiegel.WSL4MajorAuxiliaryPhase
import WaringSiegel.WSL4AuxiliaryProductSeries

/-! # The actual finite auxiliary main term and its full singular series -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryMajorMainIntegral_eq_productMajorSeries
    (ρ R L : ℝ) (p : ℕ) (hp : p≠0) (target : 𝓞 K) (htarget : target≠0) :
    auxiliaryMajorMainIntegral ρ R (rootScale 3 target) L p hp target =
      (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
        auxiliaryProductMajorSeries ρ R L (p:𝓞 K) (Nat.cast_ne_zero.mpr hp)
          target (normalizedTarget 3 1 target) := by
  rw [auxiliaryMajorMainIntegral_rootScale_formula ρ R L p hp target htarget]
  congr 1
  simp only [auxiliaryProductMajorSeries,productCenterSeries,rationalCentersUpTo,Finset.sum_map,
    boundedCenterAsRational_conductor]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fieldRationalCenter_representative]
  simp only [Function.Embedding.coeFn_mk,boundedCenterAsRational_conductor]

theorem auxiliaryMajorMainIntegral_full_series_error
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
      ∀ (p : ℕ) (hp : p.Prime), 173≤p → ∀ L : ℝ, 1≤L →
      ‖auxiliaryMajorMainIntegral ρ R (rootScale 3 target) L p hp.ne_zero target-
        (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
          (auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
              (smoothRootWeight ρ R) (normalizedTarget 3 1 target))‖ ≤
        auxiliaryMajorScale (K := K) (rootScale 3 target) p*C*(p:ℝ)^(2*finrank ℚ K)/L^(5/4:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := auxiliaryProductMajorSeries_truncation (K := K) ρ R hρ hR
  refine ⟨C,hC,?_⟩
  intro target htarget p hp hp173 L hL
  have hz := auxiliaryMajorScale_pos (K := K) _ (rootScale_pos htarget 3) p hp.pos
  rw [auxiliaryMajorMainIntegral_eq_productMajorSeries ρ R L p hp.ne_zero target htarget,
    ← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]
  exact (mul_le_mul_of_nonneg_left
    (hbound p hp hp173 target L hL (normalizedTarget 3 1 target)) hz.le).trans_eq (by ring)

#print axioms auxiliaryMajorMainIntegral_eq_productMajorSeries
#print axioms auxiliaryMajorMainIntegral_full_series_error
end WaringSiegel.WSL4

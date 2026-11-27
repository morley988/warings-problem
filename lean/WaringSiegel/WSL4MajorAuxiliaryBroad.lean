import WaringSiegel.WSL4MajorAuxiliaryAssembly
import WaringSiegel.WSL4MajorAuxiliaryPruning

/-! # Full actual auxiliary broad-major approximation -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem broadAuxiliaryCoefficient_full_main_error
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (C0 : ℝ) (hC0 : 1≤C0) (N : ℕ) :
    ∃ C₁ C₂ C₃ : ℝ, 0<C₁ ∧ 0<C₂ ∧ 0<C₃ ∧
      ∀ (target : 𝓞 K) (htarget : target≠0) (p : ℕ) (hp : p.Prime), 173≤p →
      1≤rootScale 3 target/(p:ℝ) →
      ∀ L : ℝ, 1≤L → (p:ℝ)^finrank ℚ K*L≤(rootScale 3 target)^finrank ℚ K →
      (2:ℝ)^finrank ℚ K*(C0*(rootScale 3 target)^finrank ℚ K)^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*((rootScale 3 target)^3)^finrank ℚ K →
      ‖auxiliaryMajorCoefficient ρ R hρ hR (rootScale 3 target) (rootScale_pos htarget 3)
          p hp.pos (C0*(rootScale 3 target)^finrank ℚ K) target-
        (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
          (auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
              (smoothRootWeight ρ R) (normalizedTarget 3 1 target))‖ ≤
        C₁*((rootScale 3 target)^finrank ℚ K)^4*
          ((rootScale 3 target/(p:ℝ))^finrank ℚ K)^4*
          ((p:ℝ)^finrank ℚ K*L/(rootScale 3 target)^finrank ℚ K)^N +
        auxiliaryMajorScale (K := K) (rootScale 3 target) p*C₂*(p:ℝ)^(2*finrank ℚ K)/L^(5/4:ℝ) +
        C₃*((rootScale 3 target)^finrank ℚ K)^5*
          (1/L^((5:ℝ)/4)+((p:ℝ)^finrank ℚ K)^8/
            ((rootScale 3 target)^finrank ℚ K)^((5:ℝ)/4)) := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hnarrow⟩ := narrowAuxiliaryCoefficient_full_main_error (K := K) ρ R hρ hR N
  obtain ⟨C₃,hC₃,hprune⟩ := auxiliaryMajorCoefficient_sub_narrow_bound (K := K) ρ R hρ hR C0 hC0
  refine ⟨C₁,C₂,C₃,hC₁,hC₂,hC₃,?_⟩
  intro target htarget p hp hp173 hPp L hL hYL hsep
  let P := rootScale 3 target
  let X := P^finrank ℚ K
  have hP : 0<P := rootScale_pos htarget 3
  have hX : 0<X := pow_pos hP _
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hY1 : 1≤(p:ℝ)^finrank ℚ K := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  have hLX : L≤X := (le_mul_of_one_le_left hL0.le hY1).trans hYL
  have hLM : L≤C0*X := hLX.trans (le_mul_of_one_le_left hX.le hC0)
  have hsepN : (2:ℝ)^finrank ℚ K*L^2<
      (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^3)^finrank ℚ K :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hLM 2)
      (by positivity)) hsep
  have h1 := hnarrow target htarget p hp hp173 hPp L hL hYL hsepN
  have h2 := hprune P hP p hp (by omega) L hL0 hLM hsep target
  let A := auxiliaryMajorCoefficient ρ R hρ hR P hP p hp.pos (C0*X) target
  let B := auxiliaryMajorCoefficient ρ R hρ hR P hP p hp.pos L target
  let T := (auxiliaryMajorScale (K := K) P p:ℂ) *
    (auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
      pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
        (smoothRootWeight ρ R) (normalizedTarget 3 1 target))
  change ‖A-T‖≤_
  calc
    _ = ‖(B-T)+(A-B)‖ := by congr 1; ring
    _ ≤ ‖B-T‖+‖A-B‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2

#print axioms broadAuxiliaryCoefficient_full_main_error
end WaringSiegel.WSL4

import WaringSiegel.WSL4MajorAuxiliaryReplacement
import WaringSiegel.WSL4MajorAuxiliarySeries

/-! # Literal auxiliary narrow coefficient versus its full series and integral -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem narrowAuxiliaryCoefficient_full_main_error
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧
      ∀ (target : 𝓞 K) (htarget : target≠0) (p : ℕ) (hp : p.Prime), 173≤p →
      1≤rootScale 3 target/(p:ℝ) →
      ∀ L : ℝ, 1≤L → (p:ℝ)^finrank ℚ K*L≤(rootScale 3 target)^finrank ℚ K →
      (2:ℝ)^finrank ℚ K*L^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*((rootScale 3 target)^3)^finrank ℚ K →
      ‖auxiliaryMajorCoefficient ρ R hρ hR (rootScale 3 target) (rootScale_pos htarget 3)
          p hp.pos L target-
        (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
          (auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
              (smoothRootWeight ρ R) (normalizedTarget 3 1 target))‖ ≤
        C₁*((rootScale 3 target)^finrank ℚ K)^4*
          ((rootScale 3 target/(p:ℝ))^finrank ℚ K)^4*
          ((p:ℝ)^finrank ℚ K*L/(rootScale 3 target)^finrank ℚ K)^N +
        auxiliaryMajorScale (K := K) (rootScale 3 target) p*C₂*(p:ℝ)^(2*finrank ℚ K)/L^(5/4:ℝ) := by
  obtain ⟨C₁,hC₁,hreplace⟩ := auxiliaryMajor_poisson_replacement (K := K) ρ R hρ hR N
  obtain ⟨C₂,hC₂,hseries⟩ := auxiliaryProductMajorSeries_truncation (K := K) ρ R hρ hR
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro target htarget p hp hp173 hPp L hL hYL hsep
  have hP := rootScale_pos htarget 3
  have hscale := auxiliaryMajorScale_pos (K := K) _ hP p hp.pos
  have h1 := hreplace (rootScale 3 target) hP p hp.pos hPp L
    (le_trans zero_le_one hL) hYL hsep target
  have h2 := hseries p hp hp173 target L hL (normalizedTarget 3 1 target)
  let A := auxiliaryMajorCoefficient ρ R hρ hR (rootScale 3 target) hP p hp.pos L target
  let M := auxiliaryMajorMainIntegral ρ R (rootScale 3 target) L p hp.ne_zero target
  let S := auxiliaryProductMajorSeries ρ R L (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero)
    target (normalizedTarget 3 1 target)
  let T := auxiliaryCubicSingularSeries (p:𝓞 K) (Nat.cast_ne_zero.mpr hp.ne_zero) target *
    pairedWeightedSingularIntegral (integerLatticeSourceScale K) 3 8
      (smoothRootWeight ρ R) (normalizedTarget 3 1 target)
  let z : ℝ := auxiliaryMajorScale (K := K) (rootScale 3 target) p
  have hM : M=(z:ℂ)*S :=
    auxiliaryMajorMainIntegral_eq_productMajorSeries ρ R L p hp.ne_zero target htarget
  have he : A-(z:ℂ)*T=(A-M)+(z:ℂ)*(S-T) := by rw [hM]; ring
  change ‖A-(z:ℂ)*T‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add h1
  rw [norm_mul]
  have hz : ‖(z:ℂ)‖=z := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
  rw [hz]
  exact (mul_le_mul_of_nonneg_left h2 hscale.le).trans_eq (by ring)

#print axioms narrowAuxiliaryCoefficient_full_main_error
end WaringSiegel.WSL4

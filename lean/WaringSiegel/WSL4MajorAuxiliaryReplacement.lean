import WaringSiegel.WSL4MajorAuxiliaryPhase
import WaringSiegel.WSL4MajorAuxiliaryCoefficient
import WaringSiegel.WSL4ArchAuxiliaryTelescope
import WaringSiegel.WSL4MajorMass
import WaringSiegel.WSL3UnitFrequencyTails

/-! # Actual integrated auxiliary Poisson replacement, uniform in the prime -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliary_root_main_product_continuous (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (γ : K) (p : ℕ) (hp : p≠0) :
    Continuous (fun β : mixedSpace K =>
      (auxiliaryRootMaskedMain ρ R P γ p hp β)^4*(auxiliaryRootScaledMain ρ R P γ p β)^4) := by
  have hj : Continuous (fun β : mixedSpace K =>
      pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight ρ R) β) := by
    simp_rw [pairedWeightedRootIntegral_eq _ (integerLatticeSourceScale_pos (K := K)).le]
    exact continuous_const.smul (weightedRootIntegral_continuous 3 ρ R hρ hR)
  simp_rw [auxiliary_root_main_product]
  exact continuous_const.mul ((hj.comp (continuous_const.smul continuous_id)).pow 8)

theorem auxiliaryMajor_poisson_replacement
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p),
      1≤P/(p:ℝ) → ∀ L : ℝ, 0≤L → (p:ℝ)^finrank ℚ K*L≤P^finrank ℚ K →
      (2:ℝ)^finrank ℚ K*L^2<
        (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*(P^3)^finrank ℚ K →
      ∀ target : 𝓞 K,
      ‖auxiliaryMajorCoefficient ρ R hρ hR P hP p hp L target-
        auxiliaryMajorMainIntegral ρ R P L p (Nat.ne_of_gt hp) target‖ ≤
        C*(P^finrank ℚ K)^4*((P/(p:ℝ))^finrank ℚ K)^4*
          ((p:ℝ)^finrank ℚ K*L/P^finrank ℚ K)^N := by
  obtain ⟨C,hC,herror⟩ := auxiliary_root_eightfold_main_error (K := K) ρ R hρ hR N
  refine ⟨C,hC,?_⟩
  intro P hP p hp hsmall L hL hYL hsep target
  have hX : 0<P^finrank ℚ K := pow_pos hP _
  have hY : 0≤(p:ℝ)^finrank ℚ K := pow_nonneg (Nat.cast_nonneg _) _
  have hratio : (p:ℝ)^finrank ℚ K*L/P^finrank ℚ K≤1 := (div_le_one hX).mpr hYL
  unfold auxiliaryMajorCoefficient auxiliaryMajorMainIntegral
  apply centeredArcIntegral_error_le (P^3) L (pow_pos hP 3) hL hsep _
    (auxiliaryTraceIntegrand_continuous ρ R hρ hR P hP p hp target)
  · intro q
    exact (auxiliary_root_main_product_continuous ρ R hρ hR P
      (traceCenterRepresentative q) p (Nat.ne_of_gt hp)).mul
      ((traceTorusCharacter_continuous (-target)).comp
        (continuous_quotient_mk'.comp (continuous_const.add continuous_id)))
  · positivity
  · intro q β hβ
    have har : auxiliaryRootArcRatio P p (traceCenterRepresentative q) β≤
        (p:ℝ)^finrank ℚ K*L/P^finrank ℚ K := by
      have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hY) hX.le
      simpa only [auxiliaryRootArcRatio,powerArcRatio,mul_div_assoc,mul_assoc] using hh
    have he := herror (traceCenterRepresentative q) p hp P hP hsmall β (har.trans hratio)
    change ‖auxiliaryTraceProduct ρ R hρ hR P hP p hp
        (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β)) *
          traceTorusCharacter (-target)
            (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))-
        _ * traceTorusCharacter (-target)
            (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))‖≤_
    rw [← sub_mul,norm_mul]
    simp only [traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]
    exact he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (auxiliaryRootArcRatio_nonneg P hP p _ β) har N) (by positivity))

#print axioms auxiliaryMajor_poisson_replacement
end WaringSiegel.WSL4

import WaringSiegel.WSL3IdealPoissonPowerArcApproximation
import WaringSiegel.WSL3IdealPoissonAuxiliaryNormalization

/-! # Arbitrary-order actual residue-weighted Poisson approximation in arc coordinates -/
noncomputable section
set_option maxHeartbeats 1300000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem idealResidueWeight_mass_le_norm (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)]
    (F : (𝓞 K ⧸ I) → ℂ) (hF : ∀q,‖F q‖≤1) :
    (∑q,‖F q‖)≤(I.absNorm:ℝ) := by
  calc
    _ ≤ ∑ _q : 𝓞 K ⧸ I,(1:ℝ) := Finset.sum_le_sum (fun q _ => hF q)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      ideal_quotient_card_eq_absNorm]

theorem smoothPower_residue_main_error_arcWeight (k : ℕ) (rho R : ℝ)
    (hrho : 0<rho) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I≠0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ), (∀q,‖F q‖≤1) →
      ∀ (P : ℝ), 0<P → ∀ θ : mixedSpace K,
      ‖(∑' x : 𝓞 K,F (Ideal.Quotient.mk I x)*
          (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
            archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))) -
        (P^finrank ℚ K/((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
          (idealCompleteTraceFactor I F 0*weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))‖ ≤
        C*P^finrank ℚ K*(powerArcRatio k P θ I)^N*(1+powerArcRatio k P θ I) := by
  obtain ⟨C,hC,hb⟩ := smoothPower_residue_main_error (K:=K) k rho R hrho hR N
  let D := 1+powerRadiusConstant k K R
  have hD : 1≤D := by dsimp [D]; linarith [powerRadiusConstant_nonneg (K:=K) k R]
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨C*D^(N+1),by positivity,fun I hI inst F hF P hP θ => ?_⟩
  let a := powerArcRatio k P θ I
  let b := powerDualVolumeRatio k R P θ I
  have ha : 0≤a := powerArcRatio_nonneg k P hP θ I
  have hb0 : 0≤b := powerDualVolumeRatio_nonneg k R P hP θ I hI
  have hN : 0<(I.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI)
  have hmass : (∑q,‖F q‖)/(I.absNorm:ℝ)≤1 :=
    (div_le_one hN).mpr (idealResidueWeight_mass_le_norm I F hF)
  have hba : b≤D*a := by
    apply (powerDualVolumeRatio_le_arcRatio k R P hP θ I).trans
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ha
  have hadd : 1+b≤D*(1+a) := by nlinarith only [hba,hD]
  have hprod := mul_le_mul (pow_le_pow_left₀ hb0 hba N) hadd (by linarith : 0≤1+b)
    (pow_nonneg (mul_nonneg hDp.le ha) N)
  calc
    _ ≤ C*((∑q,‖F q‖)/(I.absNorm:ℝ))*P^finrank ℚ K*b^N*(1+b) := hb I hI F P hP θ
    _ ≤ C*P^finrank ℚ K*b^N*(1+b) := by
      have hh := mul_le_mul_of_nonneg_left hmass
        (show 0≤C*P^finrank ℚ K*b^N*(1+b) by positivity)
      convert hh using 1 <;> ring
    _ ≤ (C*P^finrank ℚ K)*((D*a)^N*(D*(1+a))) := by
      have hh := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le (pow_nonneg hP.le (finrank ℚ K)))
      simpa only [mul_assoc] using hh
    _ = _ := by rw [mul_pow,pow_succ]; dsimp only [a]; ring

#print axioms idealResidueWeight_mass_le_norm
#print axioms smoothPower_residue_main_error_arcWeight
end WaringSiegel.WSL4

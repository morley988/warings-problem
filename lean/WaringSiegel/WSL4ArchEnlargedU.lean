import WaringSiegel.WSL4ArchArcWeights
import WaringSiegel.WSL4ArchFourthArc
import WaringSiegel.WSL4KappaIdealShift

/-! # Actual mixed cubic U-sum at the fixed multiplier four

The unrestricted two-term bound is uniform in the mixed-scale enlargement.
The finite twisted complete-sum premise is the exact arithmetic interface.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem four_smul_mixed (θ : mixedSpace K) : (4:ℝ) • θ = (4:mixedSpace K)*θ := by
  simpa only [Nat.cast_ofNat,nsmul_eq_mul] using Nat.cast_smul_eq_nsmul ℝ 4 θ

theorem nearZeroTraceCubicSum_four_center_bound
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 < B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (P : ℝ) (hP : 0 < P) (β : mixedSpace K),
      ‖nearZeroTraceCubicSum P hP.ne'
        (traceTorusMul 4 (Submodule.Quotient.mk (mixedEmbedding K γ+β)))‖ ≤
        C*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩*
          (P^finrank ℚ K*(productArcWeight (P^3) β)^(-(1/3):ℝ)+
            ((traceConductor γ).absNorm:ℝ)*(productArcWeight (P^3) β)^((2/3):ℝ)) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubic_center_two_term_bound (K:=K)
  obtain ⟨D,hD,hd⟩ := cubicKappa_four_mul_bound B hB
  let E := ((4:ℝ)^finrank ℚ K)^((2:ℝ)/3)
  have hE : 1 ≤ E := Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by norm_num)
  refine ⟨C*D*E,by positivity,fun γ P hP β => ?_⟩
  let κ := cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩
  let κ4 := cubicKappa B ⟨traceConductor (4*γ),traceConductor_ne_zero (4*γ)⟩
  let Q : ℝ := (traceConductor γ).absNorm
  let Q4 : ℝ := (traceConductor (4*γ)).absNorm
  let A := productArcWeight (P^3) β
  let A4 := productArcWeight (P^3) ((4:ℝ) • β)
  have hA : 0 < A := productArcWeight_pos _ _
  have hA4 : 0 < A4 := productArcWeight_pos _ _
  have hκ : 0 ≤ κ := cubicKappa_nonneg B (fun v => (hB v).le) _
  have hκ4 : 0 ≤ κ4 := cubicKappa_nonneg B (fun v => (hB v).le) _
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hQ4 : 0 ≤ Q4 := Nat.cast_nonneg _
  have hW : 0 ≤ P^finrank ℚ K := pow_nonneg hP.le _
  have hQA : Q4 ≤ Q := by
    have hh : (traceConductor (4*γ)).absNorm ≤ (traceConductor γ).absNorm := by
      simpa only [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat] using
        traceConductor_integral_mul_norm_le (4:𝓞 K) γ
    dsimp only [Q4,Q]
    exact_mod_cast hh
  have hκA : κ4 ≤ D*κ := hd γ
  have hAA : A ≤ A4 := productArcWeight_le_smul_fixed _ (4:ℝ) (pow_nonneg hP.le _) (by norm_num) _
  have hAB : A4 ≤ (4:ℝ)^finrank ℚ K*A := productArcWeight_smul_fixed _ (4:ℝ) (by norm_num) _
  have hfirst : P^finrank ℚ K*A4^(-(1/3):ℝ) ≤ E*(P^finrank ℚ K*A^(-(1/3):ℝ)) := by
    apply (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hA hAA (by norm_num)) hW).trans
    exact le_mul_of_one_le_left (mul_nonneg hW (Real.rpow_nonneg hA.le _)) hE
  have hsecond : Q4*A4^((2:ℝ)/3) ≤ E*(Q*A^((2:ℝ)/3)) := by
    apply (mul_le_mul hQA (Real.rpow_le_rpow hA4.le hAB (by norm_num))
      (Real.rpow_nonneg hA4.le _) hQ).trans_eq
    rw [Real.mul_rpow (pow_nonneg (by norm_num : (0:ℝ)≤4) _) hA.le]
    dsimp only [E]
    ring
  have hsum : P^finrank ℚ K*A4^(-(1/3):ℝ)+Q4*A4^((2:ℝ)/3) ≤
      E*(P^finrank ℚ K*A^(-(1/3):ℝ)+Q*A^((2:ℝ)/3)) := by
    exact (add_le_add hfirst hsecond).trans_eq (by ring)
  have h0 := hb (4*γ) κ4 hκ4 (hfinite (4*γ)) P hP ((4:ℝ) • β)
  have he : traceTorusMul (4:𝓞 K) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      Submodule.Quotient.mk (mixedEmbedding K (4*γ)+(4:ℝ) • β) := by
    rw [traceTorusMul_mk]
    have h4 : mixedEmbedding K (((4:𝓞 K):K)) = (4:mixedSpace K) := by
      simp only [NumberField.RingOfIntegers.coe_eq_algebraMap,map_ofNat]
    rw [h4,map_mul,map_ofNat,four_smul_mixed]
    congr 1
    ring
  rw [he,nearZeroTraceCubicSum_mk]
  apply h0.trans
  have hbig := mul_le_mul (mul_le_mul_of_nonneg_left hκA hC.le) hsum
    (add_nonneg (mul_nonneg hW (Real.rpow_nonneg hA4.le _))
      (mul_nonneg hQ4 (Real.rpow_nonneg hA4.le _)))
    (mul_nonneg hC.le (mul_nonneg hD.le hκ))
  exact hbig.trans_eq (by dsimp only [κ,A,Q]; ring)

#print axioms nearZeroTraceCubicSum_four_center_bound
end WaringSiegel.WSL4

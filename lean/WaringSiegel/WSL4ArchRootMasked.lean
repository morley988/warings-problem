import WaringSiegel.WSL4ArchRootPacking
import WaringSiegel.WSL3IdealPoissonAuxiliary
import WaringSiegel.WSL4CoprimeCubicWeyl

/-! # The actual prime-masked root source with its unrestricted packing factor -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def fieldCenterCubicCharacter (γ : K) : CubicConductorCharacter K :=
  ⟨⟨traceConductor γ,traceConductor_ne_zero γ⟩,⟨fieldCenterResidueChar γ,by
    rw [fieldCenterResidueChar,traceIdealAddChar_conductor]
    exact traceFrequencyAddChar_idealConductor γ⟩⟩

theorem auxiliaryCommonModulus_nat_norm_le (I : Ideal (𝓞 K)) (hI : I≠0)
    (p : ℕ) (hp : p≠0) :
    (auxiliaryCommonModulus I (p:𝓞 K)).absNorm ≤ I.absNorm*p^finrank ℚ K := by
  have hpO : (p:𝓞 K)≠0 := Nat.cast_ne_zero.mpr hp
  have hP : Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))≠0 := mt Ideal.span_singleton_eq_bot.mp hpO
  have hprod : I*Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))≠0 := mul_ne_zero hI hP
  have hN : 0<(I*Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))).absNorm :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hprod)
  have hh := Nat.le_of_dvd hN (Ideal.absNorm_dvd_absNorm_of_le
    (show I*Ideal.span ({(p:𝓞 K)} : Set (𝓞 K))≤auxiliaryCommonModulus I (p:𝓞 K) from Ideal.mul_le_inf))
  simpa only [map_mul,ideal_absNorm_span_nat] using hh

theorem smoothRootCubic_masked_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (γ : K) (p : ℕ) (hp : p≠0) (κ : ℝ), 0≤κ →
      (∀ ξ : (inverseDifferent K*(auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K) :
          FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖auxiliaryMaskedTwistedComplete (fieldCenterCubicCharacter γ) (p:𝓞 K)
          (Nat.cast_ne_zero.mpr hp) (mixedEmbedding K (ξ:K))‖ ≤
            ((auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)).absNorm:ℝ)*κ) →
      ∀ P : ℝ, 0<P → ∀ β : mixedSpace K,
      ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
        (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0‖ ≤
        C*κ*P^finrank ℚ K*(productArcWeight (P^3) β)^(-(1/2):ℝ)*
          (1+(p:ℝ)^finrank ℚ K*((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) β/P^finrank ℚ K) := by
  obtain ⟨C,hC,hb⟩ := smoothRootCubic_residue_arc_packing_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun γ p hp κ hκ hfinite P hP β => ?_⟩
  let M := auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)
  have hM : M≠0 := auxiliaryCommonModulus_ne_zero _ (traceConductor_ne_zero γ) _ (Nat.cast_ne_zero.mpr hp)
  letI := idealResidueFintype M hM
  have hMN : 0<(M.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hM)
  have hMNbound : (M.absNorm:ℝ) ≤ (p:ℝ)^finrank ℚ K*((traceConductor γ).absNorm:ℝ) := by
    have hh := auxiliaryCommonModulus_nat_norm_le (traceConductor γ) (traceConductor_ne_zero γ) p hp
    have hh' : (M.absNorm:ℝ) ≤ ((traceConductor γ).absNorm:ℝ)*(p:ℝ)^finrank ℚ K := by
      dsimp only [M]
      exact_mod_cast hh
    exact hh'.trans_eq (mul_comm _ _)
  have hh := hb M hM (auxiliaryMaskedResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K))
    ((M.absNorm:ℝ)*κ) (mul_nonneg hMN.le hκ) hfinite P hP β
  rw [mul_div_cancel_left₀ κ hMN.ne'] at hh
  have hsource : compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
      (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0 =
      ∑' x : 𝓞 K,auxiliaryMaskedResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K)
        (Ideal.Quotient.mk M x)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter β ((mixedEmbedding K (x:K))^3)) := by
    unfold compactCoprimeTraceCubicSum
    apply tsum_congr
    intro x
    change _ = auxiliaryMaskedResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K)
      (Ideal.Quotient.mk (auxiliaryCommonModulus (fieldCenterCubicCharacter γ).1.1 (p:𝓞 K)) x)*_
    rw [auxiliaryMaskedResidueWeight_mk]
    dsimp only [fieldCenterCubicCharacter]
    rw [fieldCenterResidueChar_mk]
    simp only [RingOfIntegers.coe_eq_algebraMap,
      traceTorusCharacter_mk_archimedean,map_pow,traceCharacter_frequency_add,smoothWeightSchwartz_apply,
      Complex.real_smul,traceTorusCharacter_zero,mul_one,ite_mul,zero_mul]
    split_ifs <;> ring
  rw [hsource]
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (add_le_add_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hMNbound (productArcWeight_pos _ _).le)
      (pow_nonneg hP.le _)) 1) (mul_nonneg
        (mul_nonneg (mul_nonneg hC.le hκ) (pow_nonneg hP.le _))
        (Real.rpow_nonneg (productArcWeight_pos _ _).le _))

#print axioms fieldCenterCubicCharacter
#print axioms auxiliaryCommonModulus_nat_norm_le
#print axioms smoothRootCubic_masked_packing_bound
end WaringSiegel.WSL4

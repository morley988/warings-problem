import WaringSiegel.WSL4ArchRootScaled
import WaringSiegel.WSL4ArchRootResidueApproximation

/-! # Exact auxiliary root sources and their common paired main integral -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators SchwartzMap nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliaryMaskedResidueWeight_norm_le_one (c : CubicConductorCharacter K) (p : 𝓞 K)
    (q : 𝓞 K ⧸ auxiliaryCommonModulus c.1.1 p) : ‖auxiliaryMaskedResidueWeight c p q‖≤1 := by
  letI := idealResidueFintype c.1.1 c.1.2
  unfold auxiliaryMaskedResidueWeight
  split_ifs
  · exact le_of_eq (c.2.1.norm_apply _)
  · simp

theorem auxiliaryScaledResidueWeight_norm_le_one (c : CubicConductorCharacter K) (p : 𝓞 K)
    (q : 𝓞 K ⧸ c.1.1) : ‖auxiliaryScaledResidueWeight c p q‖≤1 := by
  letI := idealResidueFintype c.1.1 c.1.2
  exact le_of_eq (c.2.1.norm_apply _)

theorem auxiliary_masked_root_source_center (rho R : ℝ) (hrho : 0<rho) (hR : 0<R)
    (P : ℝ) (p : ℕ) (γ : K) (β : mixedSpace K) :
    compactCoprimeTraceCubicSum (smoothWeightSchwartz rho R hrho hR) P p
      (Submodule.Quotient.mk (mixedEmbedding K γ+β)) 0 =
    ∑' x : 𝓞 K,auxiliaryMaskedResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K)
      (Ideal.Quotient.mk (auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)) x)*
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

theorem auxiliary_scaled_root_source_center (rho R : ℝ) (hrho : 0<rho) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (γ : K) (β : mixedSpace K) :
    smoothTraceSource 3 rho R hrho hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
      (traceTorusMul ((p:𝓞 K)^3) (Submodule.Quotient.mk (mixedEmbedding K γ+β))) =
    ∑' x : 𝓞 K,auxiliaryScaledResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K)
      (Ideal.Quotient.mk (traceConductor γ) x)*
      (smoothRootWeight rho R ((P/(p:ℝ))⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter ((p:ℝ)^3 • β) ((mixedEmbedding K (x:K))^3)) := by
  rw [auxiliary_scaled_trace_center,smoothTraceSource_center_eq]
  unfold smoothPowerCenterSource
  apply tsum_congr
  intro x
  have hphase : fieldCenterResidueChar γ (Ideal.Quotient.mk (traceConductor γ) (((p:𝓞 K)*x)^3)) =
      archimedeanTraceCharacter (mixedEmbedding K ((p:K)^3*γ)) ((mixedEmbedding K (x:K))^3) := by
    rw [fieldCenterResidueChar_mk]
    have he : mixedEmbedding K γ * mixedEmbedding K ((((p:𝓞 K)*x)^3:𝓞 K):K) =
        mixedEmbedding K ((p:K)^3*γ) * (mixedEmbedding K (x:K))^3 := by
      simp only [RingOfIntegers.coe_eq_algebraMap,map_pow,map_mul,map_natCast]
      ring
    unfold archimedeanTraceCharacter
    rw [he]
  change _=auxiliaryScaledResidueWeight (fieldCenterCubicCharacter γ) (p:𝓞 K)
    (Ideal.Quotient.mk (fieldCenterCubicCharacter γ).1.1 x)*_
  rw [auxiliaryScaledResidueWeight_mk]
  change _=fieldCenterResidueChar γ (Ideal.Quotient.mk (traceConductor γ) (((p:𝓞 K)*x)^3))*_
  rw [hphase,traceCharacter_frequency_add]
  simp only [Complex.real_smul]
  ring

theorem auxiliary_scaled_root_frequency (P p : ℝ) (hp : 0<p) (β : mixedSpace K) :
    (P/p)^3 • (p^3 • β)=P^3 • β := by
  rw [smul_smul]
  congr 1
  field_simp [hp.ne']

def auxiliaryRootMaskedMain (rho R P : ℝ) (γ : K) (p : ℕ) (hp : p≠0)
    (β : mixedSpace K) : ℂ :=
  (P^finrank ℚ K:ℂ)*auxiliaryMaskedCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K)
    (Nat.cast_ne_zero.mpr hp)*
      pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) (P^3 • β)

def auxiliaryRootScaledMain (rho R P : ℝ) (γ : K) (p : ℕ) (β : mixedSpace K) : ℂ :=
  ((P/(p:ℝ))^finrank ℚ K:ℂ)*auxiliaryScaledCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K)*
    pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) (P^3 • β)

theorem auxiliary_root_main_normalization (rho R P : ℝ) (N : ℕ) (z : ℂ) (θ : mixedSpace K) :
    (P^finrank ℚ K/((N:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
      (z*weightedRootIntegral 3 (smoothRootWeight rho R) θ) =
    (P^finrank ℚ K:ℂ)*(z/(N:ℂ))*
      pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight rho R) θ := by
  rw [pairedWeightedRootIntegral_eq _ (integerLatticeSourceScale_pos (K:=K)).le]
  simp only [integerLatticeSourceScale,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem auxiliaryRootMaskedMain_eq_raw (rho R P : ℝ) (γ : K) (p : ℕ) (hp : p≠0)
    (β : mixedSpace K) :
    auxiliaryRootMaskedMain rho R P γ p hp β =
    (P^finrank ℚ K/(((auxiliaryCommonModulus (traceConductor γ) (p:𝓞 K)).absNorm:ℝ)*
        basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
      (auxiliaryMaskedTwistedComplete (fieldCenterCubicCharacter γ) (p:𝓞 K)
        (Nat.cast_ne_zero.mpr hp) 0 * weightedRootIntegral 3 (smoothRootWeight rho R) (P^3 • β)) := by
  rw [auxiliary_root_main_normalization]
  have hh := auxiliaryMaskedTwistedComplete_zero_norm (fieldCenterCubicCharacter γ) (p:𝓞 K)
    (Nat.cast_ne_zero.mpr hp)
  change _=(P^finrank ℚ K:ℂ)*
    (auxiliaryMaskedTwistedComplete (fieldCenterCubicCharacter γ) (p:𝓞 K) (Nat.cast_ne_zero.mpr hp) 0 /
      ((auxiliaryCommonModulus (fieldCenterCubicCharacter γ).1.1 (p:𝓞 K)).absNorm:ℂ))*_
  rw [hh]
  rfl

theorem auxiliaryRootScaledMain_eq_raw (rho R P : ℝ) (γ : K) (p : ℕ) (β : mixedSpace K) :
    auxiliaryRootScaledMain rho R P γ p β =
    ((P/(p:ℝ))^finrank ℚ K/(((traceConductor γ).absNorm:ℝ)*
        basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
      (auxiliaryScaledTwistedComplete (fieldCenterCubicCharacter γ) (p:𝓞 K) 0 *
        weightedRootIntegral 3 (smoothRootWeight rho R) (P^3 • β)) := by
  rw [auxiliary_root_main_normalization]
  have hh := auxiliaryScaledTwistedComplete_zero_norm (fieldCenterCubicCharacter γ) (p:𝓞 K)
  have hh' : auxiliaryScaledTwistedComplete (fieldCenterCubicCharacter γ) (p:𝓞 K) 0 /
      ((traceConductor γ).absNorm:ℂ)=auxiliaryScaledCubicAverage (fieldCenterCubicCharacter γ) (p:𝓞 K) := hh
  rw [hh']
  simp only [auxiliaryRootScaledMain,Complex.ofReal_div]

#print axioms auxiliary_masked_root_source_center
#print axioms auxiliary_scaled_root_source_center
#print axioms auxiliaryRootMaskedMain_eq_raw
#print axioms auxiliaryRootScaledMain_eq_raw
end WaringSiegel.WSL4

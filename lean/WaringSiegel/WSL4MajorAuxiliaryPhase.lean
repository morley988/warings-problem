import WaringSiegel.WSL4MajorAuxiliarySources
import WaringSiegel.WSL4ArchAuxiliaryMain
import WaringSiegel.WSL4MajorScaling

/-! # Exact auxiliary target phase and the lattice-normalized main integral -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem auxiliary_root_main_phase (ρ R : ℝ) (target : 𝓞 K) (htarget : target≠0)
    (γ : K) (p : ℕ) (hp : p≠0) (β : mixedSpace K) :
    (auxiliaryRootMaskedMain ρ R (rootScale 3 target) γ p hp β)^4 *
      (auxiliaryRootScaledMain ρ R (rootScale 3 target) γ p β)^4 *
      traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      ((((rootScale 3 target)^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4:ℝ):ℂ) *
        rationalCenterAuxiliaryContribution (fieldRationalCenter γ) (p:𝓞 K)
          (Nat.cast_ne_zero.mpr hp) target *
        (archimedeanTraceCharacter (-((rootScale 3 target)^3 • β)) (normalizedTarget 3 1 target) *
          pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight ρ R)
            ((rootScale 3 target)^3 • β)^8) := by
  rw [traceTorusCharacter_rootScale_center_phase 3 (by norm_num) target htarget]
  have hphase : traceTorusCharacter (-target) (traceRationalPoint γ) =
      (fieldCenterCubicCharacter γ).2.1 (-Ideal.Quotient.mk (traceConductor γ) target) := by
    change traceTorusCharacter (-target) (traceRationalPoint γ) =
      fieldCenterResidueChar γ (-Ideal.Quotient.mk (traceConductor γ) target)
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_neg target]
    rfl
  rw [hphase]
  calc
    _ = ((auxiliaryRootMaskedMain ρ R (rootScale 3 target) γ p hp β)^4 *
        (auxiliaryRootScaledMain ρ R (rootScale 3 target) γ p β)^4 *
        (fieldCenterCubicCharacter γ).2.1 (-Ideal.Quotient.mk (traceConductor γ) target)) *
        archimedeanTraceCharacter (-((rootScale 3 target)^3 • β)) (normalizedTarget 3 1 target) := by ring
    _ = _ := by
      rw [auxiliary_root_main_product_character,auxiliary_field_character_eq_rational]
      ring

theorem auxiliary_major_volume_identity (P : ℝ) (hP : 0<P) (p : ℕ) :
    ((P^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4)*((P^3)^finrank ℚ K)⁻¹ =
      auxiliaryMajorScale (K := K) P p := by
  have he : (P^3)^finrank ℚ K=(P^finrank ℚ K)^3 := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm 3]
  have hX : (P^finrank ℚ K)≠0 := pow_ne_zero _ hP.ne'
  rw [he,auxiliaryMajorScale]
  calc
    _ = ((P^finrank ℚ K)^8*((P^finrank ℚ K)^3)⁻¹)/((p:ℝ)^finrank ℚ K)^4 := by ring
    _ = _ := by
      congr 1
      field_simp [hX]

theorem auxiliary_root_main_integral (ρ R L : ℝ) (target : 𝓞 K) (htarget : target≠0)
    (γ : K) (p : ℕ) (hp : p≠0) :
    (∫ β in centeredTraceArc ((rootScale 3 target)^3) L γ,
      (auxiliaryRootMaskedMain ρ R (rootScale 3 target) γ p hp β)^4 *
        (auxiliaryRootScaledMain ρ R (rootScale 3 target) γ p β)^4 *
        traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β))
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)) =
      (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
        rationalCenterAuxiliaryContribution (fieldRationalCenter γ) (p:𝓞 K)
          (Nat.cast_ne_zero.mpr hp) target *
        productSingularIntegral 3 8 ρ R (L/((traceConductor γ).absNorm:ℝ))
          (normalizedTarget 3 1 target) := by
  have hP := rootScale_pos htarget 3
  simp_rw [auxiliary_root_main_phase ρ R target htarget γ p hp]
  rw [integral_const_mul,integral_centeredTraceArc_scale ((rootScale 3 target)^3) L
    (pow_pos hP 3) γ (fun β => archimedeanTraceCharacter (-β) (normalizedTarget 3 1 target) *
      pairedWeightedRootIntegral (integerLatticeSourceScale K) 3 (smoothRootWeight ρ R) β^8),
    centeredTraceArc_one_eq]
  simp only [Complex.real_smul]
  have he := auxiliary_major_volume_identity (K := K) (rootScale 3 target) hP p
  calc
    _ = (((((rootScale 3 target)^finrank ℚ K)^8/((p:ℝ)^finrank ℚ K)^4)*
        (((rootScale 3 target)^3)^finrank ℚ K)⁻¹:ℝ):ℂ) *
        rationalCenterAuxiliaryContribution (fieldRationalCenter γ) (p:𝓞 K)
          (Nat.cast_ne_zero.mpr hp) target *
        productSingularIntegral 3 8 ρ R (L/((traceConductor γ).absNorm:ℝ))
          (normalizedTarget 3 1 target) := by
      simp only [Complex.ofReal_mul,productSingularIntegral]
      ring
    _ = _ := by rw [he]

local instance auxiliaryPhaseCentersFintype (N : ℕ) : Fintype (traceRationalCenters K N) :=
  Fintype.ofFinite _

def auxiliaryMajorMainIntegral (ρ R P L : ℝ) (p : ℕ) (hp : p≠0) (target : 𝓞 K) : ℂ :=
  ∑ q : traceRationalCenters K ⌊L⌋₊,
    ∫ β in centeredTraceArc (P^3) L (traceCenterRepresentative q),
      (auxiliaryRootMaskedMain ρ R P (traceCenterRepresentative q) p hp β)^4 *
        (auxiliaryRootScaledMain ρ R P (traceCenterRepresentative q) p β)^4 *
        traceTorusCharacter (-target)
          (Submodule.Quotient.mk (mixedEmbedding K (traceCenterRepresentative q)+β))
        ∂archimedeanDualMeasure (integerLatticeSourceScale K)

theorem auxiliaryMajorMainIntegral_rootScale_formula (ρ R L : ℝ)
    (p : ℕ) (hp : p≠0) (target : 𝓞 K) (htarget : target≠0) :
    auxiliaryMajorMainIntegral ρ R (rootScale 3 target) L p hp target =
      (auxiliaryMajorScale (K := K) (rootScale 3 target) p:ℂ) *
      ∑ q : traceRationalCenters K ⌊L⌋₊,
        rationalCenterAuxiliaryContribution (fieldRationalCenter (traceCenterRepresentative q))
          (p:𝓞 K) (Nat.cast_ne_zero.mpr hp) target *
          productSingularIntegral 3 8 ρ R
            (L/((traceConductor (traceCenterRepresentative q)).absNorm:ℝ))
            (normalizedTarget 3 1 target) := by
  unfold auxiliaryMajorMainIntegral
  simp_rw [auxiliary_root_main_integral ρ R L target htarget]
  simp only [Finset.mul_sum,mul_assoc]

#print axioms auxiliary_root_main_phase
#print axioms auxiliary_root_main_integral
#print axioms auxiliaryMajorMainIntegral_rootScale_formula
end WaringSiegel.WSL4

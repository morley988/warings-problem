import WaringSiegel.WSL3MomentRepresentationSmooth
import WaringSiegel.WSL3IdealPoissonPowerProductApproximation
import WaringSiegel.WSL3UnitSmoothNormalization

/-! # Exact major-arc source, target phase, and paired main normalization

The finite trace-torus sum is identified with the literal smooth Poisson
source.  Both the integer-lattice covolume and the target scaling are kept.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def smoothTraceSource (k : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : P≠0) : ArchimedeanTraceTorus K → ℂ :=
  compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP

theorem smoothTraceSource_continuous (k : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : P≠0) : Continuous (smoothTraceSource (K := K) k ρ R hρ hR P hP) :=
  compactTraceWeylSum_continuous _ _ _ _ _

theorem smoothTraceSource_center_eq (k : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : P≠0) (γ : K) (β : mixedSpace K) :
    smoothTraceSource k ρ R hρ hR P hP
      (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      smoothPowerCenterSource k ρ R P γ β := by
  rw [smoothTraceSource,compactTraceWeylSum_mk]
  simp only [smoothWeightSchwartz_apply,smoothPowerCenterSource,Complex.real_smul]

def smoothTraceIntegrand (k n : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : P≠0) (target : 𝓞 K) (q : ArchimedeanTraceTorus K) : ℂ :=
  smoothTraceSource k ρ R hρ hR P hP q ^ n * traceTorusCharacter (-target) q

theorem smoothTraceIntegrand_continuous (k n : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : P≠0) (target : 𝓞 K) :
    Continuous (smoothTraceIntegrand k n ρ R hρ hR P hP target) :=
  ((smoothTraceSource_continuous k ρ R hρ hR P hP).pow n).mul
    (traceTorusCharacter_continuous (-target))

theorem traceTorusCharacter_center_phase (target : 𝓞 K) (γ : K) (β : mixedSpace K) :
    traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      traceTorusCharacter (-target) (traceRationalPoint γ) *
        archimedeanTraceCharacter (-β) (mixedEmbedding K (target:K)) := by
  have hbase (x : mixedSpace K) : traceTorusCharacter (-target) (Submodule.Quotient.mk x) =
      archimedeanTraceCharacter (mixedEmbedding K ((-target:𝓞 K):K)) x := by
    rw [traceTorusCharacter_mk]
    rfl
  rw [hbase,archimedeanTraceCharacter_add,traceRationalPoint,hbase]
  congr 1
  simp only [archimedeanTraceCharacter,RingOfIntegers.coe_eq_algebraMap,map_neg,neg_mul,
    mul_comm (mixedEmbedding K (target:K)) β]

theorem normalized_target_phase (k : ℕ) (hk : 0<k) (target : 𝓞 K)
    (htarget : target≠0) (β : mixedSpace K) :
    archimedeanTraceCharacter (-((rootScale k target)^k • β)) (normalizedTarget k 1 target) =
      archimedeanTraceCharacter (-β) (mixedEmbedding K (target:K)) := by
  rw [normalizedTarget_eq_rootScale k hk]
  simp only [Units.val_one,one_pow,one_mul]
  rw [← smul_neg,traceCharacter_smul_cancel _ (pow_ne_zero _ (rootScale_pos htarget k).ne')]

theorem traceTorusCharacter_rootScale_center_phase
    (k : ℕ) (hk : 0<k) (target : 𝓞 K) (htarget : target≠0) (γ : K) (β : mixedSpace K) :
    traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      traceTorusCharacter (-target) (traceRationalPoint γ) *
        archimedeanTraceCharacter (-((rootScale k target)^k • β)) (normalizedTarget k 1 target) := by
  rw [normalized_target_phase k hk target htarget]
  exact traceTorusCharacter_center_phase target γ β

theorem smoothPowerCenterMainTerm_eq_paired (k : ℕ) (ρ R P : ℝ)
    (γ : K) (β : mixedSpace K) :
    smoothPowerCenterMainTerm k ρ R P γ β =
      (P^(finrank ℚ K) : ℂ) *
        (((traceConductor γ).absNorm : ℂ)⁻¹ * fieldCenterCompleteSum k γ 0) *
          pairedWeightedRootIntegral (integerLatticeSourceScale K) k
            (smoothRootWeight ρ R) (P^k • β) := by
  rw [smoothPowerCenterMainTerm,pairedWeightedRootIntegral_eq _
    (integerLatticeSourceScale_pos (K := K)).le]
  simp only [integerLatticeSourceScale,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Complex.ofReal_pow,
    div_eq_mul_inv,mul_inv_rev]
  ring

def majorCompleteCoefficient (k n : ℕ) (target : 𝓞 K) (γ : K) : ℂ :=
  (((traceConductor γ).absNorm : ℂ)⁻¹ * fieldCenterCompleteSum k γ 0)^n *
    traceTorusCharacter (-target) (traceRationalPoint γ)

/-- Exact separation of the arithmetic coefficient and the paired
archimedean integrand at the target's prescribed root scale. -/
theorem smoothPowerCenterMainTerm_pow_phase
    (k n : ℕ) (hk : 0<k) (ρ R : ℝ) (target : 𝓞 K) (htarget : target≠0)
    (γ : K) (β : mixedSpace K) :
    smoothPowerCenterMainTerm k ρ R (rootScale k target) γ β ^ n *
      traceTorusCharacter (-target) (Submodule.Quotient.mk (mixedEmbedding K γ+β)) =
      ((rootScale k target)^(finrank ℚ K*n) : ℂ) * majorCompleteCoefficient k n target γ *
        (archimedeanTraceCharacter (-((rootScale k target)^k • β)) (normalizedTarget k 1 target) *
          pairedWeightedRootIntegral (integerLatticeSourceScale K) k
            (smoothRootWeight ρ R) ((rootScale k target)^k • β)^n) := by
  rw [smoothPowerCenterMainTerm_eq_paired,
    traceTorusCharacter_rootScale_center_phase k hk target htarget]
  simp only [majorCompleteCoefficient,mul_pow,Complex.ofReal_pow,pow_mul]
  ring

#print axioms smoothTraceSource_center_eq
#print axioms traceTorusCharacter_rootScale_center_phase
#print axioms smoothPowerCenterMainTerm_eq_paired
#print axioms smoothPowerCenterMainTerm_pow_phase
end WaringSiegel.WSL4

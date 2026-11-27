import WaringSiegel.WSL3IdealPoissonPower
import WaringSiegel.WSL3TraceIdealDuality

/-!
# Exact major-arc expansion at an actual field center

The modulus is the actual trace conductor of gamma, its quotient character
is constructed from the literal trace phase, and every dual frequency is in
D^-1 a_gamma^-1. No arithmetic character correspondence is a hypothesis.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def fieldCenterResidueChar (γ : K) : AddChar (𝓞 K ⧸ traceConductor γ) ℂ :=
  traceIdealAddChar (traceConductor γ) ⟨traceRationalPoint γ,γ,rfl,le_rfl⟩

@[simp] theorem fieldCenterResidueChar_mk (γ : K) (x : 𝓞 K) :
    fieldCenterResidueChar γ (Ideal.Quotient.mk (traceConductor γ) x) =
      archimedeanTraceCharacter (mixedEmbedding K γ) (mixedEmbedding K (x:K)) := by
  rw [fieldCenterResidueChar,traceIdealAddChar_mk]
  change traceTorusCharacter x (traceRationalPoint γ) = _
  rw [traceRationalPoint,traceTorusCharacter_mk]
  unfold archimedeanTraceCharacter
  rw [mul_comm (mixedEmbedding K (x:K)) (mixedEmbedding K γ)]

def fieldCenterResidueFintype (γ : K) : Fintype (𝓞 K ⧸ traceConductor γ) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot (traceConductor γ) (traceConductor_ne_zero γ)
  exact Fintype.ofFinite _

def fieldCenterCompleteSum (k : ℕ) (γ : K) (ξ : mixedSpace K) : ℂ :=
  letI := fieldCenterResidueFintype γ
  idealCompleteTraceFactor (traceConductor γ) (fun q => fieldCenterResidueChar γ (q^k)) ξ

/-- The finite coefficient is the literal complete power sum with the
actual linear trace twist, evaluated on a full residue system. -/
theorem fieldCenterCompleteSum_formula (k : ℕ) (γ : K) (ξ : mixedSpace K) :
    letI := fieldCenterResidueFintype γ
    fieldCenterCompleteSum k γ ξ =
      ∑ q : 𝓞 K ⧸ traceConductor γ,
        archimedeanTraceCharacter (mixedEmbedding K γ)
          ((mixedEmbedding K (idealResidueRepresentative (traceConductor γ) q:K))^k) *
        archimedeanTraceCharacter ξ
          (mixedEmbedding K (idealResidueRepresentative (traceConductor γ) q:K)) := by
  letI := fieldCenterResidueFintype γ
  unfold fieldCenterCompleteSum idealCompleteTraceFactor
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  simpa only [map_pow,idealResidueRepresentative_spec] using
    fieldCenterResidueChar_mk γ ((idealResidueRepresentative (traceConductor γ) q)^k)

/-- The exact complete sum at zero dual frequency is the usual pure
complete power sum over the actual trace conductor. -/
theorem fieldCenterCompleteSum_zero (k : ℕ) (γ : K) :
    letI := fieldCenterResidueFintype γ
    fieldCenterCompleteSum k γ 0 = ∑ q : 𝓞 K ⧸ traceConductor γ, fieldCenterResidueChar γ (q^k) := by
  letI := fieldCenterResidueFintype γ
  simp only [fieldCenterCompleteSum,idealCompleteTraceFactor,archimedeanTraceCharacter,
    zero_mul,map_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]

/-- Literal major-arc identity at any gamma in K, for every degree k.
The unit source, true trace conductor, complete sums, and dual ideal are all
constructed objects, and the identity has no major-arc approximation premise. -/
theorem poisson_smoothPower_at_field_center (k : ℕ) (γ : K)
    (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    (∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^k)) =
      (P^(finrank ℚ K)/(((traceConductor γ).absNorm:ℝ)*
        basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
        (∑' ξ : (inverseDifferent K * (traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          fieldCenterCompleteSum k γ (mixedEmbedding K (ξ:K)) *
            smoothPowerLinearIntegral k rho R (P^k • θ) (-(P • mixedEmbedding K (ξ:K)))) := by
  letI := fieldCenterResidueFintype γ
  have h := poisson_smoothPower_residue_weight k (traceConductor γ) (traceConductor_ne_zero γ)
    (fun q => fieldCenterResidueChar γ (q^k)) rho R hrho hR P hP θ
  change (∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^k)*
    (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))) = _ at h
  calc
    _ = ∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^k)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k)) := by
      apply tsum_congr
      intro x
      rw [← (Ideal.Quotient.mk (traceConductor γ)).map_pow x k,
        fieldCenterResidueChar_mk,traceCharacter_frequency_add]
      simp only [map_pow,Complex.real_smul]
      ring
    _ = _ := h

#print axioms fieldCenterCompleteSum_formula
#print axioms poisson_smoothPower_at_field_center
end WaringSiegel.WSL3Poisson

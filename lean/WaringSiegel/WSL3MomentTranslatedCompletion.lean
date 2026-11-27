import WaringSiegel.WSL3MomentShiftedCompletion
import WaringSiegel.WSL3MomentTranslationSupport

/-! # Exact common-domain completion and averaging

The original compact smooth sum is moved to one enlarged finite domain for
all common translations. The domain is a union, so its cardinality is bounded
by one enlarged box, rather than multiplied by the number of translations.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def smoothLowerMoment (f : 𝓢(mixedSpace K, ℂ)) (R s : ℕ)
    (S : Finset (𝓞 K)) (P : ℝ) (θ : mixedSpace K) : ℝ :=
  ∫ η, ‖frequencySum (vinogradovFrequency (integerCoordinates K) R (fun x : S => x.val))
    (fun x => f (P⁻¹ • mixedEmbedding K (x.val:K)) *
      latticeCharacter (integerCoordinates K (x.val^(R+2))) (archimedeanTorusHom θ)) η‖^(2*s)
    ∂latticeHaar

theorem smoothLowerMoment_nonneg (f : 𝓢(mixedSpace K, ℂ)) (R s : ℕ)
    (S : Finset (𝓞 K)) (P : ℝ) (θ : mixedSpace K) :
    0 ≤ smoothLowerMoment f R s S P θ :=
  integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)

theorem smoothLowerMoment_translate (f : 𝓢(mixedSpace K, ℂ)) (R s : ℕ)
    (S T : Finset (𝓞 K)) (P : ℝ) (θ : mixedSpace K) (z : 𝓞 K)
    (hsupp : ∀ x : 𝓞 K, f (P⁻¹ • mixedEmbedding K (x:K)) ≠ 0 → x∈S)
    (hT : ∀ x∈S, x-z∈T) :
    smoothLowerMoment f R s S P θ =
      ∫ η, ‖frequencySum (vinogradovFrequency (integerCoordinates K) R (fun a : T => a.val+z))
        (fun a => f (P⁻¹ • mixedEmbedding K ((a.val+z:𝓞 K):K)) *
          latticeCharacter (integerCoordinates K ((a.val+z)^(R+2))) (archimedeanTorusHom θ)) η‖^(2*s)
        ∂latticeHaar := by
  apply integral_congr_ae
  filter_upwards with η
  congr 2
  unfold frequencySum
  have h := finite_sum_common_translate
    (fun x : 𝓞 K => f (P⁻¹ • mixedEmbedding K (x:K)))
    (fun x => latticeCharacter (integerCoordinates K (x^(R+2))) (archimedeanTorusHom θ) *
      latticeCharacter (vinogradovFrequency (integerCoordinates K) R (fun y : 𝓞 K => y) x) η)
    S T z hsupp hT
  simpa only [mul_assoc, vinogradovFrequency] using h

/-- Exact L1 completion cost for the finite common-translation average. -/
theorem smoothLowerMoment_average_le (f : 𝓢(mixedSpace K, ℂ))
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s)
    (S Y : Finset (𝓞 K)) (P : ℝ) (θ : mixedSpace K)
    (hsupp : ∀ x : 𝓞 K, f (P⁻¹ • mixedEmbedding K (x:K)) ≠ 0 → x∈S) :
    (Y.card:ℝ) * smoothLowerMoment f R s S P θ ≤
      (∫ β, ‖weightCompletionAmplitude f β‖)^(2*s) *
        ∑ z : Y, sliceMoment s
          (vinogradovFrequency (integerCoordinates K) R (fun a : translatedUnion S Y => a.val))
          (fun a => integerCoordinates K (a.val^(R+1)))
          (fun a => latticeCharacter (integerCoordinates K (a.val^(R+2))) (archimedeanTorusHom θ))
          (archimedeanTorusHom (((R+2:ℕ):ℝ) • θ * mixedEmbedding K (z.val:K))) := by
  have hz (z : Y) : smoothLowerMoment f R s S P θ ≤
      (∫ β, ‖weightCompletionAmplitude f β‖)^(2*s) *
        sliceMoment s
          (vinogradovFrequency (integerCoordinates K) R (fun a : translatedUnion S Y => a.val))
          (fun a => integerCoordinates K (a.val^(R+1)))
          (fun a => latticeCharacter (integerCoordinates K (a.val^(R+2))) (archimedeanTorusHom θ))
          (archimedeanTorusHom (((R+2:ℕ):ℝ) • θ * mixedEmbedding K (z.val:K))) := by
    rw [smoothLowerMoment_translate f R s S (translatedUnion S Y) P θ z.val hsupp
      (fun x hx => mem_translatedUnion S Y hx z.property)]
    exact shifted_weighted_lower_moment_le f R s hR hs
      (fun a : translatedUnion S Y => a.val) P z.val θ
  have h := Finset.sum_le_sum (s := Finset.univ) (fun z _ => hz z)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
    ← Finset.mul_sum] using h

#print axioms smoothLowerMoment_average_le
end WaringSiegel.WSL3

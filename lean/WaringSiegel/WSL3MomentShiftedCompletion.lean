import WaringSiegel.WSL3MomentCompletionHaar
import WaringSiegel.WSL3MomentShiftedSlices
import WaringSiegel.WSL3MomentCompactKernel

/-! # Completed common-shift bound for actual smooth weighted moments -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

theorem latticeCharacter_shifted_top_coefficient (k : ℕ) (z a : 𝓞 K) (θ : mixedSpace K) :
    latticeCharacter (integerCoordinates K a)
      (archimedeanTorusHom (((k:ℝ) • θ)*mixedEmbedding K (z:K))) =
      latticeCharacter (integerCoordinates K ((k:𝓞 K)*z*a)) (archimedeanTorusHom θ) := by
  rw [latticeCharacter_integer_arch, latticeCharacter_integer_arch]
  unfold archimedeanTraceCharacter
  congr 1
  congr 1
  congr 1
  simp only [map_mul, map_natCast, Algebra.smul_def]
  ring

/-- The smoothing loss is the exact L1 Fourier mass to the moment power.
The actual common shift changes only the next coefficient after integration
of the first R lower coefficients. -/
theorem shifted_weighted_lower_moment_le (f : 𝓢(mixedSpace K, ℂ))
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s) (nodes : α → 𝓞 K)
    (P : ℝ) (z : 𝓞 K) (θ : mixedSpace K) :
    (∫ η, ‖frequencySum (vinogradovFrequency (integerCoordinates K) R (fun a => nodes a+z))
      (fun a => f (P⁻¹ • mixedEmbedding K ((nodes a+z:𝓞 K):K)) *
        latticeCharacter (integerCoordinates K ((nodes a+z)^(R+2))) (archimedeanTorusHom θ)) η‖^(2*s)
      ∂latticeHaar) ≤
      (∫ β, ‖weightCompletionAmplitude f β‖)^(2*s) *
        sliceMoment s (vinogradovFrequency (integerCoordinates K) R nodes)
          (fun a => integerCoordinates K (nodes a^(R+1)))
          (fun a => latticeCharacter (integerCoordinates K (nodes a^(R+2))) (archimedeanTorusHom θ))
          (archimedeanTorusHom (((R+2:ℕ):ℝ) • θ * mixedEmbedding K (z:K))) := by
  let points : α → mixedSpace K := fun a => mixedEmbedding K (nodes a:K)
  let v := vinogradovFrequency (integerCoordinates K) R (fun a => nodes a+z)
  let a : (Fin R × NumberFieldCoordinateIndex K → AddCircle (1 : ℝ)) → α → ℂ :=
    fun η x => latticeCharacter (integerCoordinates K ((nodes x+z)^(R+2)))
      (archimedeanTorusHom θ) * latticeCharacter (v x) η
  have ha (x : α) : Continuous (fun η => a η x) :=
    continuous_const.mul (continuous_latticeCharacter _)
  have hnorm (η) (x : α) : ‖a η x‖ ≤ 1 := by
    simp only [a, norm_mul, norm_latticeCharacter_eq_one, mul_one, le_refl]
  have h := finite_sum_shifted_weight_haar_completion f points a ha 1 zero_le_one hnorm P
    (-mixedEmbedding K (z:K)) (2*s-1)
  have hn : 2*s-1+1=2*s := by omega
  have hleft (η) : (∑ x, a η x * f (P⁻¹ • (points x-(-mixedEmbedding K (z:K))))) =
      frequencySum v (fun x => f (P⁻¹ • mixedEmbedding K ((nodes x+z:𝓞 K):K)) *
        latticeCharacter (integerCoordinates K ((nodes x+z)^(R+2))) (archimedeanTorusHom θ)) η := by
    unfold frequencySum
    apply Finset.sum_congr rfl
    intro x hx
    simp only [a, points, sub_neg_eq_add, map_add]
    ring
  have hcomplete (β : mixedSpace K) (η) : completedFiniteSum points (a η) P β =
      frequencySum v (fun x => latticeCharacter (integerCoordinates K ((nodes x+z)^(R+2)))
        (archimedeanTorusHom θ) *
        latticeCharacter (integerCoordinates K (nodes x)) (archimedeanTorusHom (P⁻¹ • β))) η := by
    unfold completedFiniteSum frequencySum
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only [a, points]
    rw [latticeCharacter_integer_arch (nodes x) (P⁻¹ • β)]
    ring
  have hslice (β : mixedSpace K) := shifted_lower_moment_eq_slice (integerCoordinates K)
    (integerCoordinates_injective K) R s hR nodes z (archimedeanTorusHom θ)
    (archimedeanTorusHom (P⁻¹ • β))
    (archimedeanTorusHom (((R+2:ℕ):ℝ) • θ * mixedEmbedding K (z:K))) (fun a => by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        latticeCharacter_shifted_top_coefficient (R+2) z a θ)
  simp only [hn, hleft, hcomplete] at h
  dsimp only [v] at h
  simp_rw [hslice] at h
  rw [integral_mul_const] at h
  convert h using 1
  rw [← mul_assoc, ← pow_succ, hn]

#print axioms shifted_weighted_lower_moment_le
end WaringSiegel.WSL3

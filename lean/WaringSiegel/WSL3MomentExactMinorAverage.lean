import WaringSiegel.WSL3MomentTranslatedCompletion
import WaringSiegel.WSL3MomentExactSliceKernel
import WaringSiegel.WSL3MomentSliceFullIntegral

/-! # Minor-arc averaging with the top-coefficient phase retained -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem smoothLowerMoment_minor_average_exact (f : 𝓢(mixedSpace K, ℂ))
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S Y : Finset (𝓞 K),
      (∀ x : 𝓞 K, f (P⁻¹ • mixedEmbedding K (x:K)) ≠ 0 → x∈S) →
      (∀ x∈S, ∀ v : InfinitePlace K, v (x:K) ≤ A*P) →
      (∀ y∈Y, ∀ v : InfinitePlace K, v (y:K) ≤ P) →
      ∀ θ : mixedSpace K,
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (P^(R+2)) (((R+2:ℕ):ℝ)^finrank ℚ K * P^finrank ℚ K) →
      (Y.card:ℝ) * smoothLowerMoment f R s S P θ ≤
        C * (P^finrank ℚ K)^(R+1) *
          monomialSliceIntegral (integerCoordinates K) R s
            (fun a : translatedUnion S Y => a.val) (archimedeanTorusHom θ) := by
  let D : ℝ := 2*s*(A+1)^(R+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨C, hC, hb⟩ := monomial_slice_shifted_minor_bound_exact (K := K) D hD
  let L : ℝ := (∫ β, ‖weightCompletionAmplitude f β‖)^(2*s)
  have hL : 0 ≤ L := pow_nonneg (integral_nonneg (fun _ => norm_nonneg _)) _
  refine ⟨(1+L)*C, mul_pos (by linarith) hC, ?_⟩
  intro P hP S Y hsupp hS hY θ hminor
  let T := translatedUnion S Y
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hT := translatedUnion_place_bound S Y A P hS hY
  have hδ (x y : Fin s → T) (v : InfinitePlace K) :
      v (((∑ i, (x i).val^(R+1)) - ∑ i, (y i).val^(R+1) : 𝓞 K):K) ≤ D*P^(R+1) := by
    have hx := place_indexed_sum_power_le (fun a : T => a.val)
      (show 0 ≤ (A+1)*P by positivity) (fun a v => hT a.val a.property v) (R+1) s x
    have hy := place_indexed_sum_power_le (fun a : T => a.val)
      (show 0 ≤ (A+1)*P by positivity) (fun a v => hT a.val a.property v) (R+1) s y
    have h := place_sub_le_twice hx hy v
    apply h.trans_eq
    dsimp [D]
    rw [mul_pow]
    ring
  have hm : (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
      traceMajorArcUnion (P*P^(R+1)) (((R+2:ℕ):ℝ)^finrank ℚ K * P^finrank ℚ K) := by
    simpa only [← pow_succ', show R+1+1=R+2 by omega] using hminor
  have h := hb P (P^(R+1)) hP (pow_le_pow_right₀ hP (by omega)) θ (R+2) (by omega)
    hm Y hY (fun a : T => a.val)
    (fun a => latticeCharacter (integerCoordinates K (a.val^(R+2))) (archimedeanTorusHom θ)) R s hδ
  have havg := smoothLowerMoment_average_le f R s hR hs S Y P θ hsupp
  have hmoment := monomialSliceIntegral_nonneg (integerCoordinates K) R s
    (fun a : T => a.val) (archimedeanTorusHom θ)
  calc
    _ ≤ L * _ := havg
    _ ≤ L * (C * (P^(R+1))^finrank ℚ K *
        monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
          (archimedeanTorusHom θ)) := mul_le_mul_of_nonneg_left h hL
    _ ≤ (1+L) * (C * (P^(R+1))^finrank ℚ K *
        monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
          (archimedeanTorusHom θ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by
      rw [← pow_mul, Nat.mul_comm (R+1), pow_mul]
      ring

#print axioms smoothLowerMoment_minor_average_exact
end WaringSiegel.WSL3

import WaringSiegel.WSL3MomentExactMinorAverage

/-! # Exact minor-arc averaging with an independently chosen translation radius -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem smoothLowerMoment_flexible_minor_average (f : 𝓢(mixedSpace K, ℂ))
    (R s : ℕ) (hR : 1≤R) (hs : 1≤s) (A : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0<C ∧ ∀ P B H : ℝ, 1≤P → 1≤B → B≤P → B^2≤H → P^(R+1)≤H →
      ∀ S Y : Finset (𝓞 K),
      (∀ x : 𝓞 K, f (P⁻¹ • mixedEmbedding K (x:K))≠0 → x∈S) →
      (∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤A*P) →
      (∀ y∈Y, ∀ v : InfinitePlace K, v (y:K)≤B) →
      ∀ θ : mixedSpace K,
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K)∉
        traceMajorArcUnion (B*H) (((R+2:ℕ):ℝ)^finrank ℚ K * B^finrank ℚ K) →
      (Y.card:ℝ)*smoothLowerMoment f R s S P θ ≤
        C*H^finrank ℚ K * monomialSliceIntegral (integerCoordinates K) R s
          (fun a : translatedUnion S Y => a.val) (archimedeanTorusHom θ) := by
  let D : ℝ := 2*s*(A+1)^(R+1)
  have hD : 0≤D := by dsimp [D]; positivity
  obtain ⟨C,hC,hb⟩ := monomial_slice_shifted_minor_bound_exact (K := K) D hD
  let L : ℝ := (∫ β, ‖weightCompletionAmplitude f β‖)^(2*s)
  have hL : 0≤L := pow_nonneg (integral_nonneg (fun _ => norm_nonneg _)) _
  refine ⟨(1+L)*C,mul_pos (by linarith) hC,?_⟩
  intro P B H hP hB hBP hBH hPH S Y hsupp hS hY θ hminor
  let T := translatedUnion S Y
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  have hH0 : 0≤H := (sq_nonneg B).trans hBH
  have hT := translatedUnion_place_bound S Y A P hS (fun y hy v => (hY y hy v).trans hBP)
  have hδ (x y : Fin s → T) (v : InfinitePlace K) :
      v (((∑ i, (x i).val^(R+1))-∑ i, (y i).val^(R+1) : 𝓞 K):K)≤D*H := by
    have hx := place_indexed_sum_power_le (fun a : T => a.val)
      (show 0≤(A+1)*P by positivity) (fun a v => hT a.val a.property v) (R+1) s x
    have hy := place_indexed_sum_power_le (fun a : T => a.val)
      (show 0≤(A+1)*P by positivity) (fun a v => hT a.val a.property v) (R+1) s y
    have he := place_sub_le_twice hx hy v
    calc
      _ ≤ 2*(s*((A+1)*P)^(R+1)) := he
      _ = D*P^(R+1) := by dsimp [D]; rw [mul_pow]; ring
      _ ≤ D*H := mul_le_mul_of_nonneg_left hPH hD
  have hb' := hb B H hB hBH θ (R+2) (by omega) hminor Y hY (fun a : T => a.val)
    (fun a => latticeCharacter (integerCoordinates K (a.val^(R+2))) (archimedeanTorusHom θ)) R s hδ
  have havg := smoothLowerMoment_average_le f R s hR hs S Y P θ hsupp
  have hmoment := monomialSliceIntegral_nonneg (integerCoordinates K) R s
    (fun a : T => a.val) (archimedeanTorusHom θ)
  calc
    _ ≤ L*_ := havg
    _ ≤ L*(C*H^finrank ℚ K * monomialSliceIntegral (integerCoordinates K) R s
        (fun a : T => a.val) (archimedeanTorusHom θ)) := mul_le_mul_of_nonneg_left hb' hL
    _ ≤ (1+L)*(C*H^finrank ℚ K * monomialSliceIntegral (integerCoordinates K) R s
        (fun a : T => a.val) (archimedeanTorusHom θ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

#print axioms smoothLowerMoment_flexible_minor_average
end WaringSiegel.WSL4

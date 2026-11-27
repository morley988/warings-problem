import WaringSiegel.WSL4MixedSixthFourier

/-! # Bounded nonnegative weights are dominated through the literal mixed count -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]
variable {α β : Type*} [Fintype α] [Fintype β]

def coprimeRealWeight (a : 𝓞 K) (x : α → 𝓞 K) (w : α → ℝ) (i : α) : ℝ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x i)) then w i else 0

theorem traceCoprimeWeylSum_real_mask (a : 𝓞 K) (x : α → 𝓞 K) (w : α → ℝ)
    (q : ArchimedeanTraceTorus K) :
    traceCoprimeWeylSum a 3 x (fun i => (w i : ℂ)) q =
      traceWeylSum 3 x (fun i => (coprimeRealWeight a x w i : ℂ)) q := by
  simp only [traceCoprimeWeylSum,traceWeylSum,coprimeRealWeight]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem mixedSecondFourthCoefficient_mask_le (a : 𝓞 K) (x : α → 𝓞 K)
    (w : α → ℝ) (v : β → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ A)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ B)
    (t : (α × α) × ((β × β) × (β × β))) :
    mixedSecondFourthCoefficient (coprimeRealWeight a x w) v t ≤
      A^2*B^4*mixedSecondFourthCoefficient (coprimeRealWeight a x (fun _ => 1)) (fun _ => 1) t := by
  by_cases h1 : IsUnit (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.1))
  · by_cases h2 : IsUnit (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) (x t.1.2))
    · simp only [mixedSecondFourthCoefficient,coprimeRealWeight,if_pos h1,if_pos h2,one_mul,mul_one]
      calc
        _ ≤ (A*A)*((B*B)*(B*B)) := by
          apply mul_le_mul
          · exact mul_le_mul (hw _) (hw _) (hw0 _) hA
          · exact mul_le_mul
              (mul_le_mul (hv _) (hv _) (hv0 _) hB)
              (mul_le_mul (hv _) (hv _) (hv0 _) hB)
              (mul_nonneg (hv0 _) (hv0 _)) (mul_nonneg hB hB)
          · exact mul_nonneg (mul_nonneg (hv0 _) (hv0 _)) (mul_nonneg (hv0 _) (hv0 _))
          · exact mul_nonneg hA hA
        _ = _ := by ring
    · simp only [mixedSecondFourthCoefficient,coprimeRealWeight,if_neg h2,mul_zero,zero_mul,le_refl]
  · simp only [mixedSecondFourthCoefficient,coprimeRealWeight,if_neg h1,zero_mul,mul_zero,le_refl]

theorem trace_coprime_mixed_sixth_le_unweighted
    (a : 𝓞 K) (x : α → 𝓞 K) (y : β → 𝓞 K)
    (w : α → ℝ) (v : β → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∀ i, w i ≤ A)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ B) :
    (∫ q, ‖traceCoprimeWeylSum a 3 x (fun i => (w i : ℂ)) q‖^2 *
      ‖traceWeylSum 3 y (fun i => (v i : ℂ)) (traceTorusMul a q)‖^4 ∂traceHaar) ≤
      A^2*B^4*(∫ q, ‖traceCoprimeWeylSum a 3 x (fun _ => 1) q‖^2 *
        ‖traceWeylSum 3 y (fun _ => 1) (traceTorusMul a q)‖^4 ∂traceHaar) := by
  have hu (q : ArchimedeanTraceTorus K) : traceCoprimeWeylSum a 3 x (fun _ => 1) q =
      traceWeylSum 3 x (fun i => (coprimeRealWeight a x (fun _ => 1) i : ℂ)) q := by
    simpa only [Complex.ofReal_one] using traceCoprimeWeylSum_real_mask a x (fun _ => 1) q
  simp_rw [traceCoprimeWeylSum_real_mask,hu]
  have h1 : (fun _ : β => (1 : ℂ)) = (fun _ : β => ((1 : ℝ) : ℂ)) := rfl
  rw [h1]
  rw [trace_second_fourth_integral,trace_second_fourth_integral,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hphase : mixedSecondFourthPhase a x y t=0
  · simp only [if_pos hphase]
    exact mixedSecondFourthCoefficient_mask_le a x w v A B hA hB hw0 hw hv0 hv t
  · simp only [if_neg hphase,mul_zero,le_refl]

#print axioms trace_coprime_mixed_sixth_le_unweighted
end WaringSiegel.WSL4Local

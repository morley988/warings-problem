import WaringSiegel.WSL4MixedCountSplit
import WaringSiegel.WSL2MomentFourthGrowth

/-! # The diagonal mixed count is the actual cubic fourth moment -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField Module
open scoped NumberField BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem cubicFourthBoxCount_eq_integral (Y : Finset (𝓞 K)) :
    (cubicFourthBoxCount Y : ℝ) =
      ∫ q, ‖traceWeylSum 3 (fun y : Y => (y : 𝓞 K)) (fun _ => 1) q‖^4 ∂traceHaar := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [traceWeylSum_norm_fourth_expansion]
  rw [traceFrequencySum_integral]
  simp only [cubicFourthBoxCount,card_subtype_eq_sum_indicator,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero,map_one,one_mul,cubicFourthBoxPhase]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> rfl

theorem cubicFourthBoxCount_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 1 ≤ R → ∀ Y : Finset (𝓞 K),
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y : K) ≤ R) →
      (cubicFourthBoxCount Y : ℝ) ≤ C*(R^finrank ℚ K : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hbound⟩ := numberField_fourth_moment_bound (K:=K) 3 (by norm_num) hε
  refine ⟨C,hC,fun R hR Y hY => ?_⟩
  rw [cubicFourthBoxCount_eq_integral,traceWeylSum_integral_norm_pow]
  simpa only [one_pow,mul_one] using hbound R hR (fun y : Y => (y : 𝓞 K))
    Subtype.val_injective (fun y v => hY y.val y.property v)
    (fun _ => (1 : ℂ)) 1 zero_le_one (fun _ => by norm_num)

theorem mixed_diagonal_box_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P M R : ℝ, 1 ≤ P → 1 ≤ M → 1 ≤ R →
      ∀ X A Y : Finset (𝓞 K),
      (∀ x ∈ X, ∀ v : InfinitePlace K, v (x : K) ≤ P) →
      (∀ m ∈ A, ∀ v : InfinitePlace K, v (m : K) ≤ M) →
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y : K) ≤ R) →
      (A.card*X.card*cubicFourthBoxCount Y : ℝ) ≤
        C*(M^finrank ℚ K)*(P^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+ε) := by
  obtain ⟨C,hC,hbound⟩ := cubicFourthBoxCount_bound (K:=K) hε
  let D : ℝ := 2*(3 : ℝ)^finrank ℚ K
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D^2*C,by positivity,fun P M R hP hM hR X A Y hX hA hY => ?_⟩
  have hxc : (X.card : ℝ) ≤ D*P^finrank ℚ K := integer_box_card_bound X P hP hX
  have hac : (A.card : ℝ) ≤ D*M^finrank ℚ K := integer_box_card_bound A M hM hA
  have hyc := hbound R hR Y hY
  calc
    _ ≤ (D*M^finrank ℚ K)*(D*P^finrank ℚ K)*(C*(R^finrank ℚ K : ℝ)^(2+ε)) :=
      mul_le_mul (mul_le_mul hac hxc (Nat.cast_nonneg _) (by positivity)) hyc
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

#print axioms cubicFourthBoxCount_bound
#print axioms mixed_diagonal_box_bound
end WaringSiegel.WSL4Local

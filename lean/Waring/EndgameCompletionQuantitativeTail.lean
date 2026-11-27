import Waring.EndgameCompletionWeightedEuler
import Waring.EndgameCompletionPruning

/-!
# Quantitative real-frequency and rational-model pruning tails

The oscillatory integral has explicit power decay. Its real-frequency
tail combines with the weighted Euler series to give the fixed normalized
rectangle-tail decay `N^(-1/(2k))`.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Waring.EndgameCompletion

theorem monomial_moment_tail_from_le (k s : ℕ) (hk : 1≤k) (hks : k<s)
    {A : ℝ} (hA : 0<A) :
    (∫ β in Set.Ioi A,‖monomialIntegral k 1 β‖^s)≤
      ((2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k))*A^(1-(s : ℝ)/(k : ℝ)) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsr : (k : ℝ)<s := by exact_mod_cast hks
  have hexp : -(s : ℝ)/(k : ℝ)< -1 := (div_lt_iff₀ hkpos).mpr (by linarith)
  have htail := integrableOn_Ioi_rpow_of_lt hexp hA
  calc
    _ ≤ ∫ β in Set.Ioi A,(2 : ℝ)^s*β^(-(s : ℝ)/(k : ℝ)) := by
      apply setIntegral_mono_on
        (integrable_monomial_moment k s hk hks (P := 1) zero_le_one).integrableOn
        (htail.const_mul ((2 : ℝ)^s)) measurableSet_Ioi
      intro β hβ
      exact monomial_integral_moment_tail_pointwise k s hk zero_le_one (hA.trans hβ)
    _ = _ := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt hexp hA]
      rw [show -(s : ℝ)/(k : ℝ)+1=1-(s : ℝ)/(k : ℝ) by ring]
      field_simp [hkpos.ne',sub_ne_zero.mpr hsr.ne',
        show -(s : ℝ)+(k : ℝ)≠0 by linarith]
      linear_combination mul_inv_cancel₀ (show -(s : ℝ)+(k : ℝ)≠0 by linarith)

theorem even_function_tail_integral (f : ℝ→ℝ) (hf : ∀ x,f (-x)=f x)
    {A : ℝ} (hA : 0≤A) :
    (∫ x in {x : ℝ|A < |x|},f x)=2*(∫ x in Set.Ioi A,f x) := by
  classical
  have hmeas : MeasurableSet {x : ℝ|A < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have habs (x : ℝ) : f |x|=f x := by
    rcases le_or_gt 0 x with hx|hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg hx,hf]
  have he : (fun x : ℝ=>(Set.Ioi A).indicator f |x|)=
      {x : ℝ|A < |x|}.indicator f := by
    funext x
    by_cases hx : A < |x|
    · simp only [Set.indicator_apply,Set.mem_Ioi,Set.mem_setOf_eq,if_pos hx,habs]
    · simp only [Set.indicator_apply,Set.mem_Ioi,Set.mem_setOf_eq,if_neg hx]
  have hh := integral_comp_abs (f := (Set.Ioi A).indicator f)
  rw [he,integral_indicator hmeas] at hh
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi,max_eq_left hA] at hh
  exact hh

theorem unitMonomialTail_explicit (k s N : ℕ) (hk : 1≤k) (hks : k<s) (hN : 1≤N) :
    unitMonomialTail k s N≤
      (2*(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k))*(N : ℝ)^(1-(s : ℝ)/(k : ℝ)) := by
  unfold unitMonomialTail
  rw [even_function_tail_integral (fun β=>‖monomialIntegral k 1 β‖^s)
    (fun β=>by dsimp only; rw [norm_monomialIntegral_neg k zero_le_one]) (Nat.cast_nonneg N)]
  exact (mul_le_mul_of_nonneg_left (monomial_moment_tail_from_le k s hk hks
    (by exact_mod_cast (show 0<N by omega))) (by norm_num : (0 : ℝ)≤2)).trans_eq (by ring)

def pruningRealTailConstant (k s : ℕ) : ℝ :=
  2*(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k)

theorem pruningRealTailConstant_nonneg (k s : ℕ) (hks : k≤s) :
    0≤pruningRealTailConstant k s := by
  unfold pruningRealTailConstant
  exact div_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hks))

theorem unitMonomialTail_le_pruningDecay (k s N : ℕ) (hk : 1≤k)
    (hks : k+2≤s) (hN : 1≤N) :
    unitMonomialTail k s N≤pruningRealTailConstant k s*(N : ℝ)^(-pruningDecay k) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsr : (k : ℝ)+2≤s := by exact_mod_cast hks
  have hkd := pruningDecay_mul (show 0<k by omega)
  have he : 1-(s : ℝ)/(k : ℝ)≤ -pruningDecay k := by
    apply (mul_le_mul_iff_right₀ hkpos).mp
    have hdiv := div_mul_cancel₀ (s : ℝ) hkpos.ne'
    nlinarith
  exact (unitMonomialTail_explicit k s N hk (by omega) hN).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) he) (pruningRealTailConstant_nonneg k s (by omega)))

theorem normalizedPruningModelMass_power_tail (k s : ℕ) (hk : 2≤k) (hks : k+2≤s)
    (hsum : Summable (completeCoefficient k s))
    (hweighted : Summable (weightedCompleteCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      normalizedPruningModelMass k s N≤C*(N : ℝ)^(-pruningDecay k) := by
  let U := ∫ β : ℝ,‖monomialIntegral k 1 β‖^s
  let T := pruningRealTailConstant k s
  let D := (∑' q : ℕ,weightedCompleteCoefficient k s q)*U+
    (∑' q : ℕ,completeCoefficient k s q)*T
  refine ⟨|D|+1,by positivity,?_⟩
  intro N hN
  have hU : 0≤U := integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) s)
  have hT : 0≤T := pruningRealTailConstant_nonneg k s (by omega)
  have htail := unitMonomialTail_le_pruningDecay k s N (by omega) hks hN
  let M := (N : ℝ)^(-pruningDecay k)
  have hM : 0≤M := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpoint (q : ℕ) : completeCoefficient k s q*
      (∫ β in {β : ℝ|N≤q ∨ (N : ℝ) < |β|},‖monomialIntegral k 1 β‖^s)≤
      M*(weightedCompleteCoefficient k s q*U+completeCoefficient k s q*T) := by
    by_cases hNq : N≤q
    · have he : {β : ℝ|N≤q ∨ (N : ℝ) < |β|}=Set.univ := by ext β; simp [hNq]
      rw [he,setIntegral_univ]
      have hcoef := completeCoefficient_tail_pointwise k s N q (by omega) hN
      rw [if_pos hNq] at hcoef
      calc
        _ ≤ (M*weightedCompleteCoefficient k s q)*U := mul_le_mul_of_nonneg_right hcoef hU
        _ ≤ _ := by
          nlinarith [mul_nonneg hM (mul_nonneg (completeCoefficient_nonneg k s q) hT)]
    · have he : {β : ℝ|N≤q ∨ (N : ℝ) < |β|}={β : ℝ|(N : ℝ) < |β|} := by ext β; simp [hNq]
      rw [he]
      change completeCoefficient k s q*unitMonomialTail k s N≤_
      calc
        _ ≤ completeCoefficient k s q*(T*M) :=
          mul_le_mul_of_nonneg_left htail (completeCoefficient_nonneg ..)
        _ ≤ _ := by
          nlinarith [mul_nonneg hM (mul_nonneg (weightedCompleteCoefficient_nonneg k s q) hU)]
  have hmajor : Summable (fun q : ℕ=>M*(weightedCompleteCoefficient k s q*U+
      completeCoefficient k s q*T)) := ((hweighted.mul_right U).add (hsum.mul_right T)).mul_left M
  have hnonneg (q : ℕ) : 0≤completeCoefficient k s q*
      (∫ β in {β : ℝ|N≤q ∨ (N : ℝ) < |β|},‖monomialIntegral k 1 β‖^s) :=
    mul_nonneg (completeCoefficient_nonneg ..) (integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) s))
  have hmodel := Summable.of_nonneg_of_le hnonneg hpoint hmajor
  have hh := hmodel.tsum_le_tsum hpoint hmajor
  rw [tsum_mul_left,(hweighted.mul_right U).tsum_add (hsum.mul_right T),
    tsum_mul_right,tsum_mul_right] at hh
  change normalizedPruningModelMass k s N≤M*D at hh
  exact hh.trans (by
    calc
      M*D≤M*(|D|+1) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self D]) hM
      _ = _ := by ring)

theorem degree8_normalizedPruningModelMass_power_tail :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      normalizedPruningModelMass 8 12 N≤C*(N : ℝ)^(-(1/16 : ℝ)) := by
  convert
    normalizedPruningModelMass_power_tail 8 12 (by norm_num) (by norm_num)
      (degree8_completeCoefficient_summable 12 (by norm_num))
      (degree8_weightedCompleteCoefficient_summable 12 (by norm_num)) using 1 <;>
    norm_num [pruningDecay]

theorem degree9_normalizedPruningModelMass_power_tail :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,1≤N →
      normalizedPruningModelMass 9 11 N≤C*(N : ℝ)^(-(1/18 : ℝ)) := by
  convert
    normalizedPruningModelMass_power_tail 9 11 (by norm_num) (by norm_num)
      (degree9_completeCoefficient_summable 11 (by norm_num))
      (degree9_weightedCompleteCoefficient_summable 11 (by norm_num)) using 1 <;>
    norm_num [pruningDecay]

#print axioms unitMonomialTail_le_pruningDecay
#print axioms degree8_normalizedPruningModelMass_power_tail
#print axioms degree9_normalizedPruningModelMass_power_tail
end Waring.EndgameCompletion

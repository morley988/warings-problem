import Waring.EndgameCompletionEuler
import Waring.EndgameCompletionSingular
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Full major-model moments and qualitative pruning

The complete-sum arithmetic series and the oscillatory integral are now
both proved integrable. Their product bounds the full rational model.
Removing a growing rectangle in denominator and scaled real frequency
leaves a model mass tending to zero, without a quantitative tail input.
-/

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Waring.EndgameCompletion

def ordinaryMajorModel (q : ℕ) [NeZero q] (k : ℕ) (P : ℝ) (a : ZMod q) (β : ℝ) : ℂ :=
  completeMonomialSumMod q k a/(q : ℂ)*monomialIntegral k P β

def ordinaryMajorModelMoment (q : ℕ) [NeZero q] (k s : ℕ) (P : ℝ) (A : Set ℝ) : ℝ :=
  ∑ a : (ZMod q)ˣ, ∫ β in A, ‖ordinaryMajorModel q k P a β‖^s

theorem ordinaryMajorModel_norm_pow (q : ℕ) [NeZero q] (k s : ℕ)
    (P : ℝ) (a : ZMod q) (β : ℝ) :
    ‖ordinaryMajorModel q k P a β‖^s =
      (normalizedCompleteSum q k a)^s*‖monomialIntegral k P β‖^s := by
  simp only [ordinaryMajorModel, norm_mul, norm_div, Complex.norm_natCast,
    mul_pow, normalizedCompleteSum]

/-- Exact separation into the arithmetic coefficient and real integral. -/
theorem ordinaryMajorModelMoment_factorization (q : ℕ) [NeZero q]
    (k s : ℕ) (P : ℝ) (A : Set ℝ) :
    ordinaryMajorModelMoment q k s P A =
      primitiveCompleteMoment q k s*(∫ β in A, ‖monomialIntegral k P β‖^s) := by
  unfold ordinaryMajorModelMoment primitiveCompleteMoment
  simp_rw [ordinaryMajorModel_norm_pow, integral_const_mul]
  rw [Finset.sum_mul]

theorem completeCoefficient_positive_tsum (k s : ℕ)
    (hsum : Summable (completeCoefficient k s)) :
    (∑' q : ℕ, completeCoefficient k s (q+1)) = ∑' q : ℕ, completeCoefficient k s q := by
  have hh := hsum.sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, completeCoefficient_zero, zero_add] using hh

theorem ordinaryMajorModel_total_factorization (k s : ℕ) (P : ℝ)
    (hsum : Summable (completeCoefficient k s)) :
    (∑' q : ℕ, ordinaryMajorModelMoment (q+1) k s P Set.univ) =
      (∑' q : ℕ, completeCoefficient k s q)*(∫ β : ℝ, ‖monomialIntegral k P β‖^s) := by
  simp_rw [ordinaryMajorModelMoment_factorization, setIntegral_univ,
    ← completeCoefficient_nezero]
  rw [tsum_mul_right, completeCoefficient_positive_tsum k s hsum]

def ordinaryMajorMomentConstant (k s : ℕ) : ℝ :=
  (∑' q : ℕ, completeCoefficient k s q)*
    (2*(1+(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k)))

theorem ordinaryMajorModel_total_le (k s : ℕ) (hk : 1 ≤ k) (hks : k < s)
    {P : ℝ} (hP : 0 < P) (hsum : Summable (completeCoefficient k s)) :
    (∑' q : ℕ, ordinaryMajorModelMoment (q+1) k s P Set.univ) ≤
      ordinaryMajorMomentConstant k s*P^(s-k) := by
  rw [ordinaryMajorModel_total_factorization k s P hsum]
  exact (mul_le_mul_of_nonneg_left (full_monomial_moment_le k s hk hks hP)
    (tsum_nonneg (completeCoefficient_nonneg k s))).trans_eq (by
      unfold ordinaryMajorMomentConstant
      ring)

theorem degree8_ordinaryMajorModel_total_le {P : ℝ} (hP : 0 < P) :
    (∑' q : ℕ, ordinaryMajorModelMoment (q+1) 8 12 P Set.univ) ≤
      ordinaryMajorMomentConstant 8 12*P^4 :=
  ordinaryMajorModel_total_le 8 12 (by norm_num) (by norm_num) hP
    (degree8_completeCoefficient_summable 12 (by norm_num))

theorem degree9_ordinaryMajorModel_total_le {P : ℝ} (hP : 0 < P) :
    (∑' q : ℕ, ordinaryMajorModelMoment (q+1) 9 11 P Set.univ) ≤
      ordinaryMajorMomentConstant 9 11*P^2 :=
  ordinaryMajorModel_total_le 9 11 (by norm_num) (by norm_num) hP
    (degree9_completeCoefficient_summable 11 (by norm_num))

def unitMonomialTail (k s N : ℕ) : ℝ :=
  ∫ β in {β : ℝ | (N : ℝ) < |β|}, ‖monomialIntegral k 1 β‖^s

theorem unitMonomialTail_tendsto_zero (k s : ℕ) (hk : 1 ≤ k) (hks : k < s) :
    Tendsto (unitMonomialTail k s) atTop (𝓝 0) := by
  have hmeas (N : ℕ) : MeasurableSet {β : ℝ | (N : ℝ) < |β|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hanti : Antitone (fun N : ℕ => {β : ℝ | (N : ℝ) < |β|}) := by
    intro N M hNM β hβ
    exact lt_of_le_of_lt (show (N : ℝ) ≤ (M : ℝ) by exact_mod_cast hNM) hβ
  have hempty : (⋂ N : ℕ, {β : ℝ | (N : ℝ) < |β|})=∅ := by
    ext β
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hall
    obtain ⟨N,hN⟩ := exists_nat_ge |β|
    exact (not_lt_of_ge hN) (hall N)
  have hh := tendsto_setIntegral_of_antitone hmeas hanti
    ⟨0, (integrable_monomial_moment k s hk hks (P := 1) zero_le_one).integrableOn⟩
  simpa [hempty, unitMonomialTail] using hh

/-- Total normalized model mass outside the rectangle `q<N`, `|β|≤N`.
For positive q, the summand equals the sum of actual model integrals by
`ordinaryMajorModelMoment_factorization`; the q=0 term is zero. -/
def normalizedPruningModelMass (k s N : ℕ) : ℝ :=
  ∑' q : ℕ, completeCoefficient k s q*
    ∫ β in {β : ℝ | N ≤ q ∨ (N : ℝ) < |β|}, ‖monomialIntegral k 1 β‖^s

/-- Actual qualitative pruning for the ordinary rational model, obtained
from the proved arithmetic and real-variable integrability. -/
theorem normalizedPruningModelMass_tendsto_zero (k s : ℕ)
    (hk : 1 ≤ k) (hks : k < s) (hsum : Summable (completeCoefficient k s)) :
    Tendsto (normalizedPruningModelMass k s) atTop (𝓝 0) := by
  have hi := integrable_monomial_moment k s hk hks (P := 1) zero_le_one
  have hpos (β : ℝ) : 0 ≤ ‖monomialIntegral k 1 β‖^s := pow_nonneg (norm_nonneg _) _
  have hbound : Summable (fun q => completeCoefficient k s q*
      ∫ β : ℝ, ‖monomialIntegral k 1 β‖^s) := hsum.mul_right _
  have hpoint (q : ℕ) : Tendsto
      (fun N : ℕ => completeCoefficient k s q*
        ∫ β in {β : ℝ | N ≤ q ∨ (N : ℝ) < |β|}, ‖monomialIntegral k 1 β‖^s)
      atTop (𝓝 (0 : ℝ)) := by
    have hh := (unitMonomialTail_tendsto_zero k s hk hks).const_mul (completeCoefficient k s q)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop q] with N hN
    simp only [unitMonomialTail, Nat.not_le.mpr hN, false_or]
  have h := tendsto_tsum_of_dominated_convergence hbound hpoint (Filter.Eventually.of_forall (by
    intro N q
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (completeCoefficient_nonneg k s q)
      (integral_nonneg hpos))]
    exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hi (Filter.Eventually.of_forall hpos))
      (completeCoefficient_nonneg k s q)))
  simpa only [tsum_zero] using h

theorem degree8_normalizedPruningModelMass_tendsto_zero :
    Tendsto (normalizedPruningModelMass 8 12) atTop (𝓝 0) :=
  normalizedPruningModelMass_tendsto_zero 8 12 (by norm_num) (by norm_num)
    (degree8_completeCoefficient_summable 12 (by norm_num))

theorem degree9_normalizedPruningModelMass_tendsto_zero :
    Tendsto (normalizedPruningModelMass 9 11) atTop (𝓝 0) :=
  normalizedPruningModelMass_tendsto_zero 9 11 (by norm_num) (by norm_num)
    (degree9_completeCoefficient_summable 11 (by norm_num))

#print axioms degree8_ordinaryMajorModel_total_le
#print axioms degree9_ordinaryMajorModel_total_le
#print axioms degree8_normalizedPruningModelMass_tendsto_zero
#print axioms degree9_normalizedPruningModelMass_tendsto_zero

end Waring.EndgameCompletion

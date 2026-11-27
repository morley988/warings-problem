import Waring.PolicyCompletionMajorHeight
import Waring.CartesianFloorScales
import Waring.CoefficientPower

/-! # Exact source height and coefficient boxes, with all floors retained -/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMajorBoxRanges
open CartesianProductSampling ProductMultiplicity PolicyCompletionMajorFamily
open PolicyCompletionPhaseContent IntegerDifferencePolynomial CoefficientPower SmoothMoments

def boxHeights {j : ℕ} (k : ℕ) (L : ℝ) (M : Fin j → ℝ) (i : Fin j) : ℝ := L/(M i)^k

def boxHeightBounds {j : ℕ} (k : ℕ) (L : ℝ) (M : Fin j → ℝ) : Fin j → ℕ :=
  fun i => ⌊boxHeights k L M i⌋₊

def boxCoefficientTuples {j : ℕ} (Q R : ℝ) (M : Fin j → ℝ) : Finset (Fin j → ℕ) :=
  Fintype.piFinset (fun i => coefficientBlock Q R (M i))

def boxSourceFamily {j : ℕ} (k : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) (α : ℝ) : ℂ :=
  sourceFamily k (positiveBox (boxHeightBounds k L M)) (boxCoefficientTuples Q R M) L α

def boxConductor {j : ℕ} (k : ℕ) (L : ℝ) (M : Fin j → ℝ) : ℝ := L^k/(∏ i, M i)^k

theorem boxHeights_pos {j : ℕ} (k : ℕ) {L : ℝ} {M : Fin j → ℝ}
    (hL : 0<L) (hM : ∀ i, 0<M i) (i : Fin j) : 0<boxHeights k L M i :=
  div_pos hL (pow_pos (hM i) k)

theorem boxHeightBounds_pos {j : ℕ} (k : ℕ) {L : ℝ} {M : Fin j → ℝ}
    (hH : ∀ i, 2≤boxHeights k L M i) (i : Fin j) : 0<boxHeightBounds k L M i := by
  apply Nat.floor_pos.mpr
  linarith [hH i]

theorem boxHeightVolume_sandwich {j : ℕ} (k : ℕ) {L : ℝ} {M : Fin j → ℝ}
    (hL : 0<L) (hM : ∀ i, 0<M i) (hH : ∀ i, 2≤boxHeights k L M i) :
    (∏ i, boxHeights k L M i)/(2:ℝ)^j ≤ (tupleProduct (boxHeightBounds k L M):ℝ) ∧
      (tupleProduct (boxHeightBounds k L M):ℝ)≤∏ i,boxHeights k L M i := by
  have hc : (tupleProduct (boxHeightBounds k L M):ℝ)=∏ i,(⌊boxHeights k L M i⌋₊:ℝ) := by
    simp only [tupleProduct,boxHeightBounds,Nat.cast_prod]
  rw [hc]
  constructor
  · have hh := Finset.prod_le_prod
      (fun i (_ : i∈(Finset.univ : Finset (Fin j))) => div_nonneg (boxHeights_pos k hL hM i).le (by norm_num))
      (fun i _ => CartesianFloorScales.half_le_floor (hH i))
    simpa only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  · exact Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => Nat.floor_le (boxHeights_pos k hL hM i).le)

theorem boxHeightVolume_power_bound {j : ℕ} (k : ℕ) {L : ℝ} {M : Fin j → ℝ}
    (hL : 1≤L) (hM : ∀ i,1≤M i) :
    (tupleProduct (boxHeightBounds k L M):ℝ)≤L^j := by
  have hb (i : Fin j) : (boxHeightBounds k L M i:ℝ)≤L := by
    apply (Nat.floor_le (div_nonneg (zero_le_one.trans hL)
      (pow_nonneg (zero_le_one.trans (hM i)) k))).trans
    exact div_le_self (zero_le_one.trans hL) (one_le_pow₀ (hM i))
  have hp := Finset.prod_le_prod (fun i (_ : i∈(Finset.univ : Finset (Fin j))) =>
    (Nat.cast_nonneg (boxHeightBounds k L M i): (0:ℝ)≤_)) (fun i _ => hb i)
  simpa only [tupleProduct,Nat.cast_prod,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hp

theorem boxHeightVolume_conductor {j k : ℕ} (hj : j≤k) (L : ℝ) (M : Fin j → ℝ) :
    L^(k-j)*(∏ i,boxHeights k L M i)=boxConductor k L M := by
  unfold boxHeights boxConductor
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ← Finset.prod_pow,← mul_div_assoc,← pow_add,Nat.sub_add_cancel hj]

theorem boxCoefficientTuples_pos {j : ℕ} (Q R : ℝ) (M : Fin j → ℝ)
    {m : Fin j → ℕ} (hm : m∈boxCoefficientTuples Q R M) (i : Fin j) : 0<m i := by
  have hi := Fintype.mem_piFinset.mp hm i
  exact (mem_smoothNumbers.mp (Finset.mem_filter.mp hi).1).1.1

theorem boxCoefficientTuples_le {j : ℕ} (Q R : ℝ) (M : Fin j → ℝ)
    {m : Fin j → ℕ} (hm : m∈boxCoefficientTuples Q R M) (i : Fin j) : (m i:ℝ)≤M i*R :=
  (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hm i)).2.2

theorem boxCoefficientTuples_card_le {j : ℕ} (Q : ℝ) {R : ℝ} {M : Fin j → ℝ}
    (hR : 0≤R) (hM : ∀ i,0≤M i) :
    ((boxCoefficientTuples Q R M).card:ℝ)≤(∏ i,M i)*R^j := by
  have hc (i : Fin j) : ((coefficientBlock Q R (M i)).card:ℝ)≤M i*R := by
    calc
      _ ≤ ((smoothNumbers (M i*R) R).card:ℝ) := by exact_mod_cast Finset.card_le_card (coefficientBlock_subset Q R (M i))
      _ ≤ (⌊M i*R⌋₊:ℝ) := by exact_mod_cast smoothNumbers_card_le (M i*R) R
      _ ≤ _ := Nat.floor_le (mul_nonneg (hM i) hR)
  simp only [boxCoefficientTuples,Fintype.card_piFinset,Nat.cast_prod]
  calc
    _ ≤ ∏ i,M i*R := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hc i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem naturalParameters_shiftRadius {j : ℕ} (k : ℕ) (h m : Fin j → ℕ) :
    shiftRadius k (naturalParameters h m)=∑ i,(h i:ℝ)*(m i:ℝ)^k := by
  simp [shiftRadius,naturalParameters,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    Int.cast_natCast]

theorem box_shiftRadius_le {j : ℕ} (k : ℕ) {L Q R : ℝ} {M : Fin j → ℝ}
    (hL : 0<L) (hR : 0≤R) (hM : ∀ i,0<M i)
    {h m : Fin j → ℕ} (hh : h∈positiveBox (boxHeightBounds k L M))
    (hm : m∈boxCoefficientTuples Q R M) :
    shiftRadius k (naturalParameters h m)≤(j:ℝ)*L*R^k := by
  rw [naturalParameters_shiftRadius]
  have hterm (i : Fin j) : (h i:ℝ)*(m i:ℝ)^k≤L*R^k := by
    have hh' : (h i:ℝ)≤boxHeights k L M i :=
      (by exact_mod_cast (mem_positiveBox.mp hh i).2 : (h i:ℝ)≤boxHeightBounds k L M i).trans
        (Nat.floor_le (boxHeights_pos k hL hM i).le)
    have hm' := boxCoefficientTuples_le Q R M hm i
    calc
      _ ≤ (L/(M i)^k)*(M i*R)^k := mul_le_mul hh'
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hm' k) (by positivity)
          (div_nonneg hL.le (pow_nonneg (hM i).le k))
      _ = L*R^k := by rw [mul_pow]; field_simp [(hM i).ne']
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin j))) (fun i _ => hterm i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hs

#print axioms boxHeightVolume_sandwich
#print axioms boxHeightVolume_conductor
#print axioms boxCoefficientTuples_card_le
#print axioms box_shiftRadius_le
end Waring.PolicyCompletionMajorBoxRanges

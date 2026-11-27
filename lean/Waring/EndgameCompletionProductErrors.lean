import Waring.EndgameCompletionProductPruning
import Waring.EndgameCompletionProductMinor

/-! # Vanishing product-weight pruning and minor errors at polynomial cutoffs -/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped Topology ENNReal
namespace Waring.EndgameCompletion
open MixedEndgame

def powerCutoff (κ P : ℝ) : ℕ := ⌊P^κ⌋₊

theorem powerCutoff_bounds {κ P : ℝ} (hκ0 : 0≤κ) (hκ1 : κ≤1) (hP : 1≤P) :
    1≤powerCutoff κ P ∧ (powerCutoff κ P : ℝ)≤P := by
  have hpκ := Real.rpow_nonneg (zero_le_one.trans hP) κ
  constructor
  · apply (Nat.le_floor_iff hpκ).mpr
    simpa only [Nat.cast_one] using Real.one_le_rpow hP hκ0
  · exact (Nat.floor_le hpκ).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hκ1)

theorem powerCutoff_half {κ P : ℝ} (hPκ : 2≤P^κ) :
    P^κ/2≤(powerCutoff κ P : ℝ) := by
  have hh := Nat.sub_one_lt_floor (P^κ)
  change P^κ/2≤(⌊P^κ⌋₊ : ℝ)
  linarith

theorem cutoff_negative_power {P κ δ : ℝ} (hP : 0<P) (hδ : 0≤δ)
    (N : ℕ) (hN : P^κ/2≤(N : ℝ)) :
    (N : ℝ)^(-δ)≤(2 : ℝ)^δ*P^(-κ*δ) := by
  have hpκ : 0<P^κ := Real.rpow_pos_of_pos hP _
  calc
    _ ≤ (P^κ/2)^(-δ) :=
      Real.rpow_le_rpow_of_nonpos (div_pos hpκ (by norm_num)) hN (neg_nonpos.mpr hδ)
    _ = _ := by
      rw [Real.div_rpow hpκ.le (by norm_num),← Real.rpow_mul hP.le,
        Real.rpow_neg (by norm_num : (0 : ℝ)≤2),div_inv_eq_mul]
      rw [mul_comm]
      congr 2
      ring

theorem product_pruning8_isLittleO (L : ℕ) {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (M : ℕ→ℕ) (hM : ∀ᶠ n in atTop,1≤M n)
    (hP : Tendsto (fun n=>(M n : ℝ)^L) atTop atTop) :
    (fun n=>productArcContribution 8 8 30 L (M n) n
      (ordinaryPruning 8 ((M n : ℝ)^L) (powerCutoff κ ((M n : ℝ)^L))))=o[atTop]
      (fun n=>((M n : ℝ)^L)^(30 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := product_pruning8_quantitative L (show 0<κ/48 by positivity)
  apply AsymptoticEndgame.power_saving_isLittleO (saving := κ/48) (by positivity) hP
  apply IsBigO.of_bound (C*(2 : ℝ)^(1/24 : ℝ))
  have hlarge := ((tendsto_rpow_atTop hκ).comp hP).eventually_ge_atTop 2
  filter_upwards [hM,hP.eventually_ge_atTop 1,hlarge] with n hMn hPn hlarge_n
  let P : ℝ := (M n : ℝ)^L
  have hp : 0<P := zero_lt_one.trans_le hPn
  have hN := powerCutoff_bounds hκ.le hκ1 hPn
  have hb := hbound (M n) hMn (powerCutoff κ P) hN.1 hN.2 n
  have ht := cutoff_negative_power hp (by norm_num : (0 : ℝ)≤1/24)
    (powerCutoff κ P) (powerCutoff_half hlarge_n)
  have he : C*P^(30+κ/48)*((2 : ℝ)^(1/24 : ℝ)*P^(-κ*(1/24)))=
      (C*(2 : ℝ)^(1/24 : ℝ))*P^(30-κ/48) := by
    rw [show C*P^(30+κ/48)*((2 : ℝ)^(1/24 : ℝ)*P^(-κ*(1/24)))=
      (C*(2 : ℝ)^(1/24 : ℝ))*(P^(30+κ/48)*P^(-κ*(1/24))) by ring,
      ← Real.rpow_add hp]
    congr 2
    ring
  have hh := hb.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq he)
  simpa only [P,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (show 0≤(M n : ℝ)^L by positivity) _)] using hh

theorem product_pruning9_isLittleO (L : ℕ) {κ : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (M : ℕ→ℕ) (hM : ∀ᶠ n in atTop,1≤M n)
    (hP : Tendsto (fun n=>(M n : ℝ)^L) atTop atTop) :
    (fun n=>productArcContribution 9 11 35 L (M n) n
      (ordinaryPruning 9 ((M n : ℝ)^L) (powerCutoff κ ((M n : ℝ)^L))))=o[atTop]
      (fun n=>((M n : ℝ)^L)^(37 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := product_pruning9_quantitative
  apply AsymptoticEndgame.power_saving_isLittleO (saving := κ/18) (by positivity) hP
  apply IsBigO.of_bound (C*(2 : ℝ)^(1/18 : ℝ))
  have hlarge := ((tendsto_rpow_atTop hκ).comp hP).eventually_ge_atTop 2
  filter_upwards [hM,hP.eventually_ge_atTop 1,hlarge] with n hMn hPn hlarge_n
  let P : ℝ := (M n : ℝ)^L
  have hp : 0<P := zero_lt_one.trans_le hPn
  have hN := powerCutoff_bounds hκ.le hκ1 hPn
  have hb := hbound L (M n) hMn (powerCutoff κ P) hN.1 hN.2 n
  have ht := cutoff_negative_power hp (by norm_num : (0 : ℝ)≤1/18)
    (powerCutoff κ P) (powerCutoff_half hlarge_n)
  have he : C*P^(37 : ℝ)*((2 : ℝ)^(1/18 : ℝ)*P^(-κ*(1/18)))=
      (C*(2 : ℝ)^(1/18 : ℝ))*P^(37-κ/18) := by
    rw [show C*P^(37 : ℝ)*((2 : ℝ)^(1/18 : ℝ)*P^(-κ*(1/18)))=
      (C*(2 : ℝ)^(1/18 : ℝ))*(P^(37 : ℝ)*P^(-κ*(1/18))) by ring,
      ← Real.rpow_add hp]
    congr 2
    ring
  have hh := hb.trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq he)
  simpa only [P,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (show 0≤(M n : ℝ)^L by positivity) _)] using hh

def ordinaryCore (k : ℕ) (P : ℝ) (N : ℕ) : Set ℝ :=
  ordinaryBroadMajor k P∩rectangleCoreGlobal k P N

theorem ordinary_arc_partition (k : ℕ) (P : ℝ) (N : ℕ) :
    ArcPartition (ordinaryCore k P N) (ordinaryPruning k P N) (ordinaryMinorRegion k P) := by
  refine ⟨(ordinaryBroadMajor_measurable k P).inter (rectangleCoreGlobal_measurable k P N),
    ordinaryPruning_measurable k P N,ordinaryMinorRegion_measurable k P,?_,?_,?_,?_⟩
  · exact Set.disjoint_left.mpr (fun _ h1 h2=>h2.2 h1.2)
  · exact Set.disjoint_left.mpr (fun _ h1 h2=>h2.2 h1.1)
  · exact Set.disjoint_left.mpr (fun _ h1 h2=>h2.2 h1.1)
  · ext α
    constructor
    · rintro (h|h|h)
      · exact ordinaryBroadMajor_subset k P h.1
      · exact ordinaryPruning_subset k P N h
      · exact h.1
    · intro h
      by_cases hb : α∈ordinaryBroadMajor k P
      · by_cases hc : α∈rectangleCoreGlobal k P N
        · exact Or.inl ⟨hb,hc⟩
        · exact Or.inr (Or.inl ⟨hb,hc⟩)
      · exact Or.inr (Or.inr ⟨h,hb⟩)

#print axioms product_pruning8_isLittleO
#print axioms product_pruning9_isLittleO
#print axioms ordinary_arc_partition
end Waring.EndgameCompletion

import Waring.RationalHeightMin
import Waring.ShortHeightDistribution
import Waring.FiniteSpacing
import Waring.GeometricSums
import Waring.ReciprocalSums
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual short-height witnesses and divisor-weighted counting

Each small intrinsic height supplies an actual minimizing reduced rational.
Grouping the resulting product `h*q` loses at most the number of its positive
divisors. The divisor bound is an explicit parameter; no `P^epsilon` estimate
is asserted without a proof.
-/

noncomputable section

open scoped BigOperators

namespace Waring.ShortHeightCounting

open FiniteSpacing ShortHeightDistribution

/-- A sufficiently small distance saturates the truncated reciprocal weight,
including the zero-distance branch. -/
theorem truncatedReciprocal_eq_cap {a x : ℝ} (_ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    truncatedReciprocal a x = 1 / a := by
  unfold truncatedReciprocal
  split_ifs with hz
  · rfl
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
    exact min_eq_left (one_div_le_one_div_of_le hxpos hxa)

/-- Counting a family of products by nonnegative target weights, with an
explicit divisor-multiplicity bound. Only finite sums and actual divisors
occur in this grouping step. -/
theorem weighted_product_count (s : Finset ℕ) (q : ℕ → ℕ) (A : ℕ) (w : ℕ → ℝ)
    {D : ℝ} (hmaps : ∀ h ∈ s, h * q h ∈ Finset.Icc 1 A)
    (hw : ∀ n ∈ Finset.Icc 1 A, 0 ≤ w n)
    (hone : ∀ h ∈ s, 1 ≤ w (h * q h))
    (hD : ∀ n ∈ Finset.Icc 1 A, (n.divisors.card : ℝ) ≤ D) :
    (s.card : ℝ) ≤ D * ∑ n ∈ Finset.Icc 1 A, w n := by
  classical
  have hfiber (n : ℕ) (hn : n ∈ Finset.Icc 1 A) :
      ((s.filter (fun h => h * q h = n)).card : ℝ) ≤ D := by
    have hsubset : s.filter (fun h => h * q h = n) ⊆ n.divisors := by
      intro h hh
      have heq := (Finset.mem_filter.mp hh).2
      exact Nat.mem_divisors.mpr ⟨⟨q h, heq.symm⟩, by have := (Finset.mem_Icc.mp hn).1; omega⟩
    exact (show ((s.filter (fun h => h * q h = n)).card : ℝ) ≤
      (n.divisors.card : ℝ) by exact_mod_cast Finset.card_le_card hsubset).trans (hD n hn)
  calc
    (s.card : ℝ) = ∑ h ∈ s, (1 : ℝ) := by simp
    _ ≤ ∑ h ∈ s, w (h * q h) := Finset.sum_le_sum hone
    _ = ∑ n ∈ Finset.Icc 1 A, ((s.filter (fun h => h * q h = n)).card : ℝ) * w n := by
      rw [← Finset.sum_fiberwise_of_maps_to' hmaps w]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 A, D * w n :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_right (hfiber n hn) (hw n hn))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Exact reduction of the actual short-height count to a reciprocal sum,
with cutoff `floor(H*Y)` and real reciprocal cap `P^2/Y`. -/
theorem short_height_count_le_divisor_reciprocal (s : Finset ℕ)
    {H P α Y D : ℝ} (hH : 0 ≤ H) (hP : 0 < P) (hY : 0 < Y)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hD : ∀ n ∈ Finset.Icc 1 ⌊H * Y⌋₊, (n.divisors.card : ℝ) ≤ D) :
    heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
      D * (Y / P ^ 2) * ∑ n ∈ Finset.Icc 1 ⌊H * Y⌋₊,
        truncatedReciprocal (Y / P ^ 2) (integerDistance (α * (n : ℝ))) := by
  classical
  let good : Finset ℕ := s.filter (fun h : ℕ => RationalHeight.height (P ^ 2) ((h : ℝ) * α) ≤ Y)
  let r : ℕ → ℚ := fun h => Classical.choose
    (RationalHeight.exists_minimizer (sq_pos_of_pos hP) ((h : ℝ) * α))
  have hr (h : ℕ) : RationalHeight.cost (P ^ 2) ((h : ℝ) * α) (r h) =
      RationalHeight.height (P ^ 2) ((h : ℝ) * α) :=
    Classical.choose_spec (RationalHeight.exists_minimizer (sq_pos_of_pos hP) ((h : ℝ) * α))
  let q : ℕ → ℕ := fun h => (r h).den
  have hcost (h : ℕ) (hh : h ∈ good) :
      RationalHeight.cost (P ^ 2) ((h : ℝ) * α) (r h) ≤ Y :=
    (hr h).trans_le (Finset.mem_filter.mp hh).2
  have hqY (h : ℕ) (hh : h ∈ good) : (q h : ℝ) ≤ Y :=
    (le_max_left _ _).trans (hcost h hh)
  have hmaps : ∀ h ∈ good, h * q h ∈ Finset.Icc 1 ⌊H * Y⌋₊ := by
    intro h hh
    have hhs := hs h (Finset.mem_filter.mp hh).1
    refine Finset.mem_Icc.mpr ⟨Nat.mul_pos hhs.1 (r h).pos, ?_⟩
    apply Nat.le_floor
    push_cast
    exact mul_le_mul hhs.2 (hqY h hh) (by positivity) hH
  have hdist (h : ℕ) (hh : h ∈ good) : integerDistance (α * (h * q h : ℕ)) ≤ Y / P ^ 2 := by
    have he : P ^ 2 * |((r h).den : ℝ) * ((h : ℝ) * α) - ((r h).num : ℝ)| ≤ Y :=
      (le_max_right _ _).trans (hcost h hh)
    have he' : |((r h).den : ℝ) * ((h : ℝ) * α) - ((r h).num : ℝ)| ≤ Y / P ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hP)).mpr
      simpa only [mul_comm] using he
    have hphase : α * (h * q h : ℕ) = ((r h).den : ℝ) * ((h : ℝ) * α) := by
      dsimp [q]
      push_cast
      ring
    rw [hphase]
    exact (round_le _ (r h).num).trans he'
  have ha : 0 < Y / P ^ 2 := div_pos hY (sq_pos_of_pos hP)
  have hweighted := weighted_product_count good q ⌊H * Y⌋₊
    (fun n => (Y / P ^ 2) * truncatedReciprocal (Y / P ^ 2)
      (integerDistance (α * (n : ℝ)))) hmaps
    (fun n _ => mul_nonneg ha.le (truncatedReciprocal_nonneg ha (abs_nonneg _)))
    (by
      intro h hh
      change 1 ≤ (Y / P ^ 2) * truncatedReciprocal (Y / P ^ 2)
        (integerDistance (α * (h * q h : ℕ)))
      rw [truncatedReciprocal_eq_cap (x := integerDistance (α * (h * q h : ℕ)))
        ha (abs_nonneg _) (hdist h hh)]
      exact le_of_eq (by field_simp)) hD
  change (good.card : ℝ) ≤ _
  calc
    _ ≤ D * ∑ n ∈ Finset.Icc 1 ⌊H * Y⌋₊,
        (Y / P ^ 2) * truncatedReciprocal (Y / P ^ 2) (integerDistance (α * (n : ℝ))) := hweighted
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The actual Q2 estimate, derived from short rational witnesses, divisor
grouping, the proved reciprocal sum and rational transference. The sole
number-theoretic parameter left is the explicit divisor-count bound `D`.
The dyadic factor is common to all `0 < Y ≤ P^2`.
-/
theorem short_height_count_q2 (s : Finset ℕ) (T : ℕ)
    {H P α Y D : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hY : 0 < Y) (hYP : Y ≤ P ^ 2)
    (hD0 : 0 ≤ D) (hPT : P ^ 2 ≤ (2 : ℝ) ^ T)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hD : ∀ n ∈ Finset.Icc 1 ⌊H * Y⌋₊, (n.divisors.card : ℝ) ≤ D) :
    let L := RationalHeight.height (H * P ^ 2) α
    heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
      (256 * D * (T + 1 : ℕ)) *
        (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2) := by
  classical
  let L := RationalHeight.height (H * P ^ 2) α
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hLpos : 0 < L := RationalHeight.height_pos _ _
  by_cases hY1 : 1 ≤ Y
  · let N : ℕ := ⌊H * Y⌋₊ + 1
    let J : ℝ := P ^ 2 / Y
    let a : ℝ := Y / P ^ 2
    let V : ℝ := (N : ℝ) * J
    let L' := RationalHeight.height V α
    have hN : 0 < N := by dsimp [N]; omega
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hJ : 1 ≤ J := (le_div_iff₀ hY).mpr (by simpa only [one_mul] using hYP)
    have hJpos : 0 < J := zero_lt_one.trans_le hJ
    have hJP : J ≤ P ^ 2 := by
      apply (div_le_iff₀ hY).mpr
      nlinarith [mul_le_mul_of_nonneg_left hY1 (sq_nonneg P)]
    have ha : 0 < a := div_pos hY (sq_pos_of_pos hPpos)
    have haJ : 1 / J = a := by dsimp [J, a]; field_simp
    have hHY : 1 ≤ H * Y := by nlinarith
    have hNlo : H * Y ≤ (N : ℝ) := by
      exact (Nat.lt_floor_add_one (H * Y)).le.trans_eq (by simp [N])
    have hNhi : (N : ℝ) ≤ 2 * (H * Y) := by
      have hfloor := Nat.floor_le (zero_le_one.trans hHY)
      dsimp [N]
      push_cast
      linarith
    have hVpos : 0 < V := mul_pos (by exact_mod_cast hN) hJpos
    have hV0pos : 0 < H * P ^ 2 := mul_pos hHpos (sq_pos_of_pos hPpos)
    have hVlo : H * P ^ 2 ≤ V := by
      have hh := mul_le_mul_of_nonneg_right hNlo hJpos.le
      convert hh using 1
      dsimp [J, V]
      field_simp
    have hVhi : V ≤ 2 * (H * P ^ 2) := by
      have hh := mul_le_mul_of_nonneg_right hNhi hJpos.le
      convert hh using 1
      dsimp [J, V]
      field_simp
    have hLL' : L ≤ L' := RationalHeight.height_mono_conductor (α := α) hVpos hVlo
    have hL'hi : L' ≤ 2 * L := by
      apply (RationalHeight.height_mono_conductor (α := α)
        (mul_pos (by norm_num) hV0pos) hVhi).trans
      simpa only [Nat.cast_one, one_mul] using
        RationalHeight.height_mul_lift (α := α) hV0pos.le (h := 1) (by decide) (by norm_num : ((1 : ℕ) : ℝ) ≤ 2)
    have hL'pos : 0 < L' := RationalHeight.height_pos _ _
    have hrecip := ReciprocalSums.reciprocal_sum_intrinsic_real α N J T hN hJ (hJP.trans hPT)
    rw [haJ] at hrecip
    have hpad : (∑ n ∈ Finset.Icc 1 ⌊H * Y⌋₊,
        truncatedReciprocal a (integerDistance (α * (n : ℝ)))) ≤
      ∑ n ∈ Finset.range N, truncatedReciprocal a (integerDistance (α * (n : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        apply Finset.mem_range.mpr
        have hn' := (Finset.mem_Icc.mp hn).2
        dsimp [N]
        omega
      · intro n _hn _hnot
        exact truncatedReciprocal_nonneg ha (abs_nonneg _)
    have hfirst : a * (V / L') ≤ 2 * H * Y / L := by
      calc
        a * (V / L') = (N : ℝ) / L' := by dsimp [a, V, J]; field_simp
        _ ≤ (N : ℝ) / L := div_le_div_of_nonneg_left hN0 hLpos hLL'
        _ ≤ 2 * (H * Y) / L := div_le_div_of_nonneg_right hNhi hLpos.le
        _ = _ := by ring
    have hsecond : a * (N : ℝ) ≤ 2 * H * Y ^ 2 / P ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hNhi ha.le
      convert hh using 1
      dsimp [a]
      ring
    have hthird : a * J = 1 := by dsimp [a, J]; field_simp
    have hfourth : a * L' ≤ 2 * L * Y / P ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hL'hi ha.le
      convert hh using 1
      dsimp [a]
      ring
    have hscalar : a * (V / L' + N + J + L') ≤
        2 * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2) := by
      calc
        _ = a * (V / L') + a * N + a * J + a * L' := by ring
        _ ≤ 2 * H * Y / L + 2 * H * Y ^ 2 / P ^ 2 + 1 + 2 * L * Y / P ^ 2 :=
          add_le_add (add_le_add (add_le_add hfirst hsecond) hthird.le) hfourth
        _ ≤ 2 * H * Y / L + 2 * H * Y ^ 2 / P ^ 2 + 1 + 2 * L * Y / P ^ 2 + 1 :=
          le_add_of_nonneg_right (by norm_num)
        _ = _ := by ring
    have hbase := short_height_count_le_divisor_reciprocal s (α := α) hHpos.le hPpos hY hs hD
    calc
      _ ≤ D * a * ∑ n ∈ Finset.Icc 1 ⌊H * Y⌋₊,
          truncatedReciprocal a (integerDistance (α * (n : ℝ))) := hbase
      _ ≤ D * a * (128 * (V / L' + N + J + L') * (T + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (hpad.trans hrecip) (mul_nonneg hD0 ha.le)
      _ = (128 * D * (T + 1 : ℕ)) * (a * (V / L' + N + J + L')) := by ring
      _ ≤ (128 * D * (T + 1 : ℕ)) *
          (2 * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2)) :=
        mul_le_mul_of_nonneg_left hscalar (by positivity)
      _ = _ := by ring
  · have hYlt : Y < 1 := lt_of_not_ge hY1
    have hempty : (s.filter (fun h : ℕ => RationalHeight.height (P ^ 2) ((h : ℝ) * α) ≤ Y)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro h _hh hsmall
      have h1 := RationalHeight.one_le_height (P ^ 2) ((h : ℝ) * α)
      linarith
    simp only [heightCount, hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Q2 with the dyadic depth replaced by an explicit logarithm. The divisor
parameter is still visible, and there is no hidden epsilon loss. -/
theorem short_height_count_q2_log (s : Finset ℕ)
    {H P α Y D : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hY : 0 < Y) (hYP : Y ≤ P ^ 2)
    (hD0 : 0 ≤ D) (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hD : ∀ n ∈ Finset.Icc 1 ⌊H * Y⌋₊, (n.divisors.card : ℝ) ≤ D) :
    let L := RationalHeight.height (H * P ^ 2) α
    heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
      (256 * D * (2 + 2 * Real.log P / Real.log 2)) *
        (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  obtain ⟨T, hcover, hcover2⟩ := exists_dyadic_cover zero_lt_one hP2
  simp only [one_mul] at hcover hcover2
  have hdepth := dyadic_depth_le_log (a := 1) T le_rfl (sq_pos_of_pos hPpos)
    (by simpa only [one_mul] using hcover2)
  rw [Real.log_pow] at hdepth
  norm_num only [Nat.cast_ofNat] at hdepth
  have hq := short_height_count_q2 s T (α := α) hH hP hY hYP hD0 hcover hs hD
  apply hq.trans
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdepth (by positivity))
  have hL := (RationalHeight.height_pos (H * P ^ 2) α).le
  positivity

/-- Q4 for actual heights, using the proved Q2 estimate. Only a uniform
finite divisor-count bound up to `floor(2HP)` remains as a premise. -/
theorem short_height_inverse_square_log_bound (s : Finset ℕ)
    {H P α D : ℝ} (hH : 1 ≤ H) (hP : 2 ≤ P) (hD0 : 0 ≤ D)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hD : ∀ n ∈ Finset.Icc 1 ⌊2 * H * P⌋₊, (n.divisors.card : ℝ) ≤ D) :
    let K := 256 * D * (2 + 2 * Real.log P / Real.log 2)
    let L := RationalHeight.height (H * P ^ 2) α
    (∑ h ∈ s, 1 / (RationalHeight.height (P ^ 2) ((h : ℝ) * α)) ^ 2) ≤
      4 * K * H / P ^ 2 * (2 + Real.log P / Real.log 2) +
        24 * K * min (H / L) (H ^ 2 / L ^ 2) := by
  have hP1 : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 2).trans hP
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply rational_height_inverse_square_log_bound s hH hP1 (by positivity) hs
  intro Y hY hY2P
  have hYP : Y ≤ P ^ 2 := by nlinarith
  apply short_height_count_q2_log s hH hP1 hY hYP hD0 hs
  intro n hn
  apply hD n
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnupper⟩
  refine Finset.mem_Icc.mpr ⟨hn1, hnupper.trans (Nat.floor_mono ?_)⟩
  have hh := mul_le_mul_of_nonneg_left hY2P hH0
  nlinarith

#print axioms weighted_product_count
#print axioms short_height_count_le_divisor_reciprocal
#print axioms short_height_count_q2
#print axioms short_height_count_q2_log
#print axioms short_height_inverse_square_log_bound

end Waring.ShortHeightCounting

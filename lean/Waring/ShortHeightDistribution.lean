import Waring.RationalHeight
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite short-height distribution deductions

The reciprocal-count estimate Q2 is an explicit premise. This file proves
the absorption, finite dyadic summation, and summation of pointwise fourth-
moment bounds which follow from that estimate. No reciprocal-count or
transference theorem is postulated as an axiom.
-/

noncomputable section

open scoped BigOperators

namespace Waring.ShortHeightDistribution

/-- The real-valued number of indices whose height is at most `Y`. -/
def heightCount {ι : Type*} (s : Finset ι) (B : ι → ℝ) (Y : ℝ) : ℝ := by
  classical
  exact ((s.filter (fun i => B i ≤ Y)).card : ℝ)

theorem heightCount_nonneg {ι : Type*} (s : Finset ι) (B : ι → ℝ) (Y : ℝ) :
    0 ≤ heightCount s B Y := Nat.cast_nonneg _

/-- The two error terms in Q2 are absorbed on a nonempty short-height range.
The hypotheses are exactly the height upper bound and the lifting bound.
-/
theorem q2_error_absorption {H P L Y : ℝ}
    (_hH : 0 < H) (hP : 0 < P) (hL : 0 < L) (hY : 0 ≤ Y)
    (hsqrt : L ^ 2 ≤ H * P ^ 2) (hlift : L ≤ H * Y) :
    H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2 ≤
      H * Y ^ 2 / P ^ 2 + 3 * H * Y / L := by
  have hbase : 1 ≤ H * Y / L := (le_div_iff₀ hL).mpr (by simpa using hlift)
  have hlast : L * Y / P ^ 2 ≤ H * Y / L := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hP) hL).mpr
    have hm := mul_le_mul_of_nonneg_right hsqrt hY
    nlinarith
  calc
    _ ≤ H * Y ^ 2 / P ^ 2 + H * Y / L + H * Y / L + H * Y / L :=
      add_le_add (add_le_add_left hbase _) hlast
    _ = _ := by ring

/-- Q2 implies Q3 for an actual finite list of heights. An empty sublevel set
requires no lifting witness; a nonempty one supplies precisely that witness. -/
theorem q2_count_absorption {ι : Type*} (s : Finset ι) (B : ι → ℝ)
    {H P L Y K : ℝ} (hH : 0 < H) (hP : 0 < P) (hL : 0 < L)
    (hY : 0 ≤ Y) (hK : 0 ≤ K) (hsqrt : L ^ 2 ≤ H * P ^ 2)
    (hlift : ∀ i ∈ s, L ≤ H * B i)
    (hq2 : heightCount s B Y ≤
      K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2)) :
    heightCount s B Y ≤ K * (H * Y ^ 2 / P ^ 2 + 3 * H * Y / L) := by
  classical
  by_cases hnonempty : (s.filter (fun i => B i ≤ Y)).Nonempty
  · obtain ⟨i, hi⟩ := hnonempty
    rcases Finset.mem_filter.mp hi with ⟨his, hiy⟩
    have hl : L ≤ H * Y := (hlift i his).trans (mul_le_mul_of_nonneg_left hiy hH.le)
    exact hq2.trans (mul_le_mul_of_nonneg_left (q2_error_absorption hH hP hL hY hsqrt hl) hK)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp only [heightCount, hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Lower inverse-square comparison used in the finite dyadic argument. -/
theorem inverse_square_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    1 / y ^ 2 ≤ 1 / x ^ 2 := by
  exact one_div_le_one_div_of_le (sq_pos_of_pos hx)
    (pow_le_pow_left₀ hx.le hxy 2)

/-- A finite pointwise dyadic majorant. All integer-depth choices and losses
are explicit; no asymptotic notation or logarithmic convention is used. -/
theorem inverse_square_dyadic_majorant (T : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ a * 2 ^ T) :
    1 / b ^ 2 ≤
      ∑ j ∈ Finset.range (T + 1),
        if b ≤ a * 2 ^ j then 4 / (a * 2 ^ j) ^ 2 else 0 := by
  induction T with
  | zero =>
      have hba : b = a := le_antisymm (by simpa using hb) hab
      subst b
      simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one, le_refl, if_true]
      apply div_le_div_of_nonneg_right (by norm_num) (sq_nonneg a)
  | succ T ih =>
      rw [Finset.sum_range_succ]
      by_cases hprev : b ≤ a * 2 ^ T
      · exact (ih hprev).trans (le_add_of_nonneg_right (by split_ifs; positivity))
      · have hcross : a * 2 ^ T ≤ b := (lt_of_not_ge hprev).le
        have hapos : 0 < a * 2 ^ T := mul_pos ha (pow_pos (by norm_num) _)
        have htail : 1 / b ^ 2 ≤ 4 / (a * 2 ^ (T + 1)) ^ 2 := by
          calc
            1 / b ^ 2 ≤ 1 / (a * 2 ^ T) ^ 2 := inverse_square_antitone hapos hcross
            _ = 4 / (a * 2 ^ (T + 1)) ^ 2 := by
              rw [pow_succ]
              field_simp
              ring
        rw [if_pos hb]
        exact htail.trans (le_add_of_nonneg_left
          (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)))

/-- Sum of a finite initial segment of the dyadic reciprocal powers. -/
theorem dyadic_reciprocal_sum_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (2 : ℝ) ^ j) ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℝ)) (m := 0) (n := N)
    (by norm_num) (by norm_num)
  norm_num only [pow_zero, sub_half, one_div_div, div_one] at h
  simpa only [Nat.Ico_zero_eq_range, div_pow, one_pow] using h

/-- General finite dyadic summation of a quadratic-plus-linear counting bound.
The final term retains the reciprocal of the actual starting height `a`.
-/
theorem dyadic_inverse_square_bound {ι : Type*} (s : Finset ι) (B : ι → ℝ)
    (T : ℕ) {a C D : ℝ} (ha : 0 < a) (_hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlower : ∀ i ∈ s, a ≤ B i) (hupper : ∀ i ∈ s, B i ≤ a * 2 ^ T)
    (hcount : ∀ j ≤ T, heightCount s B (a * 2 ^ j) ≤
      C * (a * 2 ^ j) ^ 2 + D * (a * 2 ^ j)) :
    (∑ i ∈ s, 1 / (B i) ^ 2) ≤ 4 * C * (T + 1 : ℕ) + 8 * D / a := by
  classical
  have hcountsum (j : ℕ) :
      (∑ i ∈ s, if B i ≤ a * 2 ^ j then 4 / (a * 2 ^ j) ^ 2 else 0) =
        heightCount s B (a * 2 ^ j) * (4 / (a * 2 ^ j) ^ 2) := by
    rw [← Finset.sum_filter]
    simp [heightCount]
  calc
    (∑ i ∈ s, 1 / (B i) ^ 2) ≤ ∑ i ∈ s,
        ∑ j ∈ Finset.range (T + 1),
          if B i ≤ a * 2 ^ j then 4 / (a * 2 ^ j) ^ 2 else 0 := by
      exact Finset.sum_le_sum (fun i hi =>
        inverse_square_dyadic_majorant T ha (hlower i hi) (hupper i hi))
    _ = ∑ j ∈ Finset.range (T + 1),
        heightCount s B (a * 2 ^ j) * (4 / (a * 2 ^ j) ^ 2) := by
      rw [Finset.sum_comm]
      simp_rw [hcountsum]
    _ ≤ ∑ j ∈ Finset.range (T + 1),
        (C * (a * 2 ^ j) ^ 2 + D * (a * 2 ^ j)) * (4 / (a * 2 ^ j) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcount j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        (by positivity)
    _ = 4 * C * (T + 1 : ℕ) + (4 * D / a) *
        ∑ j ∈ Finset.range (T + 1), 1 / (2 : ℝ) ^ j := by
      have hterm (j : ℕ) :
          (C * (a * 2 ^ j) ^ 2 + D * (a * 2 ^ j)) * (4 / (a * 2 ^ j) ^ 2) =
            4 * C + (4 * D / a) * (1 / (2 : ℝ) ^ j) := by
        have hap : a ≠ 0 := ne_of_gt ha
        have htwo : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 4 * C * (T + 1 : ℕ) + 8 * D / a := by
      apply add_le_add_left
      have h := mul_le_mul_of_nonneg_left (dyadic_reciprocal_sum_le_two (T + 1))
        (show 0 ≤ 4 * D / a by positivity)
      convert h using 1
      ring

/-- The starting-height factor is exactly the minimum in the manuscript's Q4. -/
theorem starting_height_identity {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    H / (L * max 1 (L / H)) = min (H / L) (H ^ 2 / L ^ 2) := by
  have hx : 0 ≤ H / L := (div_pos hH hL).le
  by_cases hLH : L ≤ H
  · have ha : L / H ≤ 1 := (div_le_iff₀ hH).mpr (by simpa using hLH)
    have hx1 : 1 ≤ H / L := (le_div_iff₀ hL).mpr (by simpa using hLH)
    have hmin : H / L ≤ H ^ 2 / L ^ 2 := by rw [← div_pow]; nlinarith
    rw [max_eq_left ha, mul_one, min_eq_left hmin]
  · have hHL : H ≤ L := (lt_of_not_ge hLH).le
    have ha : 1 ≤ L / H := (le_div_iff₀ hH).mpr (by simpa using hHL)
    have hx1 : H / L ≤ 1 := (div_le_iff₀ hL).mpr (by simpa using hHL)
    have hmin : H ^ 2 / L ^ 2 ≤ H / L := by rw [← div_pow]; nlinarith
    rw [max_eq_right ha, min_eq_right hmin]
    field_simp

/-- The finite form of Q2-to-Q4, with explicit dyadic depth and constants.
The cutoff `max 1 (L/H)` comes from the actual lower-height and lifting bounds.
-/
theorem q2_dyadic_inverse_square_bound {ι : Type*} (s : Finset ι) (B : ι → ℝ)
    (T : ℕ) {H P L K : ℝ} (hH : 0 < H) (hP : 0 < P) (hL : 0 < L) (hK : 0 ≤ K)
    (hsqrt : L ^ 2 ≤ H * P ^ 2)
    (hone : ∀ i ∈ s, 1 ≤ B i) (hlift : ∀ i ∈ s, L ≤ H * B i)
    (hupper : ∀ i ∈ s, B i ≤ max 1 (L / H) * 2 ^ T)
    (hq2 : ∀ j ≤ T, let Y := max 1 (L / H) * 2 ^ j
      heightCount s B Y ≤ K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2)) :
    (∑ i ∈ s, 1 / (B i) ^ 2) ≤
      4 * K * H / P ^ 2 * (T + 1 : ℕ) +
        24 * K * min (H / L) (H ^ 2 / L ^ 2) := by
  have ha : 0 < max 1 (L / H) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlower : ∀ i ∈ s, max 1 (L / H) ≤ B i := by
    intro i hi
    refine max_le (hone i hi) ?_
    apply (div_le_iff₀ hH).mpr
    simpa only [mul_comm] using hlift i hi
  have h := dyadic_inverse_square_bound s B T ha
    (show 0 ≤ K * H / P ^ 2 by positivity)
    (show 0 ≤ 3 * K * H / L by positivity) hlower hupper (by
      intro j hj
      have hy : 0 ≤ max 1 (L / H) * 2 ^ j := by positivity
      have hh := q2_count_absorption s B hH hP hL hy hK hsqrt hlift (hq2 j hj)
      convert hh using 1
      ring)
  calc
    _ ≤ 4 * (K * H / P ^ 2) * (T + 1 : ℕ) + 8 * (3 * K * H / L) / max 1 (L / H) := h
    _ = 4 * K * H / P ^ 2 * (T + 1 : ℕ) + 24 * K * (H / (L * max 1 (L / H))) := by ring
    _ = _ := by rw [starting_height_identity hH hL]

/-- A dyadic covering depth exists with final cutoff at most twice the target.
This also records the scale controlling the explicit dyadic loss. -/
theorem exists_dyadic_cover {a P : ℝ} (ha : 0 < a) (haP : a ≤ P) :
    ∃ T : ℕ, P ≤ a * 2 ^ T ∧ a * 2 ^ T ≤ 2 * P := by
  have hratio : 1 ≤ P / a := (le_div_iff₀ ha).mpr (by simpa using haP)
  obtain ⟨n, hn, hn1⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n + 1, ?_, ?_⟩
  · have h := (div_lt_iff₀ ha).mp hn1
    simpa only [mul_comm] using h.le
  · have h := (le_div_iff₀ ha).mp hn
    rw [pow_succ]
    nlinarith

/-- The explicit logarithmic loss of a dyadic cover whose starting height is
at least one and whose endpoint is at most twice `P`. -/
theorem dyadic_depth_le_log {a P : ℝ} (T : ℕ) (ha : 1 ≤ a) (hP : 0 < P)
    (hcover : a * 2 ^ T ≤ 2 * P) :
    ((T + 1 : ℕ) : ℝ) ≤ 2 + Real.log P / Real.log 2 := by
  have hpow : (2 : ℝ) ^ T ≤ 2 * P := by
    have h := mul_le_mul_of_nonneg_right ha (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) T)
    have hpow2 : (2 : ℝ) ^ T ≤ a * 2 ^ T := by simpa using h
    exact hpow2.trans hcover
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) T) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num) (ne_of_gt hP)] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (Real.log P / Real.log 2) * Real.log 2 = Real.log P :=
    div_mul_cancel₀ _ (ne_of_gt hlog2)
  have h := (le_div_iff₀ hlog2).mpr (show
      ((T + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log 2 + Real.log P by
    push_cast
    nlinarith)
  convert h using 1
  field_simp

/-- Dirichlet and lifting supply all height hypotheses of Q4 for an actual
finite family of positive integer multiples. The count estimate remains the
single explicit input to this inverse-square conclusion. -/
theorem rational_height_inverse_square_bound (s : Finset ℕ) (T : ℕ)
    {H P α K : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hK : 0 ≤ K)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hdyadic : P ≤ max 1 (RationalHeight.height (H * P ^ 2) α / H) * 2 ^ T)
    (hq2 : ∀ j ≤ T,
      let L := RationalHeight.height (H * P ^ 2) α
      let Y := max 1 (L / H) * 2 ^ j
      heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
        K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2)) :
    (∑ h ∈ s, 1 / (RationalHeight.height (P ^ 2) ((h : ℝ) * α)) ^ 2) ≤
      4 * K * H / P ^ 2 * (T + 1 : ℕ) +
        24 * K * min (H / RationalHeight.height (H * P ^ 2) α)
          (H ^ 2 / (RationalHeight.height (H * P ^ 2) α) ^ 2) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have hHP2 : 1 ≤ H * P ^ 2 := hP2.trans (by nlinarith [mul_le_mul_of_nonneg_right hH (sq_nonneg P)])
  have hLpos := RationalHeight.height_pos (H * P ^ 2) α
  have hLsq : (RationalHeight.height (H * P ^ 2) α) ^ 2 ≤ H * P ^ 2 := by
    calc
      _ ≤ (Real.sqrt (H * P ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hLpos.le (RationalHeight.height_le_sqrt hHP2 α) 2
      _ = _ := Real.sq_sqrt (zero_le_one.trans hHP2)
  apply q2_dyadic_inverse_square_bound s _ T hHpos hPpos hLpos hK hLsq
  · intro h _hh
    exact RationalHeight.one_le_height _ _
  · intro h hh
    exact RationalHeight.height_mul_lift (sq_nonneg P) (hs h hh).1 (hs h hh).2
  · intro h _hh
    have hb := RationalHeight.height_le_sqrt hP2 ((h : ℝ) * α)
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hPpos.le] at hb
    exact hb.trans hdyadic
  · exact hq2

/-- The dyadic depth can be eliminated entirely. The only count premise is
Q2 at real cutoffs between zero and `2P`; the conclusion has an explicit
logarithmic factor and the precise minimum of the two height terms. -/
theorem rational_height_inverse_square_log_bound (s : Finset ℕ)
    {H P α K : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hK : 0 ≤ K)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hq2 : ∀ Y : ℝ, 0 < Y → Y ≤ 2 * P →
      let L := RationalHeight.height (H * P ^ 2) α
      heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
        K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2)) :
    (∑ h ∈ s, 1 / (RationalHeight.height (P ^ 2) ((h : ℝ) * α)) ^ 2) ≤
      4 * K * H / P ^ 2 * (2 + Real.log P / Real.log 2) +
        24 * K * min (H / RationalHeight.height (H * P ^ 2) α)
          (H ^ 2 / (RationalHeight.height (H * P ^ 2) α) ^ 2) := by
  let L := RationalHeight.height (H * P ^ 2) α
  let a := max 1 (L / H)
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have ha1 : 1 ≤ a := le_max_left _ _
  have hapos : 0 < a := zero_lt_one.trans_le ha1
  have hP2 : 1 ≤ P ^ 2 := by nlinarith
  have hlocal : RationalHeight.height (P ^ 2) α ≤ P := by
    have hh := RationalHeight.height_le_sqrt hP2 α
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg hPpos.le] using hh
  have hlift : L ≤ H * RationalHeight.height (P ^ 2) α := by
    simpa only [Nat.cast_one, one_mul] using
      RationalHeight.height_mul_lift (α := α) (sq_nonneg P) (h := 1) (by decide)
        (by simpa only [Nat.cast_one] using hH)
  have haP : a ≤ P := max_le hP ((div_le_iff₀ hHpos).mpr
    (by simpa only [mul_comm] using hlift.trans (mul_le_mul_of_nonneg_left hlocal hHpos.le)))
  obtain ⟨T, hcover, hcover2⟩ := exists_dyadic_cover hapos haP
  have hh := rational_height_inverse_square_bound s T hH hP hK hs hcover (by
    intro j hj
    have hy : 0 < a * 2 ^ j := mul_pos hapos (pow_pos (by norm_num) j)
    have hy2 : a * 2 ^ j ≤ 2 * P :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
        hapos.le).trans hcover2
    exact hq2 _ hy hy2)
  have hdepth := dyadic_depth_le_log T ha1 hPpos hcover2
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_left hdepth (by positivity)) _)

/-- A finite family of positive natural indices bounded by `H` has size at
most `H`; this supplies the diagonal term when summing pointwise estimates. -/
theorem card_le_real_bound (s : Finset ℕ) {H : ℝ} (hH : 0 ≤ H)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H) : (s.card : ℝ) ≤ H := by
  have hsubset : s ⊆ Finset.Icc 1 ⌊H⌋₊ := by
    intro h hh
    exact Finset.mem_Icc.mpr ⟨(hs h hh).1, Nat.le_floor (hs h hh).2⟩
  calc
    (s.card : ℝ) ≤ ((Finset.Icc 1 ⌊H⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsubset
    _ = (⌊H⌋₊ : ℝ) := by simp
    _ ≤ H := Nat.floor_le hH

/-- Summing the pointwise Q1 bound is exact finite algebra after an inverse-
square estimate is known. The functions may contain different modulations
at every index; no relation between their complex values is required. -/
theorem fourth_moment_sum_bound {ι : Type*} (s : Finset ι) (Z : ι → ℂ) (B : ι → ℝ)
    {P A H S : ℝ} (hA : 0 ≤ A) (hcard : (s.card : ℝ) ≤ H)
    (hsum : (∑ i ∈ s, 1 / (B i) ^ 2) ≤ S)
    (hpoint : ∀ i ∈ s, ‖Z i‖ ^ 4 ≤ A * (P ^ 2 + P ^ 4 / (B i) ^ 2)) :
    (∑ i ∈ s, ‖Z i‖ ^ 4) ≤ A * (H * P ^ 2 + P ^ 4 * S) := by
  calc
    _ ≤ ∑ i ∈ s, A * (P ^ 2 + P ^ 4 / (B i) ^ 2) := Finset.sum_le_sum hpoint
    _ = A * ((s.card : ℝ) * P ^ 2 + P ^ 4 * ∑ i ∈ s, 1 / (B i) ^ 2) := by
      have hterm (i : ι) : A * (P ^ 2 + P ^ 4 / (B i) ^ 2) =
          A * P ^ 2 + (A * P ^ 4) * (1 / (B i) ^ 2) := by ring
      simp_rw [hterm]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hcard (sq_nonneg P))
        (mul_le_mul_of_nonneg_left hsum (by positivity))) hA

/-- The actual rational-height version of Q5, conditional precisely on Q1
and the reciprocal counting estimate Q2, with explicit constants and dyadic
loss. No uniformity assumption on the family's linear modulations is needed.
-/
theorem sampled_fourth_moment_conditional (s : Finset ℕ) (Z : ℕ → ℂ) (T : ℕ)
    {H P α K A : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hdyadic : P ≤ max 1 (RationalHeight.height (H * P ^ 2) α / H) * 2 ^ T)
    (hq2 : ∀ j ≤ T,
      let L := RationalHeight.height (H * P ^ 2) α
      let Y := max 1 (L / H) * 2 ^ j
      heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
        K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2))
    (hq1 : ∀ h ∈ s, ‖Z h‖ ^ 4 ≤
      A * (P ^ 2 + P ^ 4 / (RationalHeight.height (P ^ 2) ((h : ℝ) * α)) ^ 2)) :
    (∑ h ∈ s, ‖Z h‖ ^ 4) ≤
      A * (H * P ^ 2 + P ^ 4 *
        (4 * K * H / P ^ 2 * (T + 1 : ℕ) +
          24 * K * min (H / RationalHeight.height (H * P ^ 2) α)
            (H ^ 2 / (RationalHeight.height (H * P ^ 2) α) ^ 2))) := by
  exact fourth_moment_sum_bound s Z _ hA
    (card_le_real_bound s (zero_le_one.trans hH) hs)
    (rational_height_inverse_square_bound s T hH hP hK hs hdyadic hq2) hq1

/-- Q5 with the depth choice eliminated and its logarithmic loss explicit. -/
theorem sampled_fourth_moment_log_conditional (s : Finset ℕ) (Z : ℕ → ℂ)
    {H P α K A : ℝ} (hH : 1 ≤ H) (hP : 1 ≤ P) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hq2 : ∀ Y : ℝ, 0 < Y → Y ≤ 2 * P →
      let L := RationalHeight.height (H * P ^ 2) α
      heightCount s (fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)) Y ≤
        K * (H * Y ^ 2 / P ^ 2 + H * Y / L + 1 + L * Y / P ^ 2))
    (hq1 : ∀ h ∈ s, ‖Z h‖ ^ 4 ≤
      A * (P ^ 2 + P ^ 4 / (RationalHeight.height (P ^ 2) ((h : ℝ) * α)) ^ 2)) :
    (∑ h ∈ s, ‖Z h‖ ^ 4) ≤
      A * (H * P ^ 2 + P ^ 4 *
        (4 * K * H / P ^ 2 * (2 + Real.log P / Real.log 2) +
          24 * K * min (H / RationalHeight.height (H * P ^ 2) α)
            (H ^ 2 / (RationalHeight.height (H * P ^ 2) α) ^ 2))) := by
  exact fourth_moment_sum_bound s Z _ hA
    (card_le_real_bound s (zero_le_one.trans hH) hs)
    (rational_height_inverse_square_log_bound s hH hP hK hs hq2) hq1

#print axioms q2_error_absorption
#print axioms inverse_square_dyadic_majorant
#print axioms dyadic_inverse_square_bound
#print axioms q2_dyadic_inverse_square_bound
#print axioms rational_height_inverse_square_bound
#print axioms rational_height_inverse_square_log_bound
#print axioms sampled_fourth_moment_conditional
#print axioms sampled_fourth_moment_log_conditional

end Waring.ShortHeightDistribution

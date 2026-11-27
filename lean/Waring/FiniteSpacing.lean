import Waring.ShortHeightDistribution
import Waring.GeometricSums
import Mathlib.Data.Finset.Max

/-!
# Separated finite points and truncated reciprocal sums

These elementary lemmas turn a finite spacing estimate into the reciprocal
bound needed by quadratic Weyl sums. The dyadic depth is explicit, so no
asymptotic or logarithmic estimate is hidden in the statement.
-/

noncomputable section
open scoped BigOperators

namespace Waring.FiniteSpacing

/-- A finite collection of separated real points in an interval has bounded
cardinality. Repetitions are excluded by the positive separation premise. -/
theorem separated_card_mul_le {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {d : ℝ} (hd : 0 < d) {a b : ℝ} (hab : a ≤ b)
    (hrange : ∀ i ∈ s, a ≤ x i ∧ x i ≤ b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ |x i - x j|) :
    (s.card : ℝ) * d ≤ b - a + d := by
  classical
  revert a b
  induction s using Finset.induction_on_min_value x with
  | h0 =>
      intro a b hab _
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      linarith
  | @step i s hnot hmin ih =>
      intro a b hab hrange
      have hi := hrange i (Finset.mem_insert_self _ _)
      by_cases hempty : s = ∅
      · subst s
        simpa using (le_add_of_nonneg_left (sub_nonneg.mpr hab) : d ≤ (b - a) + d)
      · have hlower : ∀ j ∈ s, x i + d ≤ x j := by
          intro j hj
          have hij : i ≠ j := by intro h; subst j; exact hnot hj
          have h := hsep i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij
          rw [abs_of_nonpos (sub_nonpos.mpr (hmin j hj))] at h
          linarith
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hnew : x i + d ≤ b := (hlower j hj).trans (hrange j (Finset.mem_insert_of_mem hj)).2
        have hrest := ih
          (fun j hj k hk hne => hsep j (Finset.mem_insert_of_mem hj) k
            (Finset.mem_insert_of_mem hk) hne) hnew
          (fun j hj => ⟨hlower j hj, (hrange j (Finset.mem_insert_of_mem hj)).2⟩)
        rw [Finset.card_insert_of_notMem hnot, Nat.cast_add, Nat.cast_one]
        nlinarith

/-- Count of separated points whose absolute values lie below a threshold. -/
theorem separated_abs_count {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {d Y : ℝ} (hd : 0 < d) (hY : 0 ≤ Y)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ |x i - x j|) :
    ShortHeightDistribution.heightCount s (fun i => |x i|) Y ≤ 2 * Y / d + 1 := by
  classical
  let t := s.filter (fun i => |x i| ≤ Y)
  have h := separated_card_mul_le t x hd (a := -Y) (b := Y) (by linarith)
    (fun i hi => abs_le.mp (Finset.mem_filter.mp hi).2)
    (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j
      (Finset.mem_filter.mp hj).1 hij)
  change (t.card : ℝ) ≤ 2 * Y / d + 1
  have heq : (2 * Y / d + 1) * d = 2 * Y + d := by field_simp
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [heq]
  linarith

/-- The reciprocal is truncated at `1/a`, with the zero-distance branch
defined explicitly rather than using Lean's inverse of zero. -/
def truncatedReciprocal (a x : ℝ) : ℝ := if x = 0 then 1 / a else min (1 / a) (1 / x)

theorem truncatedReciprocal_le_cap (a x : ℝ) : truncatedReciprocal a x ≤ 1 / a := by
  unfold truncatedReciprocal
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem truncatedReciprocal_nonneg {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ truncatedReciprocal a x := by
  unfold truncatedReciprocal
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

theorem reciprocal_dyadic_majorant (T : ℕ) {a x : ℝ} (ha : 0 < a)
    (_hx : 0 ≤ x) (hxupper : x ≤ a * 2 ^ T) :
    truncatedReciprocal a x ≤
      ∑ j ∈ Finset.range (T + 1), if x ≤ a * 2 ^ j then 2 / (a * 2 ^ j) else 0 := by
  induction T with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one] at hxupper ⊢
      rw [if_pos hxupper]
      exact (truncatedReciprocal_le_cap a x).trans
        (div_le_div_of_nonneg_right (by norm_num) ha.le)
  | succ T ih =>
      rw [Finset.sum_range_succ]
      by_cases hprev : x ≤ a * 2 ^ T
      · exact (ih hprev).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
      · have hapos : 0 < a * 2 ^ T := mul_pos ha (pow_pos (by norm_num) _)
        have hxpos : 0 < x := hapos.trans (lt_of_not_ge hprev)
        have ht : truncatedReciprocal a x ≤ 2 / (a * 2 ^ (T + 1)) := by
          calc
            truncatedReciprocal a x ≤ 1 / x := by
              simp only [truncatedReciprocal, if_neg hxpos.ne']
              exact min_le_right _ _
            _ ≤ 1 / (a * 2 ^ T) := one_div_le_one_div_of_le hapos (lt_of_not_ge hprev).le
            _ = 2 / (a * 2 ^ (T + 1)) := by rw [pow_succ]; field_simp
        rw [if_pos hxupper]
        exact ht.trans (le_add_of_nonneg_left
          (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)))

/-- A linear counting bound implies an explicit logarithmic-depth
truncated-reciprocal bound. -/
theorem reciprocal_sum_of_count {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℕ) {a C D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hupper : ∀ i ∈ s, x i ≤ a * 2 ^ T)
    (hcount : ∀ j ≤ T, ShortHeightDistribution.heightCount s x (a * 2 ^ j) ≤
      C * (a * 2 ^ j) + D) :
    (∑ i ∈ s, truncatedReciprocal a (x i)) ≤ 2 * C * (T + 1 : ℕ) + 4 * D / a := by
  classical
  have hcounts (j : ℕ) :
      (∑ i ∈ s, if x i ≤ a * 2 ^ j then 2 / (a * 2 ^ j) else 0) =
        ShortHeightDistribution.heightCount s x (a * 2 ^ j) * (2 / (a * 2 ^ j)) := by
    rw [← Finset.sum_filter]
    simp [ShortHeightDistribution.heightCount]
  calc
    (∑ i ∈ s, truncatedReciprocal a (x i)) ≤
        ∑ i ∈ s, ∑ j ∈ Finset.range (T + 1),
          if x i ≤ a * 2 ^ j then 2 / (a * 2 ^ j) else 0 := by
      exact Finset.sum_le_sum (fun i hi => reciprocal_dyadic_majorant T ha (hx i hi) (hupper i hi))
    _ = ∑ j ∈ Finset.range (T + 1),
        ShortHeightDistribution.heightCount s x (a * 2 ^ j) * (2 / (a * 2 ^ j)) := by
      rw [Finset.sum_comm]
      simp_rw [hcounts]
    _ ≤ ∑ j ∈ Finset.range (T + 1), (C * (a * 2 ^ j) + D) * (2 / (a * 2 ^ j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcount j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))) (by positivity)
    _ = 2 * C * (T + 1 : ℕ) + (2 * D / a) *
        ∑ j ∈ Finset.range (T + 1), 1 / (2 : ℝ) ^ j := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have h1 (j : ℕ) : C * (a * 2 ^ j) * (2 / (a * 2 ^ j)) = 2 * C := by field_simp
      have h2 (j : ℕ) : D * (2 / (a * 2 ^ j)) = (2 * D / a) * (1 / (2 : ℝ)^j) := by ring
      simp_rw [h1, h2]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * C * (T + 1 : ℕ) + 4 * D / a := by
      have hgeo := ShortHeightDistribution.dyadic_reciprocal_sum_le_two (T + 1)
      have hm := mul_le_mul_of_nonneg_left hgeo (show 0 ≤ 2 * D / a by positivity)
      calc
        _ ≤ 2 * C * (T + 1 : ℕ) + (2 * D / a) * 2 := add_le_add_left hm _
        _ = _ := by ring

/-- Combining interval packing with dyadic summation. -/
theorem reciprocal_sum_of_separation {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (T : ℕ) {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hupper : ∀ i ∈ s, |x i| ≤ a * 2 ^ T)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ |x i - x j|) :
    (∑ i ∈ s, truncatedReciprocal a |x i|) ≤ 4 / d * (T + 1 : ℕ) + 4 / a := by
  have h := reciprocal_sum_of_count s (fun i => |x i|) T ha (by norm_num : (0 : ℝ) ≤ 1)
    (fun i _ => abs_nonneg _) hupper (C := 2 / d) (fun j _ => by
      have hh := separated_abs_count s x hd (show 0 ≤ a * 2^j by positivity) hsep
      convert hh using 1 <;> ring)
  convert h using 1 <;> ring

#print axioms separated_card_mul_le
#print axioms reciprocal_sum_of_separation

end Waring.FiniteSpacing

import Waring.FiniteSpacing
import Waring.RationalSpacing
import Waring.RationalTransference

/-!
# Reciprocal sums from rational spacing and intrinsic height

The denominator estimate is proved from finite separated-point counting on
blocks of `q/2+1` indices. The zero-distance branch is included explicitly.
The dyadic depth is visible in every statement; no logarithmic or asymptotic
estimate is assumed. The final intrinsic-height version uses the independently
proved rational transference theorem.
-/

noncomputable section
open scoped BigOperators

namespace Waring.ReciprocalSums

open FiniteSpacing RationalSpacing

/-- The total geometric-sum majorant is dominated by the reciprocal weight
used in the finite spacing theorem, including at integral phases. -/
theorem linearSumBound_le_truncated {J : ℕ} (hJ : 0 < J) (β : ℝ) :
    linearSumBound J β ≤ truncatedReciprocal (1 / (J : ℝ)) (integerDistance β) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  unfold linearSumBound truncatedReciprocal
  split_ifs with hz
  · simp
  · have hd : 0 < integerDistance β :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
    simp only [one_div_one_div]
    apply min_le_min_left
    exact div_le_div_of_nonneg_left (by norm_num) hd (by linarith)

/-- One full block satisfies an explicit denominator bound. -/
theorem reciprocal_block_bound_real (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    (J : ℝ) (T : ℕ) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) (M : ℤ) :
    (∑ i ∈ Finset.range (r.den / 2 + 1),
      truncatedReciprocal (1 / (J : ℝ))
        (integerDistance (α * ((M + (i : ℤ) : ℤ) : ℝ)))) ≤
      8 * (r.den : ℝ) * (T + 1 : ℕ) + 4 * J := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hscale : (1 : ℝ) ≤ (1 / (J : ℝ)) * 2 ^ T := by
    calc
      (1 : ℝ) = (1 / (J : ℝ)) * (J : ℝ) := by field_simp
      _ ≤ (1 / (J : ℝ)) * 2 ^ T :=
        mul_le_mul_of_nonneg_left hJT (by positivity)
  have h := reciprocal_sum_of_separation
    (Finset.range (r.den / 2 + 1))
    (fun i => signedFraction (α * ((M + (i : ℤ) : ℤ) : ℝ))) T
    (show 0 < 1 / (J : ℝ) by positivity)
    (show 0 < 1 / (2 * (r.den : ℝ)) by positivity)
    (fun i _ => (abs_signedFraction_le _).trans (by linarith))
    (fun i hi j hj hij => signedFraction_separation_block r hgood M
      (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij)
  calc
    _ ≤ 4 / (1 / (2 * (r.den : ℝ))) * (T + 1 : ℕ) + 4 / (1 / (J : ℝ)) := h
    _ = 8 * (r.den : ℝ) * (T + 1 : ℕ) + 4 * J := by field_simp; ring

/-- Summing a uniform block estimate requires only finite induction. -/
theorem sum_complete_blocks_le (f : ℕ → ℝ) (Q : ℕ) (B : ℝ)
    (hblock : ∀ M : ℕ, (∑ i ∈ Finset.range Q, f (M + i)) ≤ B) (L : ℕ) :
    (∑ i ∈ Finset.range (L * Q), f i) ≤ (L : ℝ) * B := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.succ_mul, Finset.sum_range_add]
    have hb := hblock (L * Q)
    push_cast
    nlinarith

/-- The number of padded blocks is at most `2N/q+1`. -/
theorem padded_block_count (N q : ℕ) (hq : 0 < q) :
    ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / q + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf : q ≤ 2 * (q / 2 + 1) := by omega
  have hmul : (N / (q / 2 + 1)) * q ≤ 2 * N := by
    have ha := Nat.mul_le_mul_left (N / (q / 2 + 1)) hhalf
    have hb := Nat.div_mul_le_self N (q / 2 + 1)
    nlinarith
  have hmulR : ((N / (q / 2 + 1) : ℕ) : ℝ) * (q : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hmul
  have hdiv : ((N / (q / 2 + 1) : ℕ) : ℝ) ≤ 2 * (N : ℝ) / q :=
    (le_div_iff₀ hqR).mpr hmulR
  push_cast
  linarith

/-- The genuine denominator-form reciprocal sum estimate. Reducedness and
quality of the approximant enter through the proved block separation. -/
theorem reciprocal_sum_denominator_real (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    (N : ℕ) (J : ℝ) (T : ℕ) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N,
      truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ)))) ≤
      16 * ((N : ℝ) * J / r.den + N + J + r.den) * (T + 1 : ℕ) := by
  let Q := r.den / 2 + 1
  let L := N / Q + 1
  let B : ℝ := 8 * (r.den : ℝ) * (T + 1 : ℕ) + 4 * J
  let f : ℕ → ℝ := fun n =>
    truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ)))
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hf : ∀ n, 0 ≤ f n := fun n =>
    truncatedReciprocal_nonneg (by positivity) (abs_nonneg _)
  have hpad : N ≤ L * Q := by
    have h := Nat.lt_mul_div_succ N (show 0 < Q by dsimp [Q]; omega)
    simpa only [L, Nat.mul_comm] using h.le
  have hblock : ∀ M : ℕ, (∑ i ∈ Finset.range Q, f (M + i)) ≤ B := by
    intro M
    simpa only [Q, f, B, Nat.cast_add, Int.cast_add, Int.cast_natCast] using
      reciprocal_block_bound_real r hgood J T hJ hJT (M : ℤ)
  have hsum := sum_complete_blocks_le f Q B hblock L
  have hcount : (L : ℝ) ≤ 2 * (N : ℝ) / r.den + 1 :=
    padded_block_count N r.den r.pos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hq0 : (0 : ℝ) ≤ r.den := hq.le
  have ht : (1 : ℝ) ≤ (T + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 T
  have hv : 0 ≤ (N : ℝ) * J / r.den := by positivity
  calc
    _ ≤ ∑ i ∈ Finset.range (L * Q), f i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hpad) (fun i _ _ => hf i)
    _ ≤ (L : ℝ) * B := hsum
    _ ≤ (2 * (N : ℝ) / r.den + 1) * B := mul_le_mul_of_nonneg_right hcount hB
    _ = 16 * (N : ℝ) * (T + 1 : ℕ) + 8 * ((N : ℝ) * J / r.den) +
        8 * (r.den : ℝ) * (T + 1 : ℕ) + 4 * J := by
      dsimp [B]
      field_simp
      ring
    _ ≤ 16 * ((N : ℝ) * J / r.den + N + J + r.den) * (T + 1 : ℕ) := by
      have hvT := mul_le_mul_of_nonneg_left ht hv
      have hJT' := mul_le_mul_of_nonneg_left ht hJ0
      have hqT := mul_nonneg hq0 (by positivity : (0 : ℝ) ≤ (T + 1 : ℕ))
      nlinarith

/-- Natural-cap specialization, matching finite geometric sums. -/
theorem reciprocal_sum_denominator (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    (N J T : ℕ) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N,
      truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ)))) ≤
      16 * ((N : ℝ) * J / r.den + N + J + r.den) * (T + 1 : ℕ) :=
  reciprocal_sum_denominator_real r hgood N J T (by exact_mod_cast hJ) hJT

/-- Summed geometric-sum majorants inherit the denominator estimate. -/
theorem linearSumBound_sum_denominator (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    (N J T : ℕ) (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N, linearSumBound J (α * (n : ℝ))) ≤
      16 * ((N : ℝ) * J / r.den + N + J + r.den) * (T + 1 : ℕ) := by
  exact (Finset.sum_le_sum (fun n _ => linearSumBound_le_truncated hJ _)).trans
    (reciprocal_sum_denominator r hgood N J T hJ hJT)

/-- Reciprocal sums bounded by the intrinsic minimum over all rational
approximants, with no preferred approximant left as a hypothesis. -/
theorem reciprocal_sum_intrinsic_real (α : ℝ) (N : ℕ) (J : ℝ) (T : ℕ) (hN : 0 < N)
    (hJ : 1 ≤ J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N,
      truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ)))) ≤
      128 * ((N : ℝ) * J / RationalHeight.height ((N : ℝ) * J) α +
        N + J + RationalHeight.height ((N : ℝ) * J) α) * (T + 1 : ℕ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hJ1 : (1 : ℝ) ≤ J := hJ
  have hJpos : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have h := RationalHeight.transfer_to_intrinsic_height (α := α)
    (F := ∑ n ∈ Finset.range N,
      truncatedReciprocal (1 / J) (integerDistance (α * (n : ℝ))))
    (V := (N : ℝ) * J) (B := (N : ℝ) + J) (K := 16 * (T + 1 : ℕ))
    (by nlinarith) (by positivity) (by positivity)
    (fun r hr => by
      have hb := reciprocal_sum_denominator_real r hr N J T hJpos hJT
      convert hb using 1 <;> ring)
  convert h using 1 <;> ring

/-- Natural-cap specialization of the intrinsic reciprocal bound. -/
theorem reciprocal_sum_intrinsic (α : ℝ) (N J T : ℕ) (hN : 0 < N)
    (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N,
      truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ)))) ≤
      128 * ((N : ℝ) * J / RationalHeight.height ((N : ℝ) * J) α +
        N + J + RationalHeight.height ((N : ℝ) * J) α) * (T + 1 : ℕ) :=
  reciprocal_sum_intrinsic_real α N J T hN (by exact_mod_cast hJ) hJT

/-- The total linear-sum majorant satisfies the same intrinsic estimate. -/
theorem linearSumBound_sum_intrinsic (α : ℝ) (N J T : ℕ) (hN : 0 < N)
    (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N, linearSumBound J (α * (n : ℝ))) ≤
      128 * ((N : ℝ) * J / RationalHeight.height ((N : ℝ) * J) α +
        N + J + RationalHeight.height ((N : ℝ) * J) α) * (T + 1 : ℕ) :=
  (Finset.sum_le_sum (fun n _ => linearSumBound_le_truncated hJ _)).trans
    (reciprocal_sum_intrinsic α N J T hN hJ hJT)

/-- The intrinsic-height estimate applies to the actual norms of arbitrary
integer translates of the linear Weyl sums. -/
theorem linearWeylSum_sum_intrinsic (α : ℝ) (M : ℤ) (N J T : ℕ) (hN : 0 < N)
    (hJ : 0 < J) (hJT : (J : ℝ) ≤ 2 ^ T) :
    (∑ n ∈ Finset.range N, ‖shiftedLinearWeylSum M J (α * (n : ℝ))‖) ≤
      128 * ((N : ℝ) * J / RationalHeight.height ((N : ℝ) * J) α +
        N + J + RationalHeight.height ((N : ℝ) * J) α) * (T + 1 : ℕ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, linearSumBound J (α * (n : ℝ)) :=
      Finset.sum_le_sum (fun n _ => norm_shiftedLinearWeylSum_le _ _ _)
    _ ≤ ∑ n ∈ Finset.range N,
        truncatedReciprocal (1 / (J : ℝ)) (integerDistance (α * (n : ℝ))) :=
      Finset.sum_le_sum (fun n _ => linearSumBound_le_truncated hJ _)
    _ ≤ _ := reciprocal_sum_intrinsic α N J T hN hJ hJT

#print axioms reciprocal_sum_denominator_real
#print axioms reciprocal_sum_denominator
#print axioms reciprocal_sum_intrinsic_real
#print axioms reciprocal_sum_intrinsic
#print axioms linearWeylSum_sum_intrinsic

end Waring.ReciprocalSums

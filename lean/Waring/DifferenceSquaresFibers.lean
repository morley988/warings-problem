import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite fibers of a difference of two integer squares

For a nonzero integer n, the difference z-w injects the solution pairs into
the signed divisors of n. The zero fiber is handled separately by the two signs of w.
These bounds include negative variables and need no parity convention or
positivity assumption on the interval endpoints.
-/

namespace Waring.DifferenceSquaresFibers

/-- Both signs of every positive divisor of the absolute value. -/
def signedDivisors (n : ℤ) : Finset ℤ :=
  n.natAbs.divisors.image (fun d : ℕ => (d : ℤ)) ∪
    n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ))

theorem card_signedDivisors_le (n : ℤ) :
    (signedDivisors n).card ≤ 2*n.natAbs.divisors.card := by
  unfold signedDivisors
  have h := Finset.card_union_le
    (n.natAbs.divisors.image (fun d : ℕ => (d : ℤ)))
    (n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ)))
  have hpos := (Finset.card_image_le :
    (n.natAbs.divisors.image (fun d : ℕ => (d : ℤ))).card ≤ n.natAbs.divisors.card)
  have hneg := (Finset.card_image_le :
    (n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ))).card ≤ n.natAbs.divisors.card)
  omega

theorem mem_signedDivisors {n d : ℤ} (hn : n ≠ 0) (hd : d ∣ n) :
    d ∈ signedDivisors n := by
  have hmem : d.natAbs ∈ n.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hd, Int.natAbs_ne_zero.mpr hn⟩
  rcases Int.natAbs_eq d with heq | heq
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d.natAbs, hmem, heq.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d.natAbs, hmem, heq.symm⟩)

/-- The integer difference determines a solution of a fixed nonzero square
 difference uniquely. This is the injection behind the divisor estimate. -/
theorem pair_eq_of_difference_eq {n : ℤ} (hn : n ≠ 0) {z w z' w' : ℤ}
    (hzw : z^2-w^2=n) (hzw' : z'^2-w'^2=n) (hd : z-w=z'-w') :
    (z,w)=(z',w') := by
  have hd0 : z-w ≠ 0 := by
    intro h
    have heq : z=w := sub_eq_zero.mp h
    rw [heq, sub_self] at hzw
    exact hn hzw.symm
  have hfac : (z-w)*(z+w)=n := by nlinarith [hzw]
  have hfac' : (z'-w')*(z'+w')=n := by nlinarith [hzw']
  rw [← hd] at hfac'
  have hsum : z+w=z'+w' := mul_left_cancel₀ hd0 (hfac.trans hfac'.symm)
  apply Prod.ext <;> omega

/-- Any finite collection of pairs with the same nonzero square difference
has at most twice as many members as the positive divisor set. -/
theorem pair_fiber_card_le (pairs : Finset (ℤ × ℤ)) {n : ℤ} (hn : n ≠ 0)
    (hpairs : ∀ pair ∈ pairs, pair.1^2-pair.2^2=n) :
    pairs.card ≤ 2*n.natAbs.divisors.card := by
  apply (Finset.card_le_card_of_injOn (fun pair : ℤ × ℤ => pair.1-pair.2) ?_ ?_).trans
    (card_signedDivisors_le n)
  · intro pair hpair
    apply mem_signedDivisors hn
    refine ⟨pair.1+pair.2, ?_⟩
    nlinarith [hpairs pair hpair]
  · intro pair hpair pair' hpair' hdiff
    rcases pair with ⟨z,w⟩
    rcases pair' with ⟨z',w'⟩
    exact pair_eq_of_difference_eq hn (hpairs _ hpair) (hpairs _ hpair') hdiff

/-- The actual finite fiber in two arbitrary finite sets of integers. -/
def squareDifferenceFiber (s t : Finset ℤ) (n : ℤ) : Finset (ℤ × ℤ) :=
  (s ×ˢ t).filter (fun pair => pair.1^2-pair.2^2=n)

theorem squareDifferenceFiber_card_le (s t : Finset ℤ) {n : ℤ} (hn : n ≠ 0) :
    (squareDifferenceFiber s t n).card ≤ 2*n.natAbs.divisors.card :=
  pair_fiber_card_le _ hn (fun _ hp => (Finset.mem_filter.mp hp).2)

/-- The zero fiber has at most two choices for one variable once the other
has been fixed, even when both signs occur in the original finite set. -/
theorem squareDifferenceFiber_zero_card_le (s t : Finset ℤ) :
    (squareDifferenceFiber s t 0).card ≤ 2*t.card := by
  let diagonal := t.image (fun w => (w,w))
  let antidiagonal := t.image (fun w => (-w,w))
  have hsubset : squareDifferenceFiber s t 0 ⊆ diagonal ∪ antidiagonal := by
    intro pair hp
    rcases Finset.mem_filter.mp hp with ⟨hprod, heq⟩
    rcases Finset.mem_product.mp hprod with ⟨_, hw⟩
    have hs : pair.1^2=pair.2^2 := sub_eq_zero.mp heq
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨pair.2, hw, Prod.ext h.symm rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨pair.2, hw, Prod.ext h.symm rfl⟩
  have hcard := (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hd : diagonal.card ≤ t.card := Finset.card_image_le
  have ha : antidiagonal.card ≤ t.card := Finset.card_image_le
  omega

#print axioms pair_fiber_card_le
#print axioms squareDifferenceFiber_zero_card_le
end Waring.DifferenceSquaresFibers

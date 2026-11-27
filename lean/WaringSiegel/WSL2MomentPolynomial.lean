import WaringSiegel.WSL2MomentBounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# Polynomial fibers and the actual monomial second moment

The root bounds are proved in an arbitrary characteristic-zero integral
domain and apply directly to algebraic integers. Ordinary finite differences
are represented by literal polynomials with the exact expected degree.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

section RootBounds
variable {R : Type*} [CommRing R] [IsDomain R]

/-- A nonzero polynomial has at most its degree many distinct roots in any finite set. -/
theorem polynomial_finite_roots_card_le (p : R[X]) (hp : p ≠ 0) (S : Finset R)
    (hS : ∀ x ∈ S, p.eval x = 0) : S.card ≤ p.natDegree := by
  by_contra h
  exact hp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S hS (by omega))

/-- The finite fiber of a positive power map has cardinality at most its exponent. -/
theorem power_fiber_card_le (S : Finset R) (k : ℕ) (hk : 0 < k) (a : R) :
    (S.filter (fun x => x ^ k = a)).card ≤ k := by
  classical
  have h := polynomial_finite_roots_card_le (X ^ k - C a)
    (Polynomial.X_pow_sub_C_ne_zero hk a) (S.filter (fun x => x ^ k = a)) (by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hx')
  simpa only [Polynomial.natDegree_X_pow_sub_C] using h

/-- The same root bound for any injectively indexed finite node set. -/
theorem indexed_power_fiber_card_le {α : Type*} [Fintype α]
    (nodes : α → R) (hnodes : Function.Injective nodes) (k : ℕ) (hk : 0 < k) (a : R) :
    (Finset.univ.filter (fun x => nodes x ^ k = a)).card ≤ k := by
  classical
  let S := Finset.univ.filter (fun x : α => nodes x ^ k = a)
  have hi : Set.InjOn nodes (S : Set α) := fun _ _ _ _ h => hnodes h
  have hsub : S.image nodes ⊆ (Finset.univ.image nodes).filter (fun x => x ^ k = a) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩,
      (Finset.mem_filter.mp hy).2⟩
  calc
    S.card = (S.image nodes).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ ((Finset.univ.image nodes).filter (fun x => x ^ k = a)).card := Finset.card_le_card hsub
    _ ≤ k := power_fiber_card_le _ k hk a

end RootBounds

section SecondMoment
variable {R ι α : Type*} [CommRing R] [IsDomain R] [Fintype ι] [Fintype α]

/-- Actual weighted monomial second moment, including arbitrary algebraic-integer nodes. -/
theorem monomial_second_moment_le (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (nodes : α → R) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 0 < k) (w : α → ℂ) :
    (∫ θ, ‖finiteWeylSum coord k nodes w θ‖ ^ 2 ∂latticeHaar) ≤
      (k : ℝ) * ∑ a, ‖w a‖ ^ 2 := by
  change (∫ θ, ‖frequencySum (fun a => coord (nodes a ^ k)) w θ‖ ^ 2 ∂latticeHaar) ≤ _
  apply integral_norm_frequencySum_sq_le _ _ k
  intro a
  classical
  have h := indexed_power_fiber_card_le nodes hnodes k hk (nodes a ^ k)
  simpa only [frequencyFiber, hcoord.eq_iff, eq_comm] using h

end SecondMoment

/-- The literal number-field specialization, with no coordinate-injectivity premise. -/
theorem numberField_monomial_second_moment_le (K : Type*) [Field K] [NumberField K]
    {α : Type*} [Fintype α] (nodes : α → 𝓞 K) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 0 < k) (w : α → ℂ) :
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 2 ∂latticeHaar) ≤
      (k : ℝ) * ∑ a, ‖w a‖ ^ 2 :=
  monomial_second_moment_le (integerCoordinates K) (integerCoordinates_injective K)
    nodes hnodes k hk w

section Differences
variable {R : Type*} [CommRing R]

/-- The ordinary finite difference, as an actual polynomial over the original ring. -/
def polynomialDifference (h : R) (p : R[X]) : R[X] := taylor h p - p

theorem polynomialDifference_eval (h x : R) (p : R[X]) :
    (polynomialDifference h p).eval x = p.eval (x + h) - p.eval x := by
  simp only [polynomialDifference, eval_sub, taylor_eval]

/-- Taylor's coefficient immediately below the leading degree, valid over any commutative ring. -/
theorem taylor_coeff_pred (p : R[X]) (h : R) (hn : 0 < p.natDegree) :
    (taylor h p).coeff (p.natDegree - 1) =
      (p.natDegree : R) * p.leadingCoeff * h + p.coeff (p.natDegree - 1) := by
  have hdeg : (hasseDeriv (p.natDegree - 1) p).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le _ _).trans (by omega)
  have hlinear := eq_X_add_C_of_natDegree_le_one hdeg
  rw [taylor_coeff, hlinear]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  have hnid : 1 + (p.natDegree - 1) = p.natDegree := by omega
  rw [hnid, show p.natDegree.choose (p.natDegree - 1) = p.natDegree by
    have h := Nat.choose_succ_self_right (p.natDegree - 1)
    simpa only [Nat.sub_add_cancel hn] using h, coeff_natDegree]

theorem polynomialDifference_natDegree_le (h : R) (p : R[X]) :
    (polynomialDifference h p).natDegree ≤ p.natDegree - 1 := by
  apply Polynomial.natDegree_le_pred
  · simpa only [polynomialDifference, natDegree_taylor, max_self] using
      Polynomial.natDegree_sub_le (taylor h p) p
  · simp only [polynomialDifference, coeff_sub, coeff_taylor_natDegree, coeff_natDegree, sub_self]

theorem polynomialDifference_coeff_pred (h : R) (p : R[X]) (hn : 0 < p.natDegree) :
    (polynomialDifference h p).coeff (p.natDegree - 1) =
      (p.natDegree : R) * p.leadingCoeff * h := by
  rw [polynomialDifference, coeff_sub, taylor_coeff_pred p h hn]
  ring

variable [IsDomain R] [CharZero R]

/-- A nonzero ordinary difference lowers positive degree by exactly one. -/
theorem polynomialDifference_natDegree (h : R) (hh : h ≠ 0) (p : R[X])
    (hn : 0 < p.natDegree) :
    (polynomialDifference h p).natDegree = p.natDegree - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (polynomialDifference_natDegree_le h p)
  rw [polynomialDifference_coeff_pred h p hn]
  have hp : p ≠ 0 := by intro hp; simp [hp] at hn
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hn.ne')
    (Polynomial.leadingCoeff_ne_zero.mpr hp)) hh

/-- Fixing a nonzero shift leaves at most `k−1` roots of a power-difference equation. -/
theorem shifted_power_fiber_card_le (S : Finset R) (k : ℕ) (hk : 2 ≤ k)
    (h : R) (hh : h ≠ 0) (a : R) :
    (S.filter (fun x => (x + h)^k - x^k = a)).card ≤ k - 1 := by
  classical
  let p : R[X] := polynomialDifference h (X ^ k) - C a
  have hd : p.natDegree = k - 1 := by
    dsimp [p]
    rw [natDegree_sub_C, polynomialDifference_natDegree h hh]
    · simp
    · simpa using (show 0 < k by omega)
  have hp : p ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hd; omega
  have hroots : ∀ x ∈ S.filter (fun x => (x + h)^k - x^k = a), p.eval x = 0 := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    simpa only [p, eval_sub, polynomialDifference_eval, eval_pow, eval_X, eval_C,
      sub_eq_zero] using hx'
  exact (polynomial_finite_roots_card_le p hp _ hroots).trans_eq hd

end Differences
end WaringSiegel.WSL2

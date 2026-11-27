import WaringSiegel.WSL2MomentHuaPolynomial

/-!
# Arbitrarily many genuine polynomial differences

The shift product divides the iterated difference as a polynomial, each
zero shift annihilates it, and nonzero shifts lower the degree exactly by
their number.  These are the algebraic inputs for the full Hua induction.
-/

noncomputable section
open Polynomial
open scoped BigOperators Classical

namespace WaringSiegel.WSL3
open WSL2

variable {R : Type*} [CommRing R]

def iteratedPolynomialDifference (p : R[X]) : (J : ℕ) → (Fin J → R) → R[X]
  | 0, _ => p
  | J + 1, h => polynomialDifference (h 0) (iteratedPolynomialDifference p J (Fin.tail h))

@[simp] theorem iteratedPolynomialDifference_zero (p : R[X]) (h : Fin 0 → R) :
    iteratedPolynomialDifference p 0 h = p := rfl

@[simp] theorem iteratedPolynomialDifference_cons (p : R[X]) (J : ℕ)
    (h : R) (t : Fin J → R) :
    iteratedPolynomialDifference p (J + 1) (Fin.cons h t) =
      polynomialDifference h (iteratedPolynomialDifference p J t) := by
  simp [iteratedPolynomialDifference]

theorem iteratedPolynomialDifference_C_mul (p : R[X]) (c : R) (J : ℕ) (h : Fin J → R) :
    iteratedPolynomialDifference (C c * p) J h = C c * iteratedPolynomialDifference p J h := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [iteratedPolynomialDifference, ih, polynomialDifference_C_mul]

theorem iteratedPolynomialDifference_product_dvd (p : R[X]) (J : ℕ) (h : Fin J → R) :
    C (∏ i, h i) ∣ iteratedPolynomialDifference p J h := by
  induction J with
  | zero => simp
  | succ J ih =>
    obtain ⟨q, hq⟩ := ih (Fin.tail h)
    obtain ⟨r, hr⟩ := polynomialDifference_C_dvd (h 0) q
    refine ⟨r, ?_⟩
    rw [iteratedPolynomialDifference, hq, polynomialDifference_C_mul, hr,
      Fin.prod_univ_succ, map_mul]
    simp only [Fin.tail]
    ring

theorem iteratedPolynomialDifference_eq_zero_of_shift_zero (p : R[X]) (J : ℕ)
    (h : Fin J → R) (i : Fin J) (hi : h i = 0) :
    iteratedPolynomialDifference p J h = 0 := by
  have hprod : ∏ j, h j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hd := iteratedPolynomialDifference_product_dvd p J h
  rwa [hprod, map_zero, zero_dvd_iff] at hd

theorem iteratedPolynomialDifference_shift_dvd_eval (p : R[X]) (J : ℕ)
    (h : Fin J → R) (i : Fin J) (x : R) :
    h i ∣ (iteratedPolynomialDifference p J h).eval x := by
  have hd : (∏ j, h j) ∣ (iteratedPolynomialDifference p J h).eval x := by
    simpa only [coe_evalRingHom, eval_C] using
      map_dvd (evalRingHom x) (iteratedPolynomialDifference_product_dvd p J h)
  exact (Finset.dvd_prod_of_mem h (Finset.mem_univ i)).trans hd

variable [IsDomain R] [CharZero R]

theorem iteratedPolynomialDifference_natDegree (p : R[X]) (J : ℕ) (h : Fin J → R)
    (hh : ∀ i, h i ≠ 0) (hJ : J ≤ p.natDegree) :
    (iteratedPolynomialDifference p J h).natDegree = p.natDegree - J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hd := ih (Fin.tail h) (fun i => hh i.succ) (by omega)
    rw [iteratedPolynomialDifference,
      polynomialDifference_natDegree (h 0) (hh 0) _ (by rw [hd]; omega), hd]
    omega

theorem iteratedPowerDifference_natDegree (k J : ℕ) (hJ : J ≤ k)
    (h : Fin J → R) (hh : ∀ i, h i ≠ 0) :
    (iteratedPolynomialDifference (X ^ k) J h).natDegree = k - J := by
  simpa only [natDegree_X_pow] using
    iteratedPolynomialDifference_natDegree (X ^ k) J h hh (by simpa using hJ)

theorem iteratedPowerDifference_fiber_card_le (S : Finset R) (k J : ℕ) (hJ : J < k)
    (h : Fin J → R) (hh : ∀ i, h i ≠ 0) (a : R) :
    (S.filter (fun x => (iteratedPolynomialDifference (X ^ k) J h).eval x = a)).card ≤ k - J := by
  let p := iteratedPolynomialDifference (X ^ k) J h - C a
  have hd : p.natDegree = k - J := by
    dsimp [p]
    rw [natDegree_sub_C, iteratedPowerDifference_natDegree k J hJ.le h hh]
  have hp : p ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hd; omega
  have hroots : ∀ x ∈ S.filter (fun x =>
      (iteratedPolynomialDifference (X ^ k) J h).eval x = a), p.eval x = 0 := by
    intro x hx
    simpa only [p, eval_sub, eval_C, sub_eq_zero] using (Finset.mem_filter.mp hx).2
  exact (polynomial_finite_roots_card_le p hp _ hroots).trans_eq hd

#print axioms iteratedPowerDifference_fiber_card_le

end WaringSiegel.WSL3

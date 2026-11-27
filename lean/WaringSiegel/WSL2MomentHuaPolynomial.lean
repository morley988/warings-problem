import WaringSiegel.WSL2MomentPolynomial

/-!
# Two genuine finite differences for the Hua eighth-moment step

These are literal polynomial identities over an arbitrary characteristic-zero
integral domain, including the ring of integers of every number field. No
moment estimate or root-count premise is assumed.
-/

noncomputable section
open Polynomial
open scoped BigOperators Classical

namespace WaringSiegel.WSL2

section Algebra
variable {R : Type*} [CommRing R]

theorem polynomialDifference_zero (p : R[X]) : polynomialDifference 0 p = 0 := by
  simp [polynomialDifference, taylor_zero]

theorem polynomialDifference_zero_polynomial (h : R) : polynomialDifference h (0 : R[X]) = 0 := by
  simp [polynomialDifference]

theorem double_polynomialDifference_eval (h₁ h₂ x : R) (p : R[X]) :
    (polynomialDifference h₂ (polynomialDifference h₁ p)).eval x =
      p.eval (x + h₂ + h₁) - p.eval (x + h₂) - p.eval (x + h₁) + p.eval x := by
  simp only [polynomialDifference_eval]
  ring

/-- Every ordinary difference is divisible by its shift, before evaluation. -/
theorem polynomialDifference_C_dvd (h : R) (p : R[X]) :
    C h ∣ polynomialDifference h p := by
  have hh := Polynomial.sub_dvd_eval_sub (X + C h) X (p.map C)
  rw [eval_map, eval_map] at hh
  change X + C h - X ∣ p.comp (X + C h) - p.comp X at hh
  simpa only [add_sub_cancel_left, comp_X, polynomialDifference, taylor_apply] using hh

theorem polynomialDifference_C_mul (h c : R) (p : R[X]) :
    polynomialDifference h (C c * p) = C c * polynomialDifference h p := by
  simp only [polynomialDifference, taylor_apply, mul_comp, C_comp, mul_sub]

/-- The product of both shifts divides the actual double difference. -/
theorem double_polynomialDifference_C_mul_dvd (h₁ h₂ : R) (p : R[X]) :
    C (h₁ * h₂) ∣ polynomialDifference h₂ (polynomialDifference h₁ p) := by
  obtain ⟨q, hq⟩ := polynomialDifference_C_dvd h₁ p
  obtain ⟨r, hr⟩ := polynomialDifference_C_dvd h₂ q
  rw [hq, polynomialDifference_C_mul, hr, ← mul_assoc, ← map_mul]
  exact dvd_mul_right _ _

theorem polynomialDifference_eval_dvd (h x : R) (p : R[X]) :
    h ∣ (polynomialDifference h p).eval x := by
  simpa only [coe_evalRingHom, eval_C] using map_dvd (evalRingHom x) (polynomialDifference_C_dvd h p)

theorem double_polynomialDifference_mul_dvd_eval (h₁ h₂ x : R) (p : R[X]) :
    h₁ * h₂ ∣ (polynomialDifference h₂ (polynomialDifference h₁ p)).eval x := by
  simpa only [coe_evalRingHom, eval_C] using map_dvd (evalRingHom x)
    (double_polynomialDifference_C_mul_dvd h₁ h₂ p)

theorem double_polynomialDifference_left_dvd_eval (h₁ h₂ x : R) (p : R[X]) :
    h₁ ∣ (polynomialDifference h₂ (polynomialDifference h₁ p)).eval x :=
  (dvd_mul_right h₁ h₂).trans (double_polynomialDifference_mul_dvd_eval h₁ h₂ x p)

theorem double_polynomialDifference_right_dvd_eval (h₁ h₂ x : R) (p : R[X]) :
    h₂ ∣ (polynomialDifference h₂ (polynomialDifference h₁ p)).eval x :=
  (dvd_mul_left h₂ h₁).trans (double_polynomialDifference_mul_dvd_eval h₁ h₂ x p)

theorem double_polynomialDifference_zero_of_shift_zero (h₁ h₂ : R) (p : R[X])
    (h : h₁ = 0 ∨ h₂ = 0) : polynomialDifference h₂ (polynomialDifference h₁ p) = 0 := by
  rcases h with rfl | rfl <;> simp [polynomialDifference_zero, polynomialDifference_zero_polynomial]

/-- The exact cubic double difference, useful at the first nontrivial Hua step. -/
theorem cubic_double_polynomialDifference_eval (h₁ h₂ x : R) :
    (polynomialDifference h₂ (polynomialDifference h₁ (X ^ 3))).eval x =
      6 * h₁ * h₂ * x + 3 * h₁ * h₂ * (h₁ + h₂) := by
  rw [double_polynomialDifference_eval]
  simp only [eval_pow, eval_X]
  ring

end Algebra

section Degrees
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

theorem polynomialDifference_leadingCoeff (h : R) (hh : h ≠ 0) (p : R[X])
    (hn : 0 < p.natDegree) :
    (polynomialDifference h p).leadingCoeff = (p.natDegree : R) * p.leadingCoeff * h := by
  change (polynomialDifference h p).coeff (polynomialDifference h p).natDegree = _
  rw [polynomialDifference_natDegree h hh p hn, polynomialDifference_coeff_pred h p hn]

theorem double_polynomialDifference_natDegree (h₁ h₂ : R) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0)
    (p : R[X]) (hn : 2 ≤ p.natDegree) :
    (polynomialDifference h₂ (polynomialDifference h₁ p)).natDegree = p.natDegree - 2 := by
  have hfirst := polynomialDifference_natDegree h₁ hh₁ p (by omega)
  rw [polynomialDifference_natDegree h₂ hh₂ _ (by rw [hfirst]; omega), hfirst]
  omega

theorem double_powerDifference_natDegree (k : ℕ) (hk : 2 ≤ k)
    (h₁ h₂ : R) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    (polynomialDifference h₂ (polynomialDifference h₁ (X ^ k))).natDegree = k - 2 := by
  simpa only [natDegree_X_pow] using
    double_polynomialDifference_natDegree h₁ h₂ hh₁ hh₂ (X ^ k) (by simpa using hk)

theorem double_powerDifference_leadingCoeff (k : ℕ) (hk : 2 ≤ k)
    (h₁ h₂ : R) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    (polynomialDifference h₂ (polynomialDifference h₁ (X ^ k))).leadingCoeff =
      (k : R) * ((k - 1 : ℕ) : R) * h₁ * h₂ := by
  have hdeg : (polynomialDifference h₁ (X ^ k)).natDegree = k - 1 := by
    rw [polynomialDifference_natDegree h₁ hh₁ _ (by simpa using (show 0 < k by omega)), natDegree_X_pow]
  rw [polynomialDifference_leadingCoeff h₂ hh₂ _ (by rw [hdeg]; omega), hdeg,
    polynomialDifference_leadingCoeff h₁ hh₁ _ (by simpa using (show 0 < k by omega))]
  simp only [natDegree_X_pow, leadingCoeff_X_pow, mul_one]
  ring

/-- The actual fiber of a double-difference equation has at most k−2 roots
when the shifts are nonzero and the remaining degree is positive. -/
theorem double_powerDifference_fiber_card_le (S : Finset R) (k : ℕ) (hk : 3 ≤ k)
    (h₁ h₂ : R) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) (a : R) :
    (S.filter (fun x =>
      (polynomialDifference h₂ (polynomialDifference h₁ (X ^ k))).eval x = a)).card ≤ k - 2 := by
  let p : R[X] := polynomialDifference h₂ (polynomialDifference h₁ (X ^ k)) - C a
  have hd : p.natDegree = k - 2 := by
    dsimp [p]
    rw [natDegree_sub_C, double_powerDifference_natDegree k (by omega) h₁ h₂ hh₁ hh₂]
  have hp : p ≠ 0 := by intro hz; rw [hz, natDegree_zero] at hd; omega
  have hroots : ∀ x ∈ S.filter (fun x =>
      (polynomialDifference h₂ (polynomialDifference h₁ (X ^ k))).eval x = a), p.eval x = 0 := by
    intro x hx
    simpa only [p, eval_sub, eval_C, sub_eq_zero] using (Finset.mem_filter.mp hx).2
  exact (polynomial_finite_roots_card_le p hp _ hroots).trans_eq hd

end Degrees
end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.double_powerDifference_fiber_card_le
#print axioms WaringSiegel.WSL2.double_polynomialDifference_mul_dvd_eval

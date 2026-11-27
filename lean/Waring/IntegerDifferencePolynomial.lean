import Waring.DifferencePolynomials
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.Monomial

/-!
# Integer polynomials for every modified centered difference

The normalizing division by m^k is exact at the polynomial level. Factoring
p(X+a)-p(X-a) by 2a constructs its integer quotient, where a=h*m^k.
Iterating gives an integer polynomial whose real evaluation is the actual
recursive modifiedCenteredPower used throughout the analytic development.
Each difference lowers the degree bound by one.
-/

noncomputable section
namespace Waring.IntegerDifferencePolynomial
open Polynomial Differences

def difference (k : ℕ) (h m : ℤ) (p : Polynomial ℤ) : Polynomial ℤ :=
  C (2*h) * (Polynomial.evalSubFactor (p.map C)
    (X+C (h*m^k)) (X-C (h*m^k))).val

/-- Exact divisibility before any real-number interpretation. -/
theorem difference_mul (k : ℕ) (h m : ℤ) (p : Polynomial ℤ) :
    C (m^k) * difference k h m p =
      p.comp (X+C (h*m^k)) - p.comp (X-C (h*m^k)) := by
  have H := (Polynomial.evalSubFactor (p.map C)
    (X+C (h*m^k)) (X-C (h*m^k))).property
  simp only [Polynomial.eval_map] at H
  change p.comp (X+C (h*m^k))-p.comp (X-C (h*m^k)) = _ at H
  rw [H]
  unfold difference
  simp only [map_mul,map_pow,map_ofNat]
  ring

theorem centered_difference_natDegree_le (p : Polynomial ℤ) (a : ℤ) :
    (p.comp (X+C a) - p.comp (X-C a)).natDegree ≤ p.natDegree-1 := by
  have heq : X-C a = X+C (-a) := by simp [sub_eq_add_neg]
  rw [heq]
  change (taylor a p-taylor (-a) p).natDegree ≤ _
  apply Polynomial.natDegree_le_pred
  · simpa only [Polynomial.natDegree_taylor,max_self] using
      Polynomial.natDegree_sub_le (taylor a p) (taylor (-a) p)
  · simp only [Polynomial.coeff_sub,Polynomial.coeff_taylor_natDegree,sub_self]

theorem difference_natDegree_le (k : ℕ) (h m : ℤ) (p : Polynomial ℤ) (hm : m ≠ 0) :
    (difference k h m p).natDegree ≤ p.natDegree-1 := by
  have H := centered_difference_natDegree_le p (h*m^k)
  rw [← difference_mul,Polynomial.natDegree_C_mul (pow_ne_zero k hm)] at H
  exact H

/-- The real value is exactly the normalized centered difference. -/
theorem difference_eval_real (k : ℕ) (h m : ℤ) (p : Polynomial ℤ)
    (hm : m ≠ 0) (z : ℝ) :
    (difference k h m p).eval₂ (Int.castRingHom ℝ) z =
      (p.eval₂ (Int.castRingHom ℝ) (z+(h : ℝ)*(m : ℝ)^k) -
       p.eval₂ (Int.castRingHom ℝ) (z-(h : ℝ)*(m : ℝ)^k)) / (m : ℝ)^k := by
  have H := congrArg (fun q : Polynomial ℤ => q.eval₂ (Int.castRingHom ℝ) z)
    (difference_mul k h m p)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_sub,
    Polynomial.eval₂_comp,Polynomial.eval₂_add,Polynomial.eval₂_X,
    Polynomial.eval₂_pow,map_mul,map_pow] at H
  have hmR : (m : ℝ)^k ≠ 0 := pow_ne_zero k (by exact_mod_cast hm)
  apply (eq_div_iff hmR).mpr
  change (m : ℝ)^k * (difference k h m p).eval₂ (Int.castRingHom ℝ) z =
    p.eval₂ (Int.castRingHom ℝ) (z+(h : ℝ)*(m : ℝ)^k) -
    p.eval₂ (Int.castRingHom ℝ) (z-(h : ℝ)*(m : ℝ)^k) at H
  linear_combination H

def powerPolynomial (k : ℕ) : List (ℤ × ℤ) → Polynomial ℤ
  | [] => X^k
  | hm :: rest => difference k hm.1 hm.2 (powerPolynomial k rest)

def realParameters (params : List (ℤ × ℤ)) : List (ℝ × ℝ) :=
  params.map (fun hm => ((hm.1 : ℝ),(hm.2 : ℝ)))

/-- A single polynomial represents the source phase for every real center. -/
theorem powerPolynomial_eval_real (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (z : ℝ) :
    (powerPolynomial k params).eval₂ (Int.castRingHom ℝ) z =
      modifiedCenteredPower k (realParameters params) z := by
  induction params generalizing z with
  | nil => simp [powerPolynomial,realParameters,modifiedCenteredPower]
  | cons p rest ih =>
    have hmrest : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    simp only [powerPolynomial,realParameters,List.map_cons,modifiedCenteredPower]
    rw [difference_eval_real k p.1 p.2 _ (hm p (List.mem_cons_self ..)),
      ih hmrest,ih hmrest]
    rfl

/-- Integer centers give literal integer frequencies for Fourier orthogonality. -/
theorem powerPolynomial_eval_int (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (z : ℤ) :
    (((powerPolynomial k params).eval z : ℤ) : ℝ) =
      modifiedCenteredPower k (realParameters params) (z : ℝ) := by
  change (Int.castRingHom ℝ) ((powerPolynomial k params).eval z) = _
  rw [← Polynomial.eval₂_at_apply (Int.castRingHom ℝ)]
  exact powerPolynomial_eval_real k params hm (z : ℝ)

/-- The actual source degree decreases at every nonzero coefficient step. -/
theorem powerPolynomial_natDegree_le (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) :
    (powerPolynomial k params).natDegree ≤ k-params.length := by
  induction params with
  | nil => simp [powerPolynomial]
  | cons p rest ih =>
    have hmrest : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hm p (List.mem_cons_of_mem _ hp)
    have h := (difference_natDegree_le k p.1 p.2 (powerPolynomial k rest)
      (hm p (List.mem_cons_self ..))).trans (Nat.sub_le_sub_right (ih hmrest) 1)
    simpa only [powerPolynomial,List.length_cons,Nat.sub_sub,Nat.add_comm rest.length 1] using h

#print axioms difference_mul
#print axioms powerPolynomial_eval_int
#print axioms powerPolynomial_natDegree_le
end Waring.IntegerDifferencePolynomial

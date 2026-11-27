import Waring.PolicyCompletionPositivePhase
import Waring.PolicyCompletionPolynomialGcd
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Exact leading coefficient and common height factor of the source phase

The complete-sum gcd loss involves the product of the differencing heights.
These identities prove that factor for every depth, independently of the
coefficient variables, and identify the fixed factorial multiplier exactly.
-/

noncomputable section
namespace Waring.PolicyCompletionPhaseContent
open Polynomial IntegerDifferencePolynomial PolicyCompletionPositivePhase
open PolicyCompletionPolynomialGcd

def heightProduct (params : List (ℤ × ℤ)) : ℤ := (params.map Prod.fst).prod

def leadingMultiplier (k j : ℕ) : ℕ := 2^j*k.descFactorial j

theorem difference_C_mul (k : ℕ) (h m H : ℤ) (f : Polynomial ℤ) (hm : m≠0) :
    difference k h m (C H*f) = C H*difference k h m f := by
  apply mul_left_cancel₀ (a := C (m^k)) (Polynomial.C_ne_zero.mpr (pow_ne_zero k hm))
  rw [difference_mul]
  calc
    _ = C H*(f.comp (X+C (h*m^k))-f.comp (X-C (h*m^k))) := by
      simp only [Polynomial.mul_comp, Polynomial.C_comp]
      ring
    _ = _ := by rw [← difference_mul]; ring

theorem powerPolynomial_height_factor (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2≠0) :
    ∃ g : Polynomial ℤ, powerPolynomial k params = C (heightProduct params)*g := by
  induction params with
  | nil => exact ⟨X^k, by simp [powerPolynomial, heightProduct]⟩
  | cons p rest ih =>
    obtain ⟨g,hg⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
    refine ⟨C 2*(Polynomial.evalSubFactor (g.map C)
      (X+C (p.1*p.2^k)) (X-C (p.1*p.2^k))).val, ?_⟩
    rw [powerPolynomial, hg, difference_C_mul k p.1 p.2 _ g (hm p (List.mem_cons_self ..))]
    simp only [heightProduct, List.map_cons, List.prod_cons, difference, map_mul]
    ring

theorem heightProduct_dvd_coeff (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2≠0) (i : ℕ) :
    heightProduct params ∣ (powerPolynomial k params).coeff i := by
  obtain ⟨g,hg⟩ := powerPolynomial_height_factor k params hm
  rw [hg, Polynomial.coeff_C_mul]
  exact dvd_mul_right _ _

theorem powerPolynomial_leadingCoeff (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, hm.1≠0 ∧ hm.2≠0) (hlen : params.length≤k) :
    (powerPolynomial k params).leadingCoeff =
      (leadingMultiplier k params.length : ℤ)*heightProduct params := by
  induction params with
  | nil => simp [powerPolynomial, leadingMultiplier, heightProduct]
  | cons p rest ih =>
    have hrest : ∀ q ∈ rest, q.1≠0 ∧ q.2≠0 :=
      fun q hq => hparams q (List.mem_cons_of_mem _ hq)
    have hlenrest : rest.length≤k := by simp only [List.length_cons] at hlen; omega
    have hdeg := powerPolynomial_natDegree k rest hrest hlenrest
    have hdegpos : 0<(powerPolynomial k rest).natDegree := by
      rw [hdeg]
      simp only [List.length_cons] at hlen
      omega
    rw [powerPolynomial, difference_leadingCoeff k p.1 p.2 _
      (hparams p (List.mem_cons_self ..)).1 (hparams p (List.mem_cons_self ..)).2 hdegpos,
      hdeg, ih hrest hlenrest]
    simp only [leadingMultiplier, heightProduct, List.length_cons, List.map_cons, List.prod_cons,
      Nat.descFactorial_succ, pow_succ, Nat.cast_mul]
    ring

theorem powerPolynomial_coefficient_relation (k : ℕ) (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, hm.1≠0 ∧ hm.2≠0) (hlen : params.length≤k) (i : ℕ) :
    ∃ L : ℤ, (leadingMultiplier k params.length : ℤ)*(powerPolynomial k params).coeff i =
      (powerPolynomial k params).coeff (k-params.length)*L := by
  obtain ⟨L,hL⟩ := heightProduct_dvd_coeff k params (fun p hp => (hparams p hp).2) i
  refine ⟨L, ?_⟩
  rw [← powerPolynomial_natDegree k params hparams hlen, Polynomial.coeff_natDegree,
    powerPolynomial_leadingCoeff k params hparams hlen, hL]
  ring

/-- An arbitrary linear twist retains only a fixed multiple of its own
frequency in the common coefficient divisor. -/
theorem coefficientDivisorBoundAt_linear_twist (q d : ℕ) (hd : 2≤d)
    (f : Polynomial ℤ) (K L b : ℤ) (hrel : K*f.coeff 1=f.coeff d*L) :
    CoefficientDivisorBoundAt q (f+C b*X) (K*b).natAbs := by
  intro n hn hcoeff
  have h1 := hcoeff 1 (by omega)
  have hd' := hcoeff d (by omega)
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X] at h1
  have hdne : d≠1 := by omega
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, hdne, Ne.symm hdne] at hd'
  apply Int.natCast_dvd.mp
  have hh : (n:ℤ) ∣ K*(f.coeff 1+b)-f.coeff d*L :=
    dvd_sub (dvd_mul_of_dvd_right h1 K) (dvd_mul_of_dvd_left hd' L)
  have heq : K*(f.coeff 1+b)-f.coeff d*L=K*b := by rw [← hrel]; ring
  rwa [heq] at hh

#print axioms powerPolynomial_height_factor
#print axioms powerPolynomial_leadingCoeff
#print axioms coefficientDivisorBoundAt_linear_twist
end Waring.PolicyCompletionPhaseContent

import Waring.EndgameCompletionStationary
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Taylor

/-! # Exact stationary filtering for arbitrary polynomial phases

The auxiliary major arcs need a complete polynomial sum, including arbitrary
linear twists. These are exact finite identities over residue rings. The
normalized derivative variant also handles primes dividing the degree by
using a sufficiently deep square-zero shift.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialStationary
open Polynomial EndgameCompletion

def completePolynomialSum (q : ℕ) [NeZero q] (f : Polynomial (ZMod q)) : ℂ :=
  ∑ x : ZMod q,ZMod.stdAddChar (f.eval x)

theorem polynomial_eval_add_of_sq_zero {R : Type*} [CommRing R]
    (f : Polynomial R) (x y : R) (hy : y^2=0) :
    f.eval (x+y)=f.eval x+f.derivative.eval x*y := by
  obtain ⟨a,ha⟩ := f.binomExpansion x y
  simpa only [hy,mul_zero,add_zero] using ha

/-- Averaging square-zero shifts removes every nonstationary residue. -/
theorem completePolynomialSum_stationary_filter (q M : ℕ) [NeZero q]
    (hM : 0 < M) (f : Polynomial (ZMod q)) (h : ZMod q)
    (hh : h^2=0) (hMh : (M : ZMod q)*h=0) :
    completePolynomialSum q f =
      ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter
        (fun x => f.derivative.eval x*h=0),ZMod.stdAddChar (f.eval x) := by
  have hshift (t : ℕ) :
      (∑ x : ZMod q,ZMod.stdAddChar (f.eval (x+h*(t : ZMod q)))) =
        completePolynomialSum q f := by
    unfold completePolynomialSum
    exact Fintype.sum_equiv (Equiv.addRight (h*(t : ZMod q))) _ _ (fun _ => rfl)
  have hlinear (x : ZMod q) :
      (∑ t ∈ Finset.range M,ZMod.stdAddChar ((f.derivative.eval x*h)*(t : ZMod q))) =
        if f.derivative.eval x*h=0 then (M : ℂ) else 0 := by
    apply stdAddChar_sum_range
    calc
      _ = f.derivative.eval x*((M : ZMod q)*h) := by ring
      _ = 0 := by rw [hMh,mul_zero]
  have havg : (M : ℂ)*completePolynomialSum q f =
      ∑ x : ZMod q,ZMod.stdAddChar (f.eval x)*
        (∑ t ∈ Finset.range M,ZMod.stdAddChar ((f.derivative.eval x*h)*(t : ZMod q))) := by
    calc
      _ = ∑ _t ∈ Finset.range M,completePolynomialSum q f := by simp
      _ = ∑ t ∈ Finset.range M,∑ x : ZMod q,
          ZMod.stdAddChar (f.eval (x+h*(t : ZMod q))) :=
        Finset.sum_congr rfl (fun t _ => (hshift t).symm)
      _ = ∑ x : ZMod q,∑ t ∈ Finset.range M,
          ZMod.stdAddChar (f.eval (x+h*(t : ZMod q))) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        have hht : (h*(t : ZMod q))^2=0 := by rw [mul_pow,hh,zero_mul]
        rw [polynomial_eval_add_of_sq_zero f x (h*(t : ZMod q)) hht,
          AddChar.map_add_eq_mul,mul_assoc]
  simp_rw [hlinear] at havg
  apply mul_left_cancel₀ (a := (M : ℂ)) (by exact_mod_cast Nat.ne_of_gt hM)
  calc
    _ = ∑ x : ZMod q,ZMod.stdAddChar (f.eval x)*
        (if f.derivative.eval x*h=0 then (M : ℂ) else 0) := havg
    _ = _ := by
      rw [Finset.mul_sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [mul_comm]

/-- Derivative content is retained explicitly. When m>=2t+2 the shift
p^(m-t-1) is square zero, and the stationary condition is D(x)=0 mod p. -/
theorem completePolynomialSum_primitiveDerivative_filter {p : ℕ} [Fact p.Prime]
    (m t : ℕ) (hm : 2*t+2 ≤ m) (f D : Polynomial ℤ)
    (hder : f.derivative=C ((p : ℤ)^t)*D) :
    completePolynomialSum (p^m) (f.map (Int.castRingHom (ZMod (p^m)))) =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^m))).filter
        (fun x => p ∣ ((D.map (Int.castRingHom (ZMod (p^m)))).eval x).val),
        ZMod.stdAddChar ((f.map (Int.castRingHom (ZMod (p^m)))).eval x) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let h : ZMod (p^m) := ((p^(m-t-1) : ℕ) : ZMod (p^m))
  have hh : h^2=0 := by
    dsimp [h]
    rw [← Nat.cast_pow,ZMod.natCast_eq_zero_iff,← pow_mul]
    exact pow_dvd_pow p (by omega)
  have hperiod : ((p^(t+1) : ℕ) : ZMod (p^m))*h=0 := by
    dsimp [h]
    rw [← Nat.cast_mul,← pow_add,show t+1+(m-t-1)=m by omega,ZMod.natCast_self]
  have hiff (x : ZMod (p^m)) :
      (f.map (Int.castRingHom (ZMod (p^m)))).derivative.eval x*h=0 ↔
        p ∣ ((D.map (Int.castRingHom (ZMod (p^m)))).eval x).val := by
    have he : (f.map (Int.castRingHom (ZMod (p^m)))).derivative.eval x*h=
        ((D.map (Int.castRingHom (ZMod (p^m)))).eval x)*((p^(m-1) : ℕ) : ZMod (p^m)) := by
      rw [Polynomial.derivative_map,hder,Polynomial.map_mul,Polynomial.map_C,
        Polynomial.eval_mul,Polynomial.eval_C]
      simp only [map_pow,map_natCast]
      dsimp [h]
      rw [Nat.cast_pow,Nat.cast_pow]
      calc
        _ = ((D.map (Int.castRingHom (ZMod (p^m)))).eval x)*
          ((p : ZMod (p^m))^t*(p : ZMod (p^m))^(m-t-1)) := by ring
        _ = _ := by rw [← pow_add,show t+(m-t-1)=m-1 by omega]
    rw [he]
    exact primepower_annihilator_iff m (by omega) _
  rw [completePolynomialSum_stationary_filter (p^m) (p^(t+1)) (pow_pos hp _) _ h hh hperiod]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hiff x
  · intro x _
    rfl

#print axioms completePolynomialSum_stationary_filter
#print axioms completePolynomialSum_primitiveDerivative_filter
end Waring.PolicyCompletionPolynomialStationary

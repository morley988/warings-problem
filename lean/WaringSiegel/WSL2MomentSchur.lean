import WaringSiegel.WSL2MomentPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# An elementary Schur prime-divisor step

A nonconstant integer polynomial has a nonzero value divisible by a prime
outside any prescribed nonzero integer.  This supplies the prime-divisor
part of the proposed degree-one-place VMVT route; the Kummer--Dedekind
construction of the actual prime ideal is separate.
-/

noncomputable section
open Polynomial

namespace WaringSiegel.WSL2

theorem integer_polynomial_exists_nonzero_eval (f : ℤ[X]) (hf : f≠0) :
    ∃n : ℤ, f.eval n≠0 := by
  by_contra h
  push_neg at h
  apply hf
  apply Polynomial.funext
  intro n
  simpa only [eval_zero] using h n

/-- Schur's prime-divisor argument, initially based at a nonzero constant term. -/
theorem polynomial_prime_divisor_outside_of_eval_zero_ne
    (f : ℤ[X]) (hf : 0<f.natDegree) (hzero : f.eval 0≠0)
    (D : ℤ) (hD : D≠0) :
    ∃p : ℕ, p.Prime ∧ ¬(p : ℤ)∣D ∧ ∃n : ℤ, f.eval n≠0 ∧ (p : ℤ)∣f.eval n := by
  let a := f.eval 0
  let g := f.comp (C (a*D)*X)
  have hdeg : g.natDegree=f.natDegree := by
    dsimp [g]
    rw [natDegree_comp,natDegree_C_mul_X _ (mul_ne_zero hzero hD),mul_one]
  have hgC (b : ℤ) : g≠C b := by
    intro heq
    have hh := congrArg natDegree heq
    rw [hdeg,natDegree_C] at hh
    omega
  have hg0 : g≠0 := by simpa only [C_0] using hgC 0
  have hg1 : g-C a≠0 := sub_ne_zero.mpr (hgC a)
  have hg2 : g-C (-a)≠0 := sub_ne_zero.mpr (hgC (-a))
  obtain ⟨t,ht⟩ := integer_polynomial_exists_nonzero_eval
    (g*(g-C a)*(g-C (-a))) (mul_ne_zero (mul_ne_zero hg0 hg1) hg2)
  simp only [eval_mul,mul_ne_zero_iff,eval_sub,eval_C,sub_ne_zero] at ht
  let b := (a*D)*t
  have hgb : g.eval t=f.eval b := by simp [g,b]
  rw [hgb] at ht
  have hd : a*D∣f.eval b-a := by
    apply dvd_trans (show a*D∣b by exact ⟨t,rfl⟩)
    simpa only [sub_zero] using Polynomial.sub_dvd_eval_sub b 0 f
  obtain ⟨z,hz⟩ := hd
  let c := 1+D*z
  have hfc : f.eval b=a*c := by dsimp [c]; nlinarith [hz]
  have hc : c.natAbs≠1 := by
    intro heq
    have habs : c.natAbs=(1 : ℤ).natAbs := by simpa using heq
    rcases Int.natAbs_eq_natAbs_iff.mp habs with hc1 | hcm1
    · exact ht.1.2 (by rw [hfc,hc1,mul_one])
    · exact ht.2 (by rw [hfc,hcm1]; ring)
  obtain ⟨p,hp,hpc⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hc
  have hpcZ : (p : ℤ)∣c := Int.natCast_dvd.mpr hpc
  refine ⟨p,hp,?_,b,ht.1.1,?_⟩
  · intro hpd
    have hone : (p : ℤ)∣1 := by
      have hh := dvd_sub hpcZ (dvd_mul_of_dvd_left hpd z)
      convert hh using 1 <;> dsimp [c] <;> ring
    have hpn : p∣1 := by exact_mod_cast hone
    exact hp.ne_one (Nat.eq_one_of_dvd_one hpn)
  · rw [hfc]
    exact dvd_mul_of_dvd_right hpcZ a

/-- A nonconstant polynomial has a prime divisor outside every prescribed
finite set of prime divisors, with the evaluated value required to be nonzero. -/
theorem polynomial_prime_divisor_outside
    (f : ℤ[X]) (hf : 0<f.natDegree) (D : ℤ) (hD : D≠0) :
    ∃p : ℕ, p.Prime ∧ ¬(p : ℤ)∣D ∧ ∃n : ℤ, f.eval n≠0 ∧ (p : ℤ)∣f.eval n := by
  have hf0 : f≠0 := by intro heq; simp [heq] at hf
  obtain ⟨a,ha⟩ := integer_polynomial_exists_nonzero_eval f hf0
  let g := f.comp (X+C a)
  have hgdeg : 0<g.natDegree := by simpa only [g,natDegree_comp,natDegree_X_add_C,mul_one] using hf
  have hg0 : g.eval 0≠0 := by simpa [g] using ha
  obtain ⟨p,hp,hpD,n,hn,hpn⟩ := polynomial_prime_divisor_outside_of_eval_zero_ne g hgdeg hg0 D hD
  refine ⟨p,hp,hpD,n+a,?_,?_⟩
  · simpa [g] using hn
  · simpa [g] using hpn

/-- The new prime may also be required to exceed an arbitrary prescribed bound. -/
theorem polynomial_large_prime_divisor_outside
    (f : ℤ[X]) (hf : 0<f.natDegree) (D : ℤ) (hD : D≠0) (k : ℕ) :
    ∃p : ℕ, p.Prime ∧ k<p ∧ ¬(p : ℤ)∣D ∧
      ∃n : ℤ, f.eval n≠0 ∧ (p : ℤ)∣f.eval n := by
  have hfact : (k.factorial : ℤ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  obtain ⟨p,hp,hpD,n,hn,hpn⟩ :=
    polynomial_prime_divisor_outside f hf (D*(k.factorial:ℤ)) (mul_ne_zero hD hfact)
  refine ⟨p,hp,?_,?_,n,hn,hpn⟩
  · by_contra hpk
    have hpf : p∣k.factorial := Nat.dvd_factorial hp.pos (Nat.le_of_not_gt hpk)
    have hpfZ : (p:ℤ)∣(k.factorial:ℤ) := by exact_mod_cast hpf
    exact hpD (dvd_mul_of_dvd_right hpfZ D)
  · intro hpd
    exact hpD (dvd_mul_of_dvd_left hpd (k.factorial:ℤ))

end WaringSiegel.WSL2

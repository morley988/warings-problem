import WaringSiegel.WSL4RamanujamCoefficientSharp
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Polynomial coefficients and finite sums as actual bounded power lists -/
noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WSL4
variable {R : Type*} [CommRing R]

theorem finite_sum_power_list {ι : Type*} (s : Finset ι) (k : ℕ)
    (a : ι → R) (N : ι → ℕ)
    (h : ∀i∈s,∃l : List R,l.length≤N i ∧ localPowerListSum k l=a i) :
    ∃l : List R,l.length≤∑i∈s,N i ∧ localPowerListSum k l=∑i∈s,a i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨l,hlen,hl⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨m,hm,he⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨l++m,?_,?_⟩
    · simpa only [List.length_append,Finset.sum_insert hi] using Nat.add_le_add hlen hm
    · rw [localPowerListSum_append,hl,he,Finset.sum_insert hi]

theorem polynomial_eval_power_list (P : R[X]) (k N d : ℕ) (x : R)
    (hd : P.natDegree≤d)
    (h : ∀i≤d,∃l : List R,l.length≤N ∧ localPowerListSum k l=P.coeff i) :
    ∃l : List R,l.length≤N*(d+1) ∧ localPowerListSum k l=P.eval (x^k) := by
  obtain ⟨l,hlen,hl⟩ := finite_sum_power_list (Finset.range (d+1)) k
    (fun i => P.coeff i*(x^k)^i) (fun _ => N) (by
      intro i hi
      have hi' : i≤d := by have := Finset.mem_range.mp hi; omega
      obtain ⟨l,hlen,hl⟩ := h i hi'
      refine ⟨l.map (x^i*·),by simpa using hlen,?_⟩
      rw [localPowerListSum_map_mul,hl]
      change (x^i)^k*P.coeff i=P.coeff i*(x^k)^i
      simp only [← pow_mul,Nat.mul_comm i k,mul_comm])
  refine ⟨l,by simpa [Nat.mul_comm] using hlen,?_⟩
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree<d+1)]
  exact hl

theorem scalar_integer_polynomial_power_list
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (p n r d : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) (P : ℤ[X]) (hd : P.natDegree≤d)
    (c x : R) (hc : c∈rationalPrimeCoefficientRing p R) :
    ∃l : List R,l.length≤4*(n*p^r)*(d+1) ∧
      localPowerListSum (n*p^r) l=c*P.eval₂ (Int.castRingHom R) (x^(n*p^r)) := by
  let Q : R[X] := C c*P.map (Int.castRingHom R)
  have hQ : Q.natDegree≤d := by
    have h1 := Polynomial.natDegree_mul_le (p:=C c) (q:=P.map (Int.castRingHom R))
    simp only [natDegree_C,zero_add] at h1
    have hmap : (P.map (Int.castRingHom R)).natDegree≤P.natDegree := Polynomial.natDegree_map_le
    exact h1.trans (hmap.trans hd)
  have hcoeff : ∀i≤d,∃l : List R,l.length≤4*(n*p^r) ∧
      localPowerListSum (n*p^r) l=Q.coeff i := by
    intro i hi
    apply rationalPrimeCoefficient_power_list_sharp p n r hn hnu
    change (C c*P.map (Int.castRingHom R)).coeff i∈rationalPrimeCoefficientRing p R
    rw [coeff_C_mul,coeff_map]
    exact (rationalPrimeCoefficientRing p R).mul_mem hc
      (mem_rationalPrimeCoefficientRing_intCast p (P.coeff i))
  obtain ⟨l,hlen,hl⟩ := polynomial_eval_power_list Q (n*p^r) (4*(n*p^r)) d x hQ hcoeff
  refine ⟨l,hlen,?_⟩
  simpa only [Q,eval_mul,eval_C,eval_map] using hl

#print axioms finite_sum_power_list
#print axioms polynomial_eval_power_list
#print axioms scalar_integer_polynomial_power_list
end WaringSiegel.WSL4Local

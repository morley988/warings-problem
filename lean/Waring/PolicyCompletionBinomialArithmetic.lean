import Waring.PolicyCompletionBinomialRoots
import Mathlib.Algebra.Ring.GeomSum

/-!
# Actual positive divided differences and their residue fibers

The integer quotient used in the basic coefficient proof equals a positive
geometric polynomial. Its derivative-scale lower and upper bounds are
proved term by term. Coprimality with a quotient divisor follows from the
original gcd(n,n+l)=1 condition and is not an additional source assumption.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBinomialArithmetic
open PolicyCompletionBinomialRoots

def natQuotient (d n l : ℕ) : ℕ :=
  ∑i∈Finset.range d,(n+l)^i*n^(d-1-i)

theorem differenceQuotient_eq_natQuotient (d n l : ℕ) (hl : 0<l) :
    differenceQuotient d n l=(natQuotient d n l : ℤ) := by
  have hlZ : (l : ℤ)≠0 := by exact_mod_cast hl.ne'
  unfold differenceQuotient
  rw [← geom_sum₂_mul,show (n : ℤ)+(l : ℤ)-(n : ℤ)=(l : ℤ) by ring,
    Int.mul_ediv_cancel _ hlZ]
  simp only [natQuotient,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_add]

theorem natQuotient_bounds (d n l : ℕ) :
    d*n^(d-1)≤natQuotient d n l ∧ natQuotient d n l≤d*(n+l)^(d-1) := by
  have hi (i : ℕ) (hi : i∈Finset.range d) : i+(d-1-i)=d-1 := by
    have := Finset.mem_range.mp hi
    omega
  constructor
  · calc
      _ = ∑_i∈Finset.range d,n^(d-1) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi'
        calc
          n^(d-1)=n^i*n^(d-1-i) := by rw [← pow_add,hi i hi']
          _ ≤ (n+l)^i*n^(d-1-i) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
  · calc
      _ ≤ ∑_i∈Finset.range d,(n+l)^(d-1) := by
        apply Finset.sum_le_sum
        intro i hi'
        calc
          (n+l)^i*n^(d-1-i)≤(n+l)^i*(n+l)^(d-1-i) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)
          _ = (n+l)^(d-1) := by rw [← pow_add,hi i hi']
      _ = _ := by simp

theorem natQuotient_pos {d n : ℕ} (hd : 0<d) (hn : 0<n) (l : ℕ) :
    0<natQuotient d n l :=
  (Nat.mul_pos hd (pow_pos hn _)).trans_le (natQuotient_bounds d n l).1

/-- A divisor of the quotient is automatically coprime to both endpoints. -/
theorem quotient_divisor_coprime {d n l q : ℕ} (hd : 0<d)
    (hcop : Nat.Coprime n (n+l)) (hdiv : (q : ℤ)∣differenceQuotient d n l) :
    Nat.Coprime (n*(n+l)) q := by
  have hqdiff : (q : ℤ)∣((n : ℤ)+(l : ℤ))^d-(n : ℤ)^d :=
    (dvd_mul_left (q : ℤ) (l : ℤ)).trans ((quotient_divisibility_iff d n l q).mp hdiv)
  apply Nat.coprime_mul_iff_left.mpr
  constructor
  · by_contra hh
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    have hpdiff : (p : ℤ)∣((n : ℤ)+(l : ℤ))^d-(n : ℤ)^d :=
      (show (p : ℤ)∣(q : ℤ) by exact_mod_cast hpq).trans hqdiff
    have hpnPow : (p : ℤ)∣(n : ℤ)^d := dvd_pow (by exact_mod_cast hpn) hd.ne'
    have hpother : (p : ℤ)∣((n : ℤ)+(l : ℤ))^d := by
      convert dvd_add hpdiff hpnPow using 1
      ring
    have hpNat : p∣(n+l)^d := by exact_mod_cast hpother
    exact (hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpn)) (hp.dvd_of_dvd_pow hpNat)
  · by_contra hh
    obtain ⟨p,hp,hpn,hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hh
    have hpdiff : (p : ℤ)∣((n : ℤ)+(l : ℤ))^d-(n : ℤ)^d :=
      (show (p : ℤ)∣(q : ℤ) by exact_mod_cast hpq).trans hqdiff
    have hpnPow : (p : ℤ)∣((n : ℤ)+(l : ℤ))^d :=
      dvd_pow (by exact_mod_cast hpn) hd.ne'
    have hpother : (p : ℤ)∣(n : ℤ)^d := by
      convert dvd_sub hpnPow hpdiff using 1
      ring
    have hpNat : p∣n^d := by exact_mod_cast hpother
    exact (hp.coprime_iff_not_dvd.mp (hcop.symm.of_dvd_left hpn)) (hp.dvd_of_dvd_pow hpNat)

/-- All actual divisibility fibers in any coprime subdomain of [1,N]. -/
theorem natQuotient_fiber_card_le_rpow {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀q l N : ℕ,0<q→0<l→∀A : Finset ℕ,
      A⊆Finset.Icc 1 N→(∀n∈A,Nat.Coprime n (n+l))→
      ((A.filter fun n=>q∣natQuotient d n l).card : ℝ)≤
        C*((N : ℝ)/q+1)*((l*q : ℕ) : ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := quotientPoints_card_le_rpow hd hε
  refine ⟨C,hC,?_⟩
  intro q l N hq hl A hA hcop
  have hsub : A.filter (fun n=>q∣natQuotient d n l)⊆quotientPoints d q l N := by
    intro n hn
    obtain ⟨hn,hdiv⟩ := Finset.mem_filter.mp hn
    have hdivZ : (q : ℤ)∣differenceQuotient d n l := by
      rw [differenceQuotient_eq_natQuotient _ _ _ hl]
      exact_mod_cast hdiv
    apply Finset.mem_filter.mpr
    exact ⟨hA hn,hcop n hn,quotient_divisor_coprime hd (hcop n hn) hdivZ,hdivZ⟩
  exact (show ((A.filter fun n=>q∣natQuotient d n l).card : ℝ)≤
    ((quotientPoints d q l N).card : ℝ) by exact_mod_cast Finset.card_le_card hsub).trans
      (hbound q l N hq hl)

#print axioms natQuotient_bounds
#print axioms quotient_divisor_coprime
#print axioms natQuotient_fiber_card_le_rpow
end Waring.PolicyCompletionBinomialArithmetic

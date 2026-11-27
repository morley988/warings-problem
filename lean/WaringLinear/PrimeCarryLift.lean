import WaringLinear.TeichCarry
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic

/-! A Hensel lift for the divided binomial permits one zero coordinate to
correct a unit power while fixing the sum of the two roots. Together with
a valuation-one integer carry this gives five prime powers in every
Henselian local ring with finite residue field of odd characteristic p. -/
noncomputable section
open Polynomial IsLocalRing BigOperators Finset
namespace WaringLinear.PrimeCarryLift

variable {R : Type*} [CommRing R]

/-- Monic divided difference for an odd prime p=n+3; t is the target. -/
private def branch (n : ℕ) (t : R) : R[X] :=
  X^(n+2) + ∑ i : Fin (n+2), C (if (i:ℕ)=0 then -t else
    (((n+3).choose (i:ℕ) / (n+3) : ℕ) : R)) * X^(i:ℕ)

private theorem branch_monic (n : ℕ) (t : R) :
    (branch n t).Monic := monic_X_pow_add (degree_sum_fin_lt _)

private theorem branch_zero (n : ℕ) (t : R) : (branch n t).eval 0= -t := by
  simp [branch,Fin.sum_univ_succ,eval_finset_sum]

private theorem branch_derivative (n : ℕ) (t : R) :
    (branch n t).derivative.eval 0=1 := by
  simp [branch,Fin.sum_univ_succ,eval_finset_sum, show 0<n+3 by omega]

private theorem branch_formula (n : ℕ) (hp : (n+3).Prime) (t x : R) :
    (1+x)^(n+3)-x^(n+3)-1=(n+3:R)*((branch n t).eval x+t) := by
  have hcoef (i : Fin (n+2)) :
      (n+3:R) * (if (i:ℕ)=0 then -t else
        (((n+3).choose (i:ℕ) / (n+3):ℕ):R)) =
        if (i:ℕ)=0 then (n+3:R)*(-t) else (((n+3).choose (i:ℕ)):R) := by
    split_ifs with hi
    · rfl
    · have hd := hp.dvd_choose_self hi (show (i:ℕ)<n+3 by omega)
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using
        congrArg (fun v : ℕ => (v:R)) (Nat.mul_div_cancel' hd)
  rw [add_comm (1:R) x,add_pow]
  simp only [one_pow,mul_one]
  simp only [branch,eval_add,eval_X,eval_pow,eval_finset_sum,eval_mul,eval_C]
  rw [mul_add,mul_add,Finset.mul_sum]
  simp_rw [←mul_assoc,hcoef]
  rw [Finset.sum_range_succ,Finset.sum_range_succ]
  -- The last two binomial coefficients are p and 1.
  simp only [Nat.choose_self,Nat.cast_one,mul_one,Nat.choose_succ_self_right]
  rw [←Fin.sum_univ_eq_sum_range]
  simp [Fin.sum_univ_succ,add_mul,mul_comm,mul_left_comm]
  ring

/-- For every target in the maximal ideal there is a nearby split
of the unit p-th power into two powers differing by p times that target. -/
theorem unit_pair_correction [HenselianLocalRing R] {n : ℕ} (hp : (n+3).Prime)
    (t : R) (ht : t ∈ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧
      (1+x)^(n+3)-x^(n+3)=1+(n+3:R)*t := by
  obtain ⟨x,hx,hm⟩ := HenselianLocalRing.is_henselian (branch n t) (branch_monic n t) 0
    (by simpa only [branch_zero,Ideal.neg_mem_iff] using ht)
    (by rw [branch_derivative]; exact isUnit_one)
  refine ⟨x,by simpa using hm,?_⟩
  have H := branch_formula n hp t x
  rw [show (branch n t).eval x=0 from hx,zero_add] at H
  linear_combination H

theorem one_power_mod_prime {p : ℕ} (hp : p.Prime) (ho : Odd p) {n : R}
    (hn : n ∈ AddSubgroup.closure (Set.range fun x : R => x^p)) :
    ∃ w t : R, n=w^p+(p:R)*t := by
  induction hn using AddSubgroup.closure_induction with
  | mem z hz => obtain ⟨w,rfl⟩ := hz; exact ⟨w,0,by simp⟩
  | zero => exact ⟨0,0,by simp [hp.ne_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨x,t,rfl⟩ := ha
    obtain ⟨y,v,rfl⟩ := hb
    obtain ⟨e,he⟩ := (Commute.all x y).exists_add_pow_prime_eq hp
    exact ⟨x+y,t+v-e,by linear_combination -he⟩
  | neg a _ ha =>
    obtain ⟨x,t,rfl⟩ := ha
    exact ⟨-x,-t,by rw [ho.neg_pow]; ring⟩

private theorem move_unit [HenselianLocalRing R] {p : ℕ} (hp : p.Prime) (hne : p≠2)
    (u t : R) (hu : IsUnit u) (ht : t ∈ maximalIdeal R) :
    ∃ a b : R, IsUnit a ∧ a^p+b^p=u^p+(p:R)*t := by
  have hlow : 3≤p := by have := hp.two_le; omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlow
  rw [Nat.add_comm 3 j] at *
  obtain ⟨v,rfl⟩ := hu
  let T : R := (↑(v⁻¹) : R)^(j+3)*t
  obtain ⟨z,hz,he⟩ := unit_pair_correction hp T ((maximalIdeal R).mul_mem_left _ ht)
  have hunit : IsUnit (1+z) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have h₀ : residue R z=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hz
    simp [h₀]
  refine ⟨(v:R)*(1+z), (v:R)*(-z), v.isUnit.mul hunit, ?_⟩
  rw [mul_pow,mul_pow,(hp.odd_of_ne_two hne).neg_pow]
  have hh : (v:R)^(j+3)*T=t := by dsimp [T]; rw [←mul_assoc,←mul_pow]; simp
  push_cast at he ⊢
  linear_combination (v:R)^(j+3)*he + (j+3:R)*hh

private theorem finish [HenselianLocalRing R] {p : ℕ} (hp : p.Prime) (hne : p≠2)
    (u a b c t n : R) (hu : IsUnit u) (ht : t∈maximalIdeal R)
    (hn : n=u^p+a^p+b^p+c^p+(p:R)*t) :
    ∃ x : Fin 5 → R, (∑ i, (x i)^p)=n ∧ ∃ i, IsUnit (x i) := by
  obtain ⟨y,z,hy,he⟩ := move_unit hp hne u t hu ht
  refine ⟨![y,z,a,b,c],?_,⟨0,hy⟩⟩
  simp [Fin.sum_univ_succ]
  linear_combination he-hn

/-- At every odd residue prime, five actual p-th powers with a unit root
represent the entire p-th-power span. The ring may have arbitrary ramification. -/
theorem five_prime_powers [HenselianLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField R) p] [Finite (ResidueField R)] (hne : p≠2) {n : R}
    (hn : n ∈ AddSubgroup.closure (Set.range fun x : R => x^p)) :
    ∃ x : Fin 5 → R, (∑ i, (x i)^p)=n ∧ ∃ i, IsUnit (x i) := by
  have hp : p.Prime := Fact.out
  have ho : Odd p := hp.odd_of_ne_two hne
  obtain ⟨w,t,hwt⟩ := one_power_mod_prime hp ho hn
  obtain ⟨j,_,hd,hnd⟩ := WaringLinear.primePower_consecutive_carry p 1 (by decide)
  simp only [pow_one] at hd hnd
  obtain ⟨D,hD⟩ := hd
  have hDn : ¬(p:ℤ) ∣ D := by
    rintro ⟨v,hv⟩
    apply hnd
    exact ⟨v,by rw [hD,hv];ring⟩
  have hDF : (D:ResidueField R)≠0 := (CharP.intCast_eq_zero_iff _ p D).not.mpr hDn
  obtain ⟨B,hB⟩ := (frobeniusEquiv (ResidueField R) p).surjective (residue R t/(D:ResidueField R))
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective (I:=maximalIdeal R) B
  change (residue R b)^p=residue R t/(D:ResidueField R) at hB
  let v := t-(D:R)*b^p
  have hv : v∈maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residue R (t-(D:R)*b^p)=0
    rw [map_sub,map_mul,map_intCast,map_pow,hB]
    field_simp
    ring
  have hD' : (j:R)^p+1-((j:R)+1)^p=(p:R)*(D:R) := by
    simpa using congrArg (fun a : ℤ => (a:R)) hD
  have hc : ((j:R)*b)^p+b^p+(-((j:R)+1)*b)^p=(p:R)*(D:R)*b^p := by
    rw [mul_pow,mul_pow,ho.neg_pow]
    linear_combination b^p*hD'
  by_cases hw : IsUnit w
  · apply finish hp hne w ((j:R)*b) b (-((j:R)+1)*b) v n hw hv
    dsimp [v]
    linear_combination hwt-hc
  by_cases hb : IsUnit b
  · apply finish hp hne b w ((j:R)*b) (-((j:R)+1)*b) v n hb hv
    dsimp [v]
    linear_combination hwt-hc
  have hb₀ : residue R b=0 := not_ne_iff.mp ((residue_ne_zero_iff_isUnit _).not.mpr hb)
  have ht₀ : t ∈ maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change residue R t=0
    have hh : residue R (t-(D:R)*b^p)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hv
    simpa [hb₀,hp.ne_zero] using hh
  apply finish hp hne 1 w (-1) 0 t n isUnit_one ht₀
  rw [ho.neg_pow,one_pow,zero_pow hp.ne_zero,hwt]
  ring

#print axioms unit_pair_correction
#print axioms one_power_mod_prime
#print axioms five_prime_powers
end WaringLinear.PrimeCarryLift

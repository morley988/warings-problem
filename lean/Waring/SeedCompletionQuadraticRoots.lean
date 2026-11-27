import Waring.PolicyCompletionRoots
import Mathlib.RingTheory.Int.Basic

/-!
# All roots of x^2 + 3 modulo an arbitrary positive integer

The only singular primes are two and three. Modulo eight and nine there
are no roots, so every prime-power root set has at most four elements.
Prime-power reductions then give a divisor-square bound for all roots.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionQuadraticRoots
open SeedCompletion PolicyCompletionRoots

def quadraticRoots (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun r => q ∣ r^2+3)

@[simp] theorem mem_quadraticRoots {q r : ℕ} :
    r ∈ quadraticRoots q ↔ r < q ∧ q ∣ r^2+3 := by
  simp [quadraticRoots]

theorem quadraticRoots_card_le (q : ℕ) : (quadraticRoots q).card ≤ q := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range q)

theorem eight_not_dvd (r : ℕ) : ¬8 ∣ r^2+3 := by
  intro h
  have hmod : (r^2+3)%8=0 := Nat.mod_eq_zero_of_dvd h
  have hf : ∀ t : Fin 8, (t.val^2+3)%8 ≠ 0 := by decide
  apply hf ⟨r%8,Nat.mod_lt _ (by norm_num)⟩
  simpa only [Nat.add_mod,Nat.pow_mod,Nat.mod_mod] using hmod

theorem nine_not_dvd (r : ℕ) : ¬9 ∣ r^2+3 := by
  intro h
  have hmod : (r^2+3)%9=0 := Nat.mod_eq_zero_of_dvd h
  have hf : ∀ t : Fin 9, (t.val^2+3)%9 ≠ 0 := by decide
  apply hf ⟨r%9,Nat.mod_lt _ (by norm_num)⟩
  simpa only [Nat.add_mod,Nat.pow_mod,Nat.mod_mod] using hmod

def quadraticPolynomial : Polynomial ℤ := Polynomial.X^2+Polynomial.C 3

@[simp] theorem quadraticPolynomial_eval (r : ℤ) : quadraticPolynomial.eval r = r^2+3 := by
  simp [quadraticPolynomial]

@[simp] theorem quadraticPolynomial_derivative_eval (r : ℤ) :
    quadraticPolynomial.derivative.eval r = 2*r := by
  simp [quadraticPolynomial,Polynomial.derivative_X_pow]

theorem root_prime_coprime {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hr : p ∣ r^2+3) : Nat.Coprime p (2*r) := by
  have h2 : ¬p ∣ 2 := by
    intro h
    have hp' := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h
    rcases hp' with h | h
    · exact hp.ne_one h
    · exact hp2 h
  have h3 : ¬p ∣ 3 := by
    intro h
    have hp' := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h
    rcases hp' with h | h
    · exact hp.ne_one h
    · exact hp3 h
  have hr' : ¬p ∣ r := by
    intro h
    have hs : p ∣ r^2 := dvd_pow h (by norm_num)
    exact h3 ((Nat.dvd_add_right hs).mp hr)
  exact (hp.coprime_iff_not_dvd.mpr h2).mul_right (hp.coprime_iff_not_dvd.mpr hr')

/-- Every prime-power fiber, including the two singular primes. -/
theorem prime_power_card_le_four {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (quadraticRoots (p^e)).card ≤ 4 := by
  by_cases he : e=0
  · rw [he,pow_zero]
    exact (quadraticRoots_card_le 1).trans (by norm_num)
  by_cases hp2 : p=2
  · subst p
    by_cases he2 : e ≤ 2
    · exact (quadraticRoots_card_le (2^e)).trans (by
        exact (Nat.pow_le_pow_right (by norm_num) he2).trans_eq (by norm_num))
    · have hnone : quadraticRoots (2^e)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have h8 : 8 ∣ 2^e := by
          change 2^3 ∣ 2^e
          exact pow_dvd_pow 2 (by omega)
        exact eight_not_dvd r (h8.trans (mem_quadraticRoots.mp hr).2)
      simp [hnone]
  by_cases hp3 : p=3
  · subst p
    by_cases he1 : e ≤ 1
    · exact (quadraticRoots_card_le (3^e)).trans (by
        exact (Nat.pow_le_pow_right (by norm_num) he1).trans (by norm_num))
    · have hnone : quadraticRoots (3^e)=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have h9 : 9 ∣ 3^e := by
          change 3^2 ∣ 3^e
          exact pow_dvd_pow 3 (by omega)
        exact nine_not_dvd r (h9.trans (mem_quadraticRoots.mp hr).2)
      simp [hnone]
  have hsub : quadraticRoots (p^e) ⊆ nonsingularResidueRoots quadraticPolynomial 0 p e := by
    intro r hr
    obtain ⟨hrlt,hrdiv⟩ := mem_quadraticRoots.mp hr
    have hpdiv : p ∣ r^2+3 := (dvd_pow_self p he).trans hrdiv
    have hcop := root_prime_coprime hp hp2 hp3 hpdiv
    apply mem_nonsingularResidueRoots.mpr
    refine ⟨hrlt,?_,?_⟩
    · simp only [quadraticPolynomial_eval,sub_zero]
      exact_mod_cast hrdiv
    · rw [quadraticPolynomial_derivative_eval,Int.isCoprime_iff_nat_coprime]
      simpa only [Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_ofNat] using hcop
  calc
    _ ≤ (nonsingularResidueRoots quadraticPolynomial 0 p e).card := Finset.card_le_card hsub
    _ ≤ quadraticPolynomial.natDegree :=
      nonsingularResidueRoots_card_le_natDegree quadraticPolynomial 0 hp (by omega)
    _ ≤ 4 := by
      unfold quadraticPolynomial
      rw [Polynomial.natDegree_X_pow_add_C]
      norm_num

/-- Reduction of a root modulo a positive divisor. -/
theorem root_reduction_mem {q d r : ℕ} (hd : 0 < d) (hdq : d ∣ q)
    (hr : r ∈ quadraticRoots q) : r%d ∈ quadraticRoots d := by
  obtain ⟨hrlt,hrdiv⟩ := mem_quadraticRoots.mp hr
  apply mem_quadraticRoots.mpr
  refine ⟨Nat.mod_lt _ hd,?_⟩
  apply Nat.dvd_of_mod_eq_zero
  have hmod := Nat.mod_eq_zero_of_dvd (hdq.trans hrdiv)
  simpa only [Nat.add_mod,Nat.pow_mod,Nat.mod_mod] using hmod

/-- Complete prime-power residues distinguish all residues modulo q. -/
theorem prime_power_reduction_injective {q : ℕ} (hq : 0 < q) :
    Set.InjOn (fun x : ℕ => fun p : q.primeFactors => x%(p.val^q.factorization p.val))
      (quadraticRoots q) := by
  intro x hx y hy hxy
  obtain ⟨hxlt,_⟩ := mem_quadraticRoots.mp hx
  obtain ⟨hylt,_⟩ := mem_quadraticRoots.mp hy
  have hqdiv : (q : ℤ) ∣ (y : ℤ)-x := by
    apply Int.natCast_dvd.mpr
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p e hp hpeq
    by_cases he : e=0
    · simp [he]
    have hpdq : p ∣ q := (dvd_pow_self p he).trans hpeq
    have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpdq,hq.ne'⟩
    have hefac : e ≤ q.factorization p := (hp.pow_dvd_iff_le_factorization hq.ne').mp hpeq
    have hmod := congrFun hxy ⟨p,hmem⟩
    have hzmod : (x : ZMod (p^q.factorization p))=(y : ZMod (p^q.factorization p)) :=
      (ZMod.natCast_eq_natCast_iff' x y _).mpr hmod
    have hfull : ((p^q.factorization p : ℕ) : ℤ) ∣ (y : ℤ)-x :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) _).mp
        (by simpa only [Int.cast_natCast] using hzmod)
    apply Int.natCast_dvd.mp
    exact (show ((p^e : ℕ) : ℤ) ∣ ((p^q.factorization p : ℕ) : ℤ) by
      exact_mod_cast pow_dvd_pow p hefac).trans hfull
  have hzmod : (x : ZMod q)=(y : ZMod q) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) q).mpr hqdiv
  have hmod := (ZMod.natCast_eq_natCast_iff' x y q).mp hzmod
  simpa only [Nat.mod_eq_of_lt hxlt,Nat.mod_eq_of_lt hylt] using hmod

/-- The complete root set is bounded by a squared divisor count. -/
theorem quadraticRoots_card_le_divisors_sq {q : ℕ} (hq : 0 < q) :
    (quadraticRoots q).card ≤ q.divisors.card^2 := by
  classical
  let roots := Fintype.piFinset
    (fun p : q.primeFactors => quadraticRoots (p.val^q.factorization p.val))
  have hcard : (quadraticRoots q).card ≤ roots.card := by
    apply Finset.card_le_card_of_injOn
      (fun x : ℕ => fun p : q.primeFactors => x%(p.val^q.factorization p.val))
    · intro x hx
      apply Fintype.mem_piFinset.mpr
      intro p
      have hp := Nat.prime_of_mem_primeFactors p.property
      exact root_reduction_mem (pow_pos hp.pos _)
        ((hp.pow_dvd_iff_le_factorization hq.ne').mpr le_rfl) hx
    · exact prime_power_reduction_injective hq
  apply hcard.trans
  rw [Fintype.card_piFinset]
  calc
    _ ≤ ∏ _p : q.primeFactors, 4 := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact prime_power_card_le_four (Nat.prime_of_mem_primeFactors p.property) _
    _ = 4^q.primeFactors.card := by simp
    _ = (2^q.primeFactors.card)^2 := by
      change (2^2)^q.primeFactors.card = (2^q.primeFactors.card)^2
      rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ q.divisors.card^2 := Nat.pow_le_pow_left (two_pow_primeFactors_card_le_divisors hq) _

#print axioms prime_power_card_le_four
#print axioms quadraticRoots_card_le_divisors_sq
end Waring.SeedCompletionQuadraticRoots

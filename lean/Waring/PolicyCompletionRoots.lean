import Waring.SeedCompletionRoots
import Waring.AuxiliaryL2Grouping

/-!
# Uniform nonsingular roots for composite moduli

Reduce a nonsingular root modulo q to its residues modulo the distinct prime
divisors of q. The prime-power uniqueness theorem makes this reduction
injective: agreement modulo each prime lifts to every prime power dividing q.
Each prime coordinate has at most the polynomial degree many possibilities.
The resulting degree^omega(q) bound is at most a fixed power of the divisor
count, and therefore is O(q^epsilon), uniformly in the polynomial coefficients
and target residue, when the degree is bounded.

This proves the actual root estimate used in equation (2.22), printed page
239 of Wooley's 1990 thesis, Part III. No Chinese-remainder existence theorem
is needed because only the injective direction is used.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionRoots
open SeedCompletion AuxiliaryL2Grouping

/-- Divisibility of the arguments transfers to divisibility of the values. -/
theorem eval_sub_dvd {q x y : ℤ} (f : Polynomial ℤ) (h : q ∣ x-y) :
    q ∣ f.eval x-f.eval y :=
  h.trans (Polynomial.sub_dvd_eval_sub x y f)

/-- Coprimality of the derivative is invariant under reduction of the input. -/
theorem derivative_coprime_of_congruent {q x y : ℤ} (f : Polynomial ℤ)
    (h : q ∣ y-x) (hcop : IsCoprime q (f.derivative.eval x)) :
    IsCoprime q (f.derivative.eval y) := by
  obtain ⟨t,ht⟩ := eval_sub_dvd f.derivative h
  have heq : f.derivative.eval y = f.derivative.eval x+q*t := by omega
  rw [heq]
  exact hcop.add_mul_left_right t

/-- A nonsingular root modulo q reduces to a nonsingular root modulo each
positive divisor of q. -/
theorem root_reduction_mem (f : Polynomial ℤ) (a : ℤ) {q d x : ℕ}
    (hd : 0 < d) (hdq : d ∣ q)
    (hx : x ∈ nonsingularResidueRoots f a q 1) :
    x % d ∈ nonsingularResidueRoots f a d 1 := by
  obtain ⟨hxlt,hfx,hcop⟩ := mem_nonsingularResidueRoots.mp hx
  simp only [pow_one] at hxlt hfx
  have hdq' : (d : ℤ) ∣ (q : ℤ) := by exact_mod_cast hdq
  have hmod : (d : ℤ) ∣ (x : ℤ)-((x % d : ℕ) : ℤ) := by
    refine ⟨(x / d : ℕ),?_⟩
    have heq : ((x % d : ℕ) : ℤ)+(d : ℤ)*((x/d : ℕ) : ℤ)=(x : ℤ) := by
      exact_mod_cast Nat.mod_add_div x d
    omega
  apply mem_nonsingularResidueRoots.mpr
  refine ⟨by simpa using Nat.mod_lt x hd,?_,?_⟩
  · have hfirst := hdq'.trans hfx
    have hsecond := eval_sub_dvd f hmod
    simpa only [pow_one] using
      (show (d : ℤ) ∣ f.eval ((x%d : ℕ) : ℤ)-a from by
        convert dvd_sub hfirst hsecond using 1; ring)
  · have hneg : (d : ℤ) ∣ ((x % d : ℕ) : ℤ)-(x : ℤ) := by
      simpa only [neg_sub] using dvd_neg.mpr hmod
    exact derivative_coprime_of_congruent f hneg (hcop.of_isCoprime_of_dvd_left hdq')

/-- The simultaneous prime reductions distinguish all nonsingular roots
modulo q. Agreement at each prime lifts to every prime power dividing q. -/
theorem root_prime_reduction_injective (f : Polynomial ℤ) (a : ℤ)
    {q : ℕ} (hq : 0 < q) :
    Set.InjOn (fun x : ℕ => fun p : q.primeFactors => x % p.val)
      (nonsingularResidueRoots f a q 1) := by
  intro x hx y hy hxy
  obtain ⟨hxlt,hfx,hcop⟩ := mem_nonsingularResidueRoots.mp hx
  obtain ⟨hylt,hfy,_⟩ := mem_nonsingularResidueRoots.mp hy
  simp only [pow_one] at hxlt hylt hfx hfy
  have hdiff : (q : ℤ) ∣ f.eval (y : ℤ)-f.eval (x : ℤ) := by
    convert dvd_sub hfy hfx using 1; ring
  have hqdiff : (q : ℤ) ∣ (y : ℤ)-x := by
    apply Int.natCast_dvd.mpr
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p e hp hpeq
    by_cases he : e=0
    · simp [he]
    · have hpdq : p ∣ q := (dvd_pow_self p he).trans hpeq
      have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp,hpdq,hq.ne'⟩
      have hmod : x % p=y % p := congrFun hxy ⟨p,hmem⟩
      have hzmod : (x : ZMod p)=(y : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' x y p).mpr hmod
      have hpdiv : (p : ℤ) ∣ (y : ℤ)-x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) p).mp
          (by simpa only [Int.cast_natCast] using hzmod)
      have hpq' : (p : ℤ) ∣ (q : ℤ) := by exact_mod_cast hpdq
      have hpeq' : (p : ℤ)^e ∣ (q : ℤ) := by exact_mod_cast hpeq
      have hlift := nonsingular_congruence_power_unique f (p : ℤ) (x : ℤ) (y : ℤ) e
        (hcop.of_isCoprime_of_dvd_left hpq') hpdiv (hpeq'.trans hdiff)
      exact Int.natCast_dvd.mp (by simpa only [Nat.cast_pow] using hlift)
  have hzmod : (x : ZMod q)=(y : ZMod q) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (x : ℤ) (y : ℤ) q).mpr hqdiff
  have hmod := (ZMod.natCast_eq_natCast_iff' x y q).mp hzmod
  simpa only [Nat.mod_eq_of_lt hxlt,Nat.mod_eq_of_lt hylt] using hmod

/-- The exact degree^omega bound for arbitrary positive composite moduli. -/
theorem nonsingularRoots_card_le_degree_pow (f : Polynomial ℤ) (a : ℤ)
    {q : ℕ} (hq : 0 < q) :
    (nonsingularResidueRoots f a q 1).card ≤ f.natDegree^q.primeFactors.card := by
  classical
  let roots := Fintype.piFinset
    (fun p : q.primeFactors => nonsingularResidueRoots f a p.val 1)
  have hinj := root_prime_reduction_injective f a hq
  have hcard : (nonsingularResidueRoots f a q 1).card ≤ roots.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => fun p : q.primeFactors => x % p.val)
    · intro x hx
      apply Fintype.mem_piFinset.mpr
      intro p
      exact root_reduction_mem f a (Nat.pos_of_mem_primeFactors p.property)
        (Nat.dvd_of_mem_primeFactors p.property) hx
    · exact hinj
  apply hcard.trans
  rw [Fintype.card_piFinset]
  calc
    (∏ p : q.primeFactors, (nonsingularResidueRoots f a p.val 1).card) ≤
        ∏ _p : q.primeFactors, f.natDegree := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact nonsingularResidueRoots_card_le_natDegree f a
        (e := 1) (Nat.prime_of_mem_primeFactors p.property) (by omega)
    _ = f.natDegree^q.primeFactors.card := by simp

theorem two_pow_primeFactors_card_le_divisors {q : ℕ} (hq : 0 < q) :
    2^q.primeFactors.card ≤ q.divisors.card := by
  rw [Nat.card_divisors hq.ne']
  calc
    _ = ∏ _p ∈ q.primeFactors, 2 := (Finset.prod_const _).symm
    _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p+1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      have hpq := Nat.mem_primeFactors.mp hp
      have hv := hpq.1.factorization_pos_of_dvd hq.ne' hpq.2.1
      omega

/-- A fixed divisor-count power controls every polynomial of bounded degree. -/
theorem nonsingularRoots_card_le_divisor_power (d : ℕ) (f : Polynomial ℤ)
    (hdeg : f.natDegree ≤ d) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    (nonsingularResidueRoots f a q 1).card ≤ q.divisors.card^d := by
  calc
    _ ≤ f.natDegree^q.primeFactors.card := nonsingularRoots_card_le_degree_pow f a hq
    _ ≤ d^q.primeFactors.card := Nat.pow_le_pow_left hdeg _
    _ ≤ (2^d)^q.primeFactors.card :=
      Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) _
    _ = (2^q.primeFactors.card)^d := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
    _ ≤ q.divisors.card^d := Nat.pow_le_pow_left (two_pow_primeFactors_card_le_divisors hq) _

/-- The uniform source root estimate. The finite constant depends only on
the degree bound and epsilon, not on coefficients, target, or modulus. -/
theorem nonsingularRoots_card_le_rpow (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Polynomial ℤ), f.natDegree ≤ d →
      ∀ (a : ℤ) (q : ℕ), 0 < q →
        ((nonsingularResidueRoots f a q 1).card : ℝ) ≤ C*(q : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := divisor_power_le_rpow d hε
  refine ⟨C,hC,?_⟩
  intro f hdeg a q hq
  have hcount : ((nonsingularResidueRoots f a q 1).card : ℝ) ≤ (q.divisors.card : ℝ)^d := by
    exact_mod_cast nonsingularRoots_card_le_divisor_power d f hdeg a hq
  exact hcount.trans (hdiv q hq)

/-- Natural representatives of arbitrary integer arguments belong to the
actual root set. This handles centered intervals with negative endpoints. -/
theorem integer_residue_mem_roots (f : Polynomial ℤ) (a z : ℤ)
    {q : ℕ} (hq : 0 < q)
    (hval : (q : ℤ) ∣ f.eval z-a)
    (hcop : IsCoprime (q : ℤ) (f.derivative.eval z)) :
    (z % (q : ℤ)).toNat ∈ nonsingularResidueRoots f a q 1 := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hmod0 := Int.emod_nonneg z hqZ.ne'
  have hmodlt := Int.emod_lt_of_pos z hqZ
  have hr : ((z % (q : ℤ)).toNat : ℤ)=z % (q : ℤ) := Int.toNat_of_nonneg hmod0
  have hdif : (q : ℤ) ∣ z-((z % (q : ℤ)).toNat : ℤ) := by
    rw [hr]
    exact Int.dvd_self_sub_emod
  apply mem_nonsingularResidueRoots.mpr
  refine ⟨?_,?_,?_⟩
  · rw [pow_one]
    exact_mod_cast (show ((z % (q : ℤ)).toNat : ℤ) < q from hr ▸ hmodlt)
  · simp only [pow_one]
    convert dvd_sub hval (eval_sub_dvd f hdif) using 1; ring
  · apply derivative_coprime_of_congruent f _ hcop
    simpa only [neg_sub] using dvd_neg.mpr hdif

/-- At the efficient-differencing modulus w^k the source loss is w^epsilon.
The constant remains uniform over all bounded-degree polynomials. -/
theorem nonsingular_power_roots_card_le_rpow (d k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Polynomial ℤ), f.natDegree ≤ d →
      ∀ (a : ℤ) (w : ℕ), 0 < w →
        ((nonsingularResidueRoots f a (w^k) 1).card : ℝ) ≤ C*(w : ℝ)^ε := by
  let δ := ε/((k : ℝ)+1)
  have hk1 : (0 : ℝ) < (k : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hk1
  have hkδ : (k : ℝ)*δ ≤ ε := by
    have heq : δ*((k : ℝ)+1)=ε := div_mul_cancel₀ ε hk1.ne'
    nlinarith
  obtain ⟨C,hC,hroots⟩ := nonsingularRoots_card_le_rpow d hδ
  refine ⟨C,hC,?_⟩
  intro f hdeg a w hw
  calc
    _ ≤ C*((w^k : ℕ) : ℝ)^δ := hroots f hdeg a (w^k) (pow_pos hw k)
    _ = C*(w : ℝ)^((k : ℝ)*δ) := by
      rw [Nat.cast_pow,← Real.rpow_natCast_mul (by positivity)]
    _ ≤ C*(w : ℝ)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hw) hkδ) hC.le

#print axioms root_prime_reduction_injective
#print axioms nonsingularRoots_card_le_degree_pow
#print axioms nonsingularRoots_card_le_rpow
#print axioms integer_residue_mem_roots
#print axioms nonsingular_power_roots_card_le_rpow

end Waring.PolicyCompletionRoots

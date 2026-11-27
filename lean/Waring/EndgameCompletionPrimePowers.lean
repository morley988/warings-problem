import Waring.EndgameCompletionStationary

/-!
# Prime-power recursions for complete monomial sums

The finite stationary-phase filter is reindexed over multiples of the prime.
Periodicity then removes exactly `k-1` blocks at every recursive step.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion
open QuadraticModulation

/-- Residues divisible by `p`, in their canonical range `0,...,q-1`, are
parametrized exactly by `p*y` with `0 ≤ y < M` when `q=p*M`. -/
theorem sum_zmod_filter_dvd (q p M : ℕ) [NeZero q] (hp : 0 < p)
    (hq : q=p*M) (F : ZMod q → ℂ) :
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter (fun x => p ∣ x.val), F x) =
      ∑ y ∈ Finset.range M, F ((p*y : ℕ) : ZMod q) := by
  have hbound {y : ℕ} (hy : y ∈ Finset.range M) : p*y < q := by
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hy) hp
  symm
  apply Finset.sum_bij (fun y _ => ((p*y : ℕ) : ZMod q))
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast_of_lt (hbound hy)]
    exact dvd_mul_right p y
  · intro y hy z hz heq
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (hbound hy), ZMod.val_natCast_of_lt (hbound hz)] at hval
    exact Nat.eq_of_mul_eq_mul_left hp hval
  · intro x hx
    obtain ⟨y,hy⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨y, Finset.mem_range.mpr ?_, ?_⟩
    · have hlt := ZMod.val_lt x
      rw [hy, hq] at hlt
      exact (Nat.mul_lt_mul_left hp).mp hlt
    · rw [← hy, ZMod.natCast_zmod_val]
  · intro y _
    rfl

theorem sum_zmod_eq_sum_range (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    (∑ x : ZMod q, F x) = ∑ y ∈ Finset.range q, F (y : ZMod q) := by
  simpa only [one_dvd, Finset.filter_true, one_mul] using
    sum_zmod_filter_dvd q 1 q zero_lt_one (by simp) F

theorem completeMonomialSumMod_eq_range (q : ℕ) [NeZero q] (k : ℕ) (a : ℤ) :
    completeMonomialSumMod q k (a : ZMod q) =
      ∑ y ∈ Finset.range q, e ((a : ℝ)/q*(y : ℝ)^k) := by
  unfold completeMonomialSumMod
  rw [sum_zmod_eq_sum_range]
  simp_rw [stdAddChar_monomial_nat]

/-- Divisibility of the canonical residue is unchanged when reducing by
a modulus divisible by the divisor. -/
theorem dvd_zmod_val_iff_dvd {q d n : ℕ} [NeZero q] (hd : d ∣ q) :
    d ∣ ((n : ZMod q).val) ↔ d ∣ n := by
  rw [ZMod.val_natCast, Nat.dvd_mod_iff hd]

/-- Small prime-power levels have an exact value at good primes. -/
theorem completeMonomialSumMod_primepower_small {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) (a : ZMod (p^l))
    (ha : ¬ p ∣ a.val) (hpk : ¬ p ∣ k) :
    completeMonomialSumMod (p^l) k a = (p^(l-1) : ℕ) := by
  rw [completeMonomialSumMod_primepower_good_filter l k hl (by omega) a ha hpk,
    sum_zmod_filter_dvd (p^l) p (p^(l-1)) (Fact.out : p.Prime).pos
      (by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l)])]
  have hphase (y : ℕ) :
      ZMod.stdAddChar (a*((p*y : ℕ) : ZMod (p^l))^k) = 1 := by
    have hnil : (((p*y : ℕ) : ZMod (p^l))^k) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow p hlk).trans (pow_dvd_pow_of_dvd (dvd_mul_right p y) k)
    rw [hnil, mul_zero, AddChar.map_zero_eq_one]
  simp only [hphase, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The phase identity that divides a prime from every summation variable. -/
theorem primepower_reduced_phase {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hkl : k ≤ l) (a : ZMod (p^l)) (y : ℕ) :
    ZMod.stdAddChar (a*((p*y : ℕ) : ZMod (p^l))^k) =
      e ((a.val : ℝ)/(p^(l-k) : ℕ)*(y : ℝ)^k) := by
  have hcoeff : ((a.val : ℕ) : ZMod (p^l)) = a := ZMod.natCast_zmod_val a
  calc
    _ = ZMod.stdAddChar ((((a.val : ℕ) : ℤ) : ZMod (p^l))*((p*y : ℕ) : ZMod (p^l))^k) := by
      push_cast
      rw [hcoeff]
    _ = e ((a.val : ℝ)/(p^l : ℕ)*(p*y : ℕ)^k) := by
      simpa only [Int.cast_natCast] using stdAddChar_monomial_nat (p^l) k (a.val : ℤ) (p*y)
    _ = _ := by
      congr 1
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      push_cast
      rw [show (p : ℝ)^l = p^k*p^(l-k) by rw [← pow_add, Nat.add_sub_of_le hkl]]
      field_simp
      rw [mul_pow]
      ring

/-- Exact recursive reduction at every good prime. The coefficient is
reduced canonically to the smaller residue ring. -/
theorem completeMonomialSumMod_primepower_recurrence_good {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hk : 2 ≤ k) (hkl : k ≤ l) (a : ZMod (p^l))
    (ha : ¬ p ∣ a.val) (hpk : ¬ p ∣ k) :
    completeMonomialSumMod (p^l) k a =
      (p^(k-1) : ℕ)*completeMonomialSumMod (p^(l-k)) k (a.val : ZMod (p^(l-k))) := by
  rw [completeMonomialSumMod_primepower_good_filter l k (by omega) hk a ha hpk,
    sum_zmod_filter_dvd (p^l) p (p^(l-1)) (Fact.out : p.Prime).pos
      (by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l)])]
  simp_rw [primepower_reduced_phase l k hkl a]
  have hlen : p^(l-1) = p^(k-1)*p^(l-k) := by rw [← pow_add]; congr 1; omega
  have hper : Function.Periodic
      (fun y : ℕ => e ((a.val : ℝ)/(p^(l-k) : ℕ)*(y : ℝ)^k)) (p^(l-k)) := by
    simpa only [Int.cast_natCast] using
      rational_monomial_periodic k (a.val : ℤ) (pow_pos (Fact.out : p.Prime).pos (l-k))
  have hmod := completeMonomialSumMod_eq_range (p^(l-k)) k (a.val : ℤ)
  simp only [Int.cast_natCast] at hmod
  rw [hlen, periodic_sum_full_blocks hper, hmod]

theorem primepower_annihilator_power_iff {p : ℕ} [Fact p.Prime]
    (l j : ℕ) (hj : j ≤ l) (b : ZMod (p^l)) :
    b*(p^(l-j) : ℕ)=0 ↔ p^j ∣ b.val := by
  have heq : b*(p^(l-j) : ℕ) = ((b.val*p^(l-j) : ℕ) : ZMod (p^l)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [heq, ZMod.natCast_eq_zero_iff]
  have hdiv (n : ℕ) : p^l ∣ n*p^(l-j) ↔ p^j ∣ n := by
    rw [show p^l=p^j*p^(l-j) by rw [← pow_add, Nat.add_sub_of_le hj],
      Nat.mul_dvd_mul_iff_right (pow_pos (Fact.out : p.Prime).pos _)]
  exact hdiv b.val

/-- The derivative condition at a prime dividing the degree. The given
factorization `k=p^v*d`, with `p∤d`, retains the valuation explicitly. -/
theorem completeMonomialSumMod_primepower_valuation_filter {p : ℕ} [Fact p.Prime]
    (l k v d : ℕ) (hk : 2 ≤ k) (hkfactor : k=p^v*d)
    (hpd : ¬ p ∣ d) (hl : 2*(v+1) ≤ l) (a : ZMod (p^l))
    (ha : ¬ p ∣ a.val) :
    completeMonomialSumMod (p^l) k a =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter (fun x => p ∣ x.val),
        ZMod.stdAddChar (a*x^k) := by
  have hj : v+1 ≤ l := by omega
  have hiff (x : ZMod (p^l)) :
      a*(k : ZMod (p^l))*x^(k-1)*(p^(l-(v+1)) : ℕ)=0 ↔ p ∣ x.val := by
    rw [primepower_annihilator_power_iff l (v+1) hj]
    have hprod : a*(k : ZMod (p^l))*x^(k-1) =
        ((a.val*k*x.val^(k-1) : ℕ) : ZMod (p^l)) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [hprod, dvd_zmod_val_iff_dvd (pow_dvd_pow p hj)]
    have hfactor : a.val*k*x.val^(k-1) = (a.val*d*x.val^(k-1))*p^v := by
      nth_rw 1 [hkfactor]
      ring
    rw [hfactor, pow_succ', Nat.mul_dvd_mul_iff_right
      (pow_pos (Fact.out : p.Prime).pos _)]
    simp only [(Fact.out : p.Prime).dvd_mul, ha, hpd, false_or]
    constructor
    · exact (Fact.out : p.Prime).dvd_of_dvd_pow
    · intro hx
      exact (dvd_pow_self p (by omega : k-1 ≠ 0)).trans (pow_dvd_pow_of_dvd hx (k-1))
  rw [completeMonomialSumMod_primepower_filter l (v+1) k hl a]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff x
  · intro x _
    rfl

theorem completeMonomialSumMod_primepower_recurrence_of_filter {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hk : 1 ≤ k) (hkl : k ≤ l) (a : ZMod (p^l))
    (hfilter : completeMonomialSumMod (p^l) k a =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter (fun x => p ∣ x.val),
        ZMod.stdAddChar (a*x^k)) :
    completeMonomialSumMod (p^l) k a =
      (p^(k-1) : ℕ)*completeMonomialSumMod (p^(l-k)) k (a.val : ZMod (p^(l-k))) := by
  rw [hfilter, sum_zmod_filter_dvd (p^l) p (p^(l-1)) (Fact.out : p.Prime).pos
      (by rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ l)])]
  simp_rw [primepower_reduced_phase l k hkl a]
  have hlen : p^(l-1) = p^(k-1)*p^(l-k) := by rw [← pow_add]; congr 1; omega
  have hper : Function.Periodic
      (fun y : ℕ => e ((a.val : ℝ)/(p^(l-k) : ℕ)*(y : ℝ)^k)) (p^(l-k)) := by
    simpa only [Int.cast_natCast] using
      rational_monomial_periodic k (a.val : ℤ) (pow_pos (Fact.out : p.Prime).pos (l-k))
  have hmod := completeMonomialSumMod_eq_range (p^(l-k)) k (a.val : ℤ)
  simp only [Int.cast_natCast] at hmod
  rw [hlen, periodic_sum_full_blocks hper, hmod]

/-- A uniform recurrence that also covers primes dividing the degree. -/
theorem completeMonomialSumMod_primepower_recurrence_valuation {p : ℕ} [Fact p.Prime]
    (l k v d : ℕ) (hk : 2 ≤ k) (hkfactor : k=p^v*d)
    (hpd : ¬ p ∣ d) (hl : 2*(v+1) ≤ l) (hkl : k ≤ l)
    (a : ZMod (p^l)) (ha : ¬ p ∣ a.val) :
    completeMonomialSumMod (p^l) k a =
      (p^(k-1) : ℕ)*completeMonomialSumMod (p^(l-k)) k (a.val : ZMod (p^(l-k))) := by
  exact completeMonomialSumMod_primepower_recurrence_of_filter l k (by omega) hkl a
    (completeMonomialSumMod_primepower_valuation_filter l k v d hk hkfactor hpd hl a ha)

/-- Degree eight needs no exceptional-prime hypothesis: the prime `2`
uses the valuation-three shift, and every odd prime uses the good-prime
shift. The threshold `l≥8` covers both. -/
theorem completeMonomialSumMod_degree8_recurrence {p : ℕ} [Fact p.Prime]
    (l : ℕ) (hl : 8 ≤ l) (a : ZMod (p^l)) (ha : ¬ p ∣ a.val) :
    completeMonomialSumMod (p^l) 8 a =
      (p^7 : ℕ)*completeMonomialSumMod (p^(l-8)) 8 (a.val : ZMod (p^(l-8))) := by
  by_cases hp2 : p=2
  · subst p
    exact completeMonomialSumMod_primepower_recurrence_valuation l 8 3 1
      (by norm_num) (by norm_num) (by norm_num) (by omega) hl a ha
  · apply completeMonomialSumMod_primepower_recurrence_good l 8 (by norm_num) hl a ha
    intro hd
    have hd2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow
      (m := 2) (n := 3) (by norm_num; exact hd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp2 h

/-- Degree nine likewise includes its exceptional prime `3`. -/
theorem completeMonomialSumMod_degree9_recurrence {p : ℕ} [Fact p.Prime]
    (l : ℕ) (hl : 9 ≤ l) (a : ZMod (p^l)) (ha : ¬ p ∣ a.val) :
    completeMonomialSumMod (p^l) 9 a =
      (p^8 : ℕ)*completeMonomialSumMod (p^(l-9)) 9 (a.val : ZMod (p^(l-9))) := by
  by_cases hp3 : p=3
  · subst p
    exact completeMonomialSumMod_primepower_recurrence_valuation l 9 2 1
      (by norm_num) (by norm_num) (by norm_num) (by omega) hl a ha
  · apply completeMonomialSumMod_primepower_recurrence_good l 9 (by norm_num) hl a ha
    intro hd
    have hd3 : p ∣ 3 := (Fact.out : p.Prime).dvd_of_dvd_pow
      (m := 3) (n := 2) (by norm_num; exact hd)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp3 h

#print axioms completeMonomialSumMod_primepower_small
#print axioms completeMonomialSumMod_primepower_recurrence_good
#print axioms completeMonomialSumMod_primepower_recurrence_valuation
#print axioms completeMonomialSumMod_degree8_recurrence
#print axioms completeMonomialSumMod_degree9_recurrence

end Waring.EndgameCompletion

import Waring.EndgameCompletionCompleteSums

/-!
# Exact stationary-phase filtering for complete monomial sums

A square-zero shift makes the monomial's first-order Taylor expansion exact.
Averaging a complete sum over those shifts removes every residue where the
first derivative has a nontrivial additive character. These are finite
identities, with no asymptotic estimate or p-adic source theorem assumed.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

theorem add_pow_succ_of_sq_zero {R : Type*} [CommRing R]
    (x y : R) (hy : y^2=0) (n : ℕ) :
    (x+y)^(n+1) = x^(n+1)+(n+1 : ℕ)*x^n*y := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (x+y)^((n+1)+1) = (x+y)^(n+1)*(x+y) := pow_succ _ _
        _ = (x^(n+1)+(n+1 : ℕ)*x^n*y)*(x+y) := by rw [ih]
        _ = x^((n+1)+1)+((n+1)+1 : ℕ)*x^(n+1)*y+
            ((n+1 : ℕ)*x^n)*y^2 := by push_cast; ring
        _ = _ := by rw [hy, mul_zero, add_zero]

theorem add_pow_of_sq_zero {R : Type*} [CommRing R]
    (x y : R) (hy : y^2=0) (k : ℕ) :
    (x+y)^k = x^k+(k : R)*x^(k-1)*y := by
  cases k with
  | zero => simp
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
      add_pow_succ_of_sq_zero x y hy n

/-- Orthogonality over any full period of one additive phase. The period
need not equal its exact order. -/
theorem stdAddChar_sum_range (q M : ℕ) [NeZero q] (r : ZMod q)
    (hMr : (M : ZMod q)*r=0) :
    (∑ t ∈ Finset.range M, ZMod.stdAddChar (r*(t : ZMod q))) =
      if r=0 then (M : ℂ) else 0 := by
  by_cases hr : r=0
  · simp [hr, AddChar.map_zero_eq_one]
  · have hchar : ZMod.stdAddChar r ≠ (1 : ℂ) := by
      intro h
      apply hr
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using h
    have hroot : ZMod.stdAddChar r^M = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hMr, AddChar.map_zero_eq_one]
    have hpower (t : ℕ) : ZMod.stdAddChar (r*(t : ZMod q)) = ZMod.stdAddChar r^t := by
      simpa only [nsmul_eq_mul, mul_comm] using ZMod.stdAddChar.map_nsmul_eq_pow t r
    simp_rw [hpower]
    rw [geom_sum_eq hchar, hroot, sub_self, zero_div, if_neg hr]

/-- Exact stationary-phase filter on a residue ring. For prime powers, one
chooses `h=p^(l-j)` and `M=p^j`; the two shift conditions become elementary
divisibility statements, and the surviving residues satisfy the displayed
derivative-zero condition. -/
theorem completeMonomialSumMod_stationary_filter (q M : ℕ) [NeZero q]
    (hM : 0 < M) (k : ℕ) (a h : ZMod q) (hh : h^2=0)
    (hMh : (M : ZMod q)*h=0) :
    completeMonomialSumMod q k a =
      ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter
        (fun x => a*(k : ZMod q)*x^(k-1)*h=0), ZMod.stdAddChar (a*x^k) := by
  have hshift (t : ℕ) :
      (∑ x : ZMod q, ZMod.stdAddChar (a*(x+h*(t : ZMod q))^k)) =
        completeMonomialSumMod q k a := by
    unfold completeMonomialSumMod
    exact Fintype.sum_equiv (Equiv.addRight (h*(t : ZMod q))) _ _ (fun _ => rfl)
  have hlinear (x : ZMod q) :
      (∑ t ∈ Finset.range M, ZMod.stdAddChar ((a*(k : ZMod q)*x^(k-1)*h)*(t : ZMod q))) =
        if a*(k : ZMod q)*x^(k-1)*h=0 then (M : ℂ) else 0 := by
    apply stdAddChar_sum_range
    calc
      _ = (a*(k : ZMod q)*x^(k-1))*((M : ZMod q)*h) := by ring
      _ = 0 := by rw [hMh, mul_zero]
  have havg : (M : ℂ)*completeMonomialSumMod q k a =
      ∑ x : ZMod q, ZMod.stdAddChar (a*x^k)*
        (∑ t ∈ Finset.range M, ZMod.stdAddChar ((a*(k : ZMod q)*x^(k-1)*h)*(t : ZMod q))) := by
    calc
      _ = ∑ _t ∈ Finset.range M, completeMonomialSumMod q k a := by simp
      _ = ∑ t ∈ Finset.range M, ∑ x : ZMod q,
          ZMod.stdAddChar (a*(x+h*(t : ZMod q))^k) :=
        Finset.sum_congr rfl (fun t _ => (hshift t).symm)
      _ = ∑ x : ZMod q, ∑ t ∈ Finset.range M,
          ZMod.stdAddChar (a*(x+h*(t : ZMod q))^k) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        have hht : (h*(t : ZMod q))^2=0 := by rw [mul_pow, hh, zero_mul]
        rw [add_pow_of_sq_zero x (h*(t : ZMod q)) hht, mul_add,
          AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hlinear] at havg
  apply mul_left_cancel₀ (a := (M : ℂ)) (by exact_mod_cast Nat.ne_of_gt hM)
  calc
    _ = ∑ x : ZMod q, ZMod.stdAddChar (a*x^k)*
        (if a*(k : ZMod q)*x^(k-1)*h=0 then (M : ℂ) else 0) := havg
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [mul_comm]

/-- At a prime-power modulus, shifts by `p^(l-j)` have square zero whenever
`2j ≤ l`. The averaging period is `p^j`. -/
theorem completeMonomialSumMod_primepower_filter {p : ℕ} [Fact p.Prime]
    (l j k : ℕ) (hj : 2*j ≤ l) (a : ZMod (p^l)) :
    completeMonomialSumMod (p^l) k a =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter
        (fun x => a*(k : ZMod (p^l))*x^(k-1)*(p^(l-j) : ℕ)=0),
        ZMod.stdAddChar (a*x^k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  apply completeMonomialSumMod_stationary_filter (p^l) (p^j) (pow_pos hp j)
  · rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    rw [← pow_mul]
    exact pow_dvd_pow p (by omega)
  · rw [← Nat.cast_mul, ← pow_add,
      show j+(l-j)=l by omega, ZMod.natCast_self]

theorem primepower_annihilator_iff {p : ℕ} [Fact p.Prime]
    (l : ℕ) (hl : 1 ≤ l) (b : ZMod (p^l)) :
    b*(p^(l-1) : ℕ)=0 ↔ p ∣ b.val := by
  have heq : b*(p^(l-1) : ℕ) = ((b.val*p^(l-1) : ℕ) : ZMod (p^l)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [heq, ZMod.natCast_eq_zero_iff]
  have hdiv (n : ℕ) : p^l ∣ n*p^(l-1) ↔ p ∣ n := by
    rw [show p^l=p*p^(l-1) by rw [← pow_succ', Nat.sub_add_cancel hl],
      Nat.mul_dvd_mul_iff_right (pow_pos (Fact.out : p.Prime).pos _)]
  exact hdiv b.val

theorem castHom_primepower_eq_val {p : ℕ} [Fact p.Prime]
    (l : ℕ) (hl : 1 ≤ l) (b : ZMod (p^l)) :
    ZMod.castHom (dvd_pow_self p (by omega : l ≠ 0)) (ZMod p) b =
      (b.val : ZMod p) := by
  calc
    _ = ZMod.castHom (dvd_pow_self p (by omega : l ≠ 0)) (ZMod p)
        ((b.val : ℕ) : ZMod (p^l)) := by rw [ZMod.natCast_zmod_val]
    _ = _ := map_natCast _ _

/-- When the prime divides neither the coefficient nor the degree, every
nonstationary unit residue disappears. The surviving residues are exactly
the multiples of the prime. -/
theorem completeMonomialSumMod_primepower_good_filter {p : ℕ} [Fact p.Prime]
    (l k : ℕ) (hl : 2 ≤ l) (hk : 2 ≤ k) (a : ZMod (p^l))
    (ha : ¬ p ∣ a.val) (hpk : ¬ p ∣ k) :
    completeMonomialSumMod (p^l) k a =
      ∑ x ∈ (Finset.univ : Finset (ZMod (p^l))).filter (fun x => p ∣ x.val),
        ZMod.stdAddChar (a*x^k) := by
  have hl1 : 1 ≤ l := by omega
  let π : ZMod (p^l) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega : l ≠ 0)) (ZMod p)
  have hπ (b : ZMod (p^l)) : π b = (b.val : ZMod p) :=
    castHom_primepower_eq_val l hl1 b
  have hπa : π a ≠ 0 := by rw [hπ, ne_eq, ZMod.natCast_eq_zero_iff]; exact ha
  have hπk : (k : ZMod p) ≠ 0 := by rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact hpk
  have hiff (x : ZMod (p^l)) :
      a*(k : ZMod (p^l))*x^(k-1)*(p^(l-1) : ℕ)=0 ↔ p ∣ x.val := by
    rw [primepower_annihilator_iff l hl1,
      ← ZMod.natCast_eq_zero_iff ((a*(k : ZMod (p^l))*x^(k-1)).val) p,
      ← hπ, map_mul, map_mul, map_natCast, map_pow]
    simp only [mul_eq_zero, hπa, hπk, false_or,
      pow_eq_zero_iff (show k-1 ≠ 0 by omega)]
    rw [hπ, ZMod.natCast_eq_zero_iff]
  rw [completeMonomialSumMod_primepower_filter l 1 k (by omega) a]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff x
  · intro x _
    rfl

#print axioms completeMonomialSumMod_stationary_filter
#print axioms completeMonomialSumMod_primepower_filter
#print axioms completeMonomialSumMod_primepower_good_filter

end Waring.EndgameCompletion

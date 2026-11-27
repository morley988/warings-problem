import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

/-! Elementary explicit Chebyshev bounds for the count of primes up to an integer. -/

namespace WaringLinear.PrimeCountingChebyshev

open Finset

private def primes (n : ℕ) := (range (n + 1)).filter Nat.Prime

private theorem card_primes (n : ℕ) : (primes n).card = Nat.primeCounting n := by
  simp [primes, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private theorem central_lower (m : ℕ) (hm : 4 ≤ m) : 2 ^ m ≤ m.centralBinom := by
  by_contra! h
  have eq : (2 : ℕ) ^ m * 2 ^ m = 4 ^ m := by rw [← mul_pow]; norm_num
  have hbad := Nat.four_pow_lt_mul_centralBinom m hm
  exact (not_lt_of_ge ((Nat.mul_le_mul (show m < 2 ^ m from Nat.lt_two_pow_self).le h.le).trans eq.le)) hbad

private theorem central_upper (m : ℕ) (hm : 0 < m) :
    m.centralBinom ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := by
  let f (p : ℕ) := p ^ m.centralBinom.factorization p
  have hfilter : ∏ p ∈ primes (2 * m), f p = m.centralBinom := by
    rw [← Nat.prod_pow_factorization_centralBinom m]
    apply Finset.prod_filter_of_ne
    intro p _ hp
    contrapose! hp
    simp [f, Nat.factorization_eq_zero_of_non_prime _ hp]
  rw [← hfilter, ← card_primes, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (Nat.mul_pos (by decide) hm)

private theorem lower (n : ℕ) (hn : 8 ≤ n) :
    (Real.log 2 / 3) * n ≤ (Nat.primeCounting n : ℝ) * Real.log n := by
  let m := n / 2
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hn2 : 2 * m ≤ n := by dsimp [m]; omega
  have hn3 : n ≤ 3 * m := by dsimp [m]; omega
  have hp : 2 ^ m ≤ n ^ (Nat.primeCounting n) := calc
    2 ^ m ≤ m.centralBinom := central_lower _ hm
    _ ≤ (2 * m) ^ (Nat.primeCounting (2 * m)) := central_upper _ (by omega)
    _ ≤ n ^ (Nat.primeCounting (2 * m)) := Nat.pow_le_pow_left hn2 _
    _ ≤ n ^ (Nat.primeCounting n) :=
      Nat.pow_le_pow_right (by omega) (Nat.monotone_primeCounting hn2)
  have hpr : (2 : ℝ) ^ m ≤ (n : ℝ) ^ (Nat.primeCounting n) := by exact_mod_cast hp
  have hlog := Real.log_le_log (by positivity) hpr
  rw [Real.log_pow, Real.log_pow] at hlog
  have hn3' : (n : ℝ) ≤ 3 * m := by exact_mod_cast hn3
  have hpos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (sub_nonneg.mpr hn3') hpos]

private theorem upper (n : ℕ) (hn : 8 ≤ n) :
    (Nat.primeCounting n : ℝ) * Real.log n ≤ (2 + 2 * Real.log 4) * n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  let S := primes n
  have hprime (p : ℕ) (hp : p ∈ S) : Nat.Prime p := (mem_filter.mp hp).2
  have hp_pos (p : ℕ) (hp : p ∈ S) : (0 : ℝ) < p := by
    exact_mod_cast (hprime p hp).pos
  have htheta : ∑ p ∈ S, Real.log p ≤ n * Real.log 4 := by
    have hc : (∏ p ∈ S, (p : ℝ)) ≤ (4 : ℝ) ^ n := by
      rw [← Nat.cast_prod]
      exact_mod_cast primorial_le_4_pow n
    have hlog := Real.log_le_log (Finset.prod_pos hp_pos) hc
    rwa [Real.log_prod _ _ (fun p hp => (hp_pos p hp).ne'), Real.log_pow] at hlog
  have hsmall : (S.filter (· ≤ n.sqrt)).card ≤ n.sqrt := by
    have hsub : S.filter (· ≤ n.sqrt) ⊆ Icc 1 n.sqrt := by
      intro p hp
      obtain ⟨ha,hb⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(hprime p ha).one_lt.le,hb⟩
    simpa using card_le_card hsub
  have hs : ((S.filter (· ≤ n.sqrt)).card : ℝ) ≤ Real.sqrt n :=
    (show ((S.filter (· ≤ n.sqrt)).card : ℝ) ≤ n.sqrt by exact_mod_cast hsmall).trans
      Real.nat_sqrt_le_real_sqrt
  have hroot : Real.log n ≤ 2 * Real.sqrt n := by
    have hh := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hnr)
    rw [Real.log_sqrt hnr.le] at hh
    linarith
  have hsmallmass : ((S.filter (· ≤ n.sqrt)).card : ℝ) * Real.log n ≤ 2 * n := by
    calc
      _ ≤ Real.sqrt n * (2 * Real.sqrt n) := mul_le_mul hs hroot hnlog (Real.sqrt_nonneg _)
      _ = 2 * n := by nlinarith [Real.sq_sqrt hnr.le]
  have hterm (p : ℕ) (hp : p ∈ S) :
      Real.log n ≤ (if p ≤ n.sqrt then Real.log n else 0) + 2 * Real.log p := by
    split_ifs with h
    · have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hprime p hp).one_lt.le)
      linarith
    · have hpp : (n : ℝ) ≤ (p : ℝ) ^ 2 := by
        exact_mod_cast (Nat.sqrt_lt'.mp (Nat.lt_of_not_ge h)).le
      have hh := Real.log_le_log hnr hpp
      rw [Real.log_pow] at hh
      norm_num at hh ⊢
      exact hh
  have htotal := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum, ← sum_filter] at htotal
  simp only [sum_const, nsmul_eq_mul] at htotal
  rw [← card_primes]
  change (S.card : ℝ) * Real.log n ≤ _
  linarith

/-- Explicit, two-sided Chebyshev prime-counting estimates. -/
theorem primeCounting_bounds (n : ℕ) (hn : 8 ≤ n) :
    (Real.log 2 / 3) * n ≤ (Nat.primeCounting n : ℝ) * Real.log n ∧
    (Nat.primeCounting n : ℝ) * Real.log n ≤ (2 + 2 * Real.log 4) * n :=
  ⟨lower n hn, upper n hn⟩

/-- Chebyshev bounds for real endpoints, with the count including the endpoint. -/
theorem primeCounting_real_bounds (x : ℝ) (hx : 9 ≤ x) :
    (Real.log 2 / 6) * x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ∧
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x ≤ (4 + 4 * Real.log 4) * x := by
  let n := ⌊x⌋₊
  have hn : 8 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnlog := Real.log_le_log (by linarith : (0 : ℝ) < n) hnx
  have hxlog : Real.log x ≤ 2 * Real.log n := by
    have h : x ≤ (n : ℝ)^2 := by nlinarith
    have h' := Real.log_le_log (by linarith : 0 < x) h
    simpa using h'
  obtain ⟨hl,hu⟩ := primeCounting_bounds n hn
  have hc : 0 ≤ (Nat.primeCounting n : ℝ) := by positivity
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfour : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  constructor
  · calc
      (Real.log 2 / 6) * x ≤ (Real.log 2 / 3) * n := by
        nlinarith [mul_nonneg (show 0 ≤ 2 * (n : ℝ) - x by linarith) htwo]
      _ ≤ _ := hl.trans (mul_le_mul_of_nonneg_left hnlog hc)
  · calc
      (Nat.primeCounting n : ℝ) * Real.log x ≤
          2 * ((Nat.primeCounting n : ℝ) * Real.log n) := by
        nlinarith [mul_le_mul_of_nonneg_left hxlog hc]
      _ ≤ 2 * ((2 + 2 * Real.log 4) * n) := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hnx) hfour]

/-- Division form for partial summation over real intervals. -/
theorem primeCounting_div_bounds (x : ℝ) (hx : 9 ≤ x) :
    (Real.log 2 / 6) * x / Real.log x ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (4 + 4 * Real.log 4) * x / Real.log x := by
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨hl,hu⟩ := primeCounting_real_bounds x hx
  exact ⟨(div_le_iff₀ hlog).2 hl, (le_div_iff₀ hlog).2 hu⟩

#print axioms primeCounting_bounds
#print axioms primeCounting_div_bounds

end WaringLinear.PrimeCountingChebyshev

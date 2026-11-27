import Waring.CoefficientPower
import Mathlib.Data.Nat.Prime.Basic

/-!
# Exact smooth factor extraction for efficient differencing

Every positive R-smooth integer x greater than M has a divisor in the
interval (M, M R].  Both that divisor and the complementary quotient remain
R-smooth, and the quotient has size strictly less than P/M when x <= P.

This is an elementary combinatorial ingredient of the smooth block
decomposition used in efficient differencing.  The proof is by strong
induction, removing one prime factor at a time.  It does not assume a
factorization theorem or an analytic source estimate as a premise.
-/

noncomputable section
namespace Waring.SmoothMoments

/-- Smoothness is inherited by divisors. -/
theorem IsSmooth.of_dvd {n d : ℕ} {R : ℝ} (hn : IsSmooth n R) (hd : d ∣ n) :
    IsSmooth d R := by
  intro p hp hpd
  exact hn p hp (hpd.trans hd)

/-- A smooth integer greater than M has a divisor between M and M R. -/
theorem IsSmooth.exists_divisor_in_window {n : ℕ} {M R : ℝ}
    (hn : IsSmooth n R) (hM : 1 ≤ M) (hMn : M < (n : ℝ)) :
    ∃ d : ℕ, d ∣ n ∧ M < (d : ℝ) ∧ (d : ℝ) ≤ M * R := by
  suffices h : ∀ n : ℕ, IsSmooth n R → M < (n : ℝ) →
      ∃ d : ℕ, d ∣ n ∧ M < (d : ℝ) ∧ (d : ℝ) ≤ M * R by
    exact h n hn hMn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hMn
    have hn_gt_one : 1 < n := by exact_mod_cast (lt_of_le_of_lt hM hMn)
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hpR : (p : ℝ) ≤ R := hn p hp hpn
    obtain ⟨m, hnm⟩ := hpn
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      simp only [hm0, mul_zero] at hnm
      omega
    have hmlt : m < n := by
      calc
        m = 1 * m := (one_mul _).symm
        _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt hmpos
        _ = n := hnm.symm
    have hmdvd : m ∣ n := ⟨p, by rw [hnm, mul_comm]⟩
    by_cases hMm : M < (m : ℝ)
    · obtain ⟨d, hdm, hdM, hdMR⟩ := ih m hmlt (hn.of_dvd hmdvd) hMm
      exact ⟨d, hdm.trans hmdvd, hdM, hdMR⟩
    · refine ⟨n, dvd_refl n, hMn, ?_⟩
      have hmM : (m : ℝ) ≤ M := le_of_not_gt hMm
      have hR0 : 0 ≤ R := (by positivity : (0 : ℝ) ≤ p).trans hpR
      have hprod := mul_le_mul hpR hmM (by positivity : (0 : ℝ) ≤ m) hR0
      calc
        (n : ℝ) = (p : ℝ) * (m : ℝ) := by exact_mod_cast hnm
        _ ≤ R * M := hprod
        _ = M * R := mul_comm _ _

/-- The complementary factor is smooth, positive, and has the exact
shrunk length required for a smooth block decomposition. -/
theorem smooth_factorization_in_window {n : ℕ} {P R M : ℝ}
    (hn : n ∈ smoothNumbers P R) (hM : 1 ≤ M) (hMn : M < (n : ℝ)) :
    ∃ d u : ℕ, n = d * u ∧
      d ∈ CoefficientPower.coefficientBlock P R M ∧
      u ∈ smoothNumbers (P / M) R ∧ (u : ℝ) < P / M := by
  obtain ⟨⟨hnpos, hnP⟩, hs⟩ := mem_smoothNumbers.mp hn
  obtain ⟨d, hdn, hMd, hdMR⟩ := hs.exists_divisor_in_window hM hMn
  obtain ⟨u, hnu⟩ := hdn
  have hdposR : 0 < (d : ℝ) := lt_of_lt_of_le zero_lt_one hM |>.trans hMd
  have hdpos : 0 < d := by exact_mod_cast hdposR
  have hn0 : 0 < n := by omega
  have hupos : 0 < u := by
    by_contra hu
    have hu0 : u = 0 := by omega
    simp only [hu0, mul_zero] at hnu
    omega
  have hdn' : d ∣ n := ⟨u, hnu⟩
  have hun : u ∣ n := ⟨d, by rw [hnu, mul_comm]⟩
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hPpos : 0 < P := by
    have hfl : (1 : ℝ) ≤ ⌊P⌋₊ := by exact_mod_cast hnpos.trans hnP
    have hflpos : 0 < ⌊P⌋₊ := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hfl)
    exact zero_lt_one.trans_le (Nat.floor_pos.mp hflpos)
  have hnPR : (n : ℝ) ≤ P :=
    (by exact_mod_cast hnP : (n : ℝ) ≤ ⌊P⌋₊).trans (Nat.floor_le hPpos.le)
  have hnuR : (n : ℝ) = (d : ℝ) * (u : ℝ) := by exact_mod_cast hnu
  have huR : 0 < (u : ℝ) := by exact_mod_cast hupos
  have huPM : (u : ℝ) < P / M := by
    apply (lt_div_iff₀ hMpos).mpr
    have h := mul_lt_mul_of_pos_right hMd huR
    calc
      (u : ℝ) * M = M * (u : ℝ) := mul_comm _ _
      _ < (d : ℝ) * (u : ℝ) := h
      _ = (n : ℝ) := hnuR.symm
      _ ≤ P := hnPR
  refine ⟨d, u, hnu, ?_, ?_, huPM⟩
  · apply Finset.mem_filter.mpr
    refine ⟨mem_smoothNumbers.mpr ⟨⟨by omega, ?_⟩, hs.of_dvd hdn'⟩, hMd, hdMR⟩
    exact (Nat.le_of_dvd hn0 hdn').trans hnP
  · exact mem_smoothNumbers.mpr ⟨⟨by omega, Nat.le_floor huPM.le⟩, hs.of_dvd hun⟩

/-- Separate a positive integer into its part coprime to b and a remaining
factor whose prime divisors all divide b. No uniqueness is needed here. -/
theorem exists_coprime_supported_factorization (n b : ℕ) (hn : 0 < n) :
    ∃ w u : ℕ, n = w * u ∧ w.Coprime b ∧
      ∀ p : ℕ, p.Prime → p ∣ u → p ∣ b := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      refine ⟨1, 1, by norm_num, by simp, ?_⟩
      intro p hp hpd
      have hple : p ≤ 1 := Nat.le_of_dvd (by norm_num) hpd
      have hp2 := hp.two_le
      omega
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      obtain ⟨m, hnm⟩ := hpn
      have hmpos : 0 < m := by
        by_contra hm
        have hm0 : m = 0 := by omega
        simp only [hm0, mul_zero] at hnm
        omega
      have hmlt : m < n := by
        calc
          m = 1 * m := (one_mul _).symm
          _ < p * m := Nat.mul_lt_mul_of_pos_right hp.one_lt hmpos
          _ = n := hnm.symm
      obtain ⟨w, u, hmu, hwb, hu⟩ := ih m hmlt hmpos
      by_cases hpb : p ∣ b
      · refine ⟨w, p * u, ?_, hwb, ?_⟩
        · rw [hnm, hmu]
          ring
        · intro q hq hqd
          rcases hq.dvd_mul.mp hqd with hqp | hqu
          · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
            simpa only [hqp'] using hpb
          · exact hu q hq hqu
      · refine ⟨p * w, u, ?_, (hp.coprime_iff_not_dvd.mpr hpb).mul_left hwb, hu⟩
        rw [hnm, hmu, mul_assoc]

/-- Coprimality is preserved by extracting the smooth divisor window. -/
theorem IsSmooth.exists_coprime_divisor_in_window {n w b : ℕ} {M R : ℝ}
    (hn : IsSmooth n R) (hwn : w ∣ n) (hwb : w.Coprime b)
    (hM : 1 ≤ M) (hMw : M < (w : ℝ)) :
    ∃ d : ℕ, d ∣ n ∧ M < (d : ℝ) ∧ (d : ℝ) ≤ M * R ∧ d.Coprime b := by
  obtain ⟨d, hdw, hMd, hdMR⟩ := (hn.of_dvd hwn).exists_divisor_in_window hM hMw
  exact ⟨d, hdw.trans hwn, hMd, hdMR, hwb.coprime_dvd_left hdw⟩

/-- The exact arithmetic good/bad split used in the fundamental efficient-
differencing lemma: either a small divisor leaves only primes from b, or
there is a smooth block divisor coprime to b.  Applied to b equal to the
absolute derivative value, this is the split preceding equation (2.20) in
Wooley's 1990 thesis, Part III, printed page 237. -/
theorem smooth_coprime_window_or_supported_quotient {n b : ℕ} {P R M : ℝ}
    (hn : n ∈ smoothNumbers P R) (hM : 1 ≤ M) :
    (∃ w u : ℕ, n = w * u ∧ (w : ℝ) ≤ M ∧
      ∀ p : ℕ, p.Prime → p ∣ u → p ∣ b) ∨
    (∃ d : ℕ, d ∈ CoefficientPower.coefficientBlock P R M ∧ d ∣ n ∧ d.Coprime b) := by
  obtain ⟨⟨hnpos, hnP⟩, hs⟩ := mem_smoothNumbers.mp hn
  have hn0 : 0 < n := by omega
  obtain ⟨w, u, hnu, hwb, hu⟩ := exists_coprime_supported_factorization n b hn0
  by_cases hwM : (w : ℝ) ≤ M
  · exact Or.inl ⟨w, u, hnu, hwM, hu⟩
  · have hwn : w ∣ n := ⟨u, hnu⟩
    obtain ⟨d, hdn, hMd, hdMR, hdb⟩ :=
      hs.exists_coprime_divisor_in_window hwn hwb hM (lt_of_not_ge hwM)
    have hdpos : 0 < d := by
      have h : (0 : ℝ) < d := (lt_of_lt_of_le zero_lt_one hM).trans hMd
      exact_mod_cast h
    refine Or.inr ⟨d, ?_, hdn, hdb⟩
    apply Finset.mem_filter.mpr
    refine ⟨mem_smoothNumbers.mpr ⟨⟨by omega, ?_⟩, hs.of_dvd hdn⟩, hMd, hdMR⟩
    exact (Nat.le_of_dvd hn0 hdn).trans hnP

#print axioms IsSmooth.exists_divisor_in_window
#print axioms smooth_factorization_in_window
#print axioms exists_coprime_supported_factorization
#print axioms smooth_coprime_window_or_supported_quotient

end Waring.SmoothMoments

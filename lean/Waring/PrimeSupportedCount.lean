import Waring.DivisorBound
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Uniform sparsity of integers supported on a fixed set of prime divisors

Split every prime exponent modulo a fixed integer r. This writes a supported
integer n as a^r*b, with b dividing D^r and a at most P^(1/r). The already
proved divisor bound then gives a uniform small-power estimate. No prime
number theorem, Euler product estimate, or published counting bound is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PrimeSupportedCount

def IsPrimeSupported (n D : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ∣ D

noncomputable def supportedNumbers (N D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => IsPrimeSupported n D)

def powerRemainder (r n : ℕ) : ℕ := n / (Nat.floorRoot r n)^r

theorem root_mul_remainder (r n : ℕ) :
    (Nat.floorRoot r n)^r * powerRemainder r n = n :=
  Nat.mul_div_cancel' Nat.floorRoot_pow_dvd

theorem powerRemainder_pos {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    0 < powerRemainder r n := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hn Nat.floorRoot_pow_dvd
  · exact pow_pos (Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hr.ne', hn.ne'⟩)) r

/-- The remainder after removing an r-th power divides D^r. -/
theorem powerRemainder_dvd {r n D : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hD : 0 < D) (hs : IsPrimeSupported n D) :
    powerRemainder r n ∣ D^r := by
  apply (Nat.factorization_prime_le_iff_dvd (powerRemainder_pos hr hn).ne'
    (pow_pos hD r).ne').mp
  intro p hp
  have hfac : (powerRemainder r n).factorization p =
      n.factorization p - r * (n.factorization p / r) := by
    simp [powerRemainder, Nat.factorization_div Nat.floorRoot_pow_dvd,
      Nat.factorization_pow, Nat.factorization_floorRoot, Finsupp.floorDiv_def]
  rw [hfac, Nat.factorization_pow]
  change n.factorization p - r * (n.factorization p / r) ≤ r * D.factorization p
  by_cases hpn : p ∣ n
  · have hpD : 1 ≤ D.factorization p :=
      (hp.dvd_iff_one_le_factorization hD.ne').mp (hs p hp hpn)
    have hrem : n.factorization p - r * (n.factorization p / r) < r := by
      have h := Nat.mod_lt (n.factorization p) hr
      simpa only [Nat.mod_eq_sub_mul_div] using h
    have hprod : r ≤ r * D.factorization p := by nlinarith
    exact hrem.le.trans hprod
  · simp [Nat.factorization_eq_zero_of_not_dvd hpn]

theorem root_remainder_pair_injective (r : ℕ) :
    Function.Injective (fun n : ℕ => (Nat.floorRoot r n, powerRemainder r n)) := by
  intro m n h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  change Nat.floorRoot r m = Nat.floorRoot r n at ha
  change powerRemainder r m = powerRemainder r n at hb
  calc
    m = (Nat.floorRoot r m)^r * powerRemainder r m := (root_mul_remainder r m).symm
    _ = (Nat.floorRoot r n)^r * powerRemainder r n := by rw [ha, hb]
    _ = n := root_mul_remainder r n

/-- An exact finite counting bound before any asymptotic estimate. -/
theorem supportedNumbers_card_le {P : ℝ} (hP : 1 ≤ P) {D r : ℕ}
    (hD : 0 < D) (hr : 0 < r) :
    (supportedNumbers ⌊P⌋₊ D).card ≤
      ⌊P ^ (r : ℝ)⁻¹⌋₊ * (D^r).divisors.card := by
  classical
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hbound : ∀ n ∈ supportedNumbers ⌊P⌋₊ D,
      (Nat.floorRoot r n, powerRemainder r n) ∈
        (Finset.Icc 1 ⌊P ^ (r : ℝ)⁻¹⌋₊) ×ˢ (D^r).divisors := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn, hs⟩
    rcases Finset.mem_Icc.mp hn with ⟨hnpos, hnP⟩
    have hn0 : 0 < n := by omega
    have ha0 : 0 < Nat.floorRoot r n :=
      Nat.pos_of_ne_zero (Nat.floorRoot_ne_zero.mpr ⟨hr.ne', hn0.ne'⟩)
    have hapow : ((Nat.floorRoot r n : ℕ) : ℝ)^(r : ℝ) ≤ P := by
      rw [Real.rpow_natCast, ← Nat.cast_pow]
      have hrootn : (((Nat.floorRoot r n)^r : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hn0 (Nat.floorRoot_pow_dvd (n := r) (a := n))
      exact hrootn.trans
        ((by exact_mod_cast hnP : (n : ℝ) ≤ ⌊P⌋₊).trans (Nat.floor_le hP0))
    have haP : ((Nat.floorRoot r n : ℕ) : ℝ) ≤ P^(r : ℝ)⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos (by positivity) hP0 hrR).mpr hapow
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor haP⟩, ?_⟩
    exact Nat.mem_divisors.mpr ⟨powerRemainder_dvd hr hn0 hD hs, (pow_pos hD r).ne'⟩
  have hcard := Finset.card_le_card_of_injOn
    (fun n : ℕ => (Nat.floorRoot r n, powerRemainder r n)) hbound
    (fun _ _ _ _ h => root_remainder_pair_injective r h)
  simpa only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel] using hcard

/-- The exact count with its real root-length bound. -/
theorem supportedNumbers_card_le_real {P : ℝ} (hP : 1 ≤ P) {D r : ℕ}
    (hD : 0 < D) (hr : 0 < r) :
    ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤
      P ^ (r : ℝ)⁻¹ * ((D^r).divisors.card : ℝ) := by
  have hcard := supportedNumbers_card_le hP hD hr
  have hc : ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤
      (⌊P ^ (r : ℝ)⁻¹⌋₊ : ℝ) * ((D^r).divisors.card : ℝ) := by
    exact_mod_cast hcard
  exact hc.trans (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity))

/-- A fixed power split and the genuine divisor bound give uniform control. -/
theorem supportedNumbers_count_with_root (r : ℕ) (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ D : ℕ, 0 < D →
      ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤
        C * P^(r : ℝ)⁻¹ * (D : ℝ)^ε := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨C, hC, hb⟩ := DivisorBound.divisor_count_le_rpow (div_pos hε hrR)
  refine ⟨C, hC, ?_⟩
  intro P hP D hD
  have hdiv := hb (D^r) (pow_pos hD r)
  have hpow : (((D^r : ℕ) : ℝ))^(ε / (r : ℝ)) = (D : ℝ)^ε := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ D)]
    congr 1
    field_simp
  rw [hpow] at hdiv
  calc
    ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤
        P^(r : ℝ)⁻¹ * ((D^r).divisors.card : ℝ) := supportedNumbers_card_le_real hP hD hr
    _ ≤ P^(r : ℝ)⁻¹ * (C * (D : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = C * P^(r : ℝ)⁻¹ * (D : ℝ)^ε := by ring

/-- For every positive epsilon, supported integers satisfy a uniform
small-power bound, with the constant independent of both P and D. -/
theorem supportedNumbers_count_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ D : ℕ, 0 < D →
      ((supportedNumbers ⌊P⌋₊ D).card : ℝ) ≤ C * P^ε * (D : ℝ)^ε := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max 1 ε⁻¹)
  have hr1 : (1 : ℝ) < r := (le_max_left _ _).trans_lt hr
  have hrR : 0 < (r : ℝ) := zero_lt_one.trans hr1
  have hrN : 0 < r := by exact_mod_cast hrR
  have hinv : (r : ℝ)⁻¹ ≤ ε := by
    exact (inv_le_comm₀ hrR hε).mpr ((le_max_right _ _).trans hr.le)
  obtain ⟨C, hC, hb⟩ := supportedNumbers_count_with_root r hrN hε
  refine ⟨C, hC, ?_⟩
  intro P hP D hD
  exact (hb P hP D hD).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hinv) hC.le)
    (by positivity))

/-- The form used in efficient differencing: both the interval length and
the integer containing the permitted primes may grow polynomially in P. -/
theorem supportedNumbers_polynomial_scale {A B ε : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ D : ℕ, 0 < D →
      (D : ℝ) ≤ P^B →
      ((supportedNumbers ⌊P^A⌋₊ D).card : ℝ) ≤ C * P^ε := by
  let δ : ℝ := ε / (A + B + 1)
  have hden : 0 < A + B + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C, hC, hb⟩ := supportedNumbers_count_le_rpow hδ
  refine ⟨C, hC, ?_⟩
  intro P hP D hD hDP
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hPA : 1 ≤ P^A := Real.one_le_rpow hP hA
  have hsmall : A * δ + B * δ ≤ ε := by
    have hid : (A + B + 1) * δ = ε := by
      dsimp [δ]
      field_simp
    nlinarith
  calc
    ((supportedNumbers ⌊P^A⌋₊ D).card : ℝ) ≤
        C * (P^A)^δ * (D : ℝ)^δ := hb (P^A) hPA D hD
    _ ≤ C * (P^A)^δ * (P^B)^δ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hDP hδ.le) (by positivity)
    _ = C * P^(A * δ + B * δ) := by
      rw [← Real.rpow_mul hP0.le, ← Real.rpow_mul hP0.le,
        mul_assoc, ← Real.rpow_add hP0]
    _ ≤ C * P^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hsmall) hC.le

#print axioms powerRemainder_dvd
#print axioms supportedNumbers_card_le
#print axioms supportedNumbers_count_le_rpow
#print axioms supportedNumbers_polynomial_scale

end Waring.PrimeSupportedCount

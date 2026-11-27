import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Auxiliary cubic primes from Bertrand's theorem

Any two fixed positive power exponents eventually leave room for Bertrand's
factor two. No prime number theorem or prime-density estimate is used.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace WaringSiegel.WSL4Weil
open Filter Topology
open scoped Classical

theorem eventually_prime_in_power_interval (a b : ℝ) (ha : 0 < a) (hab : a < b) (N : ℕ) :
    ∀ᶠ P : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ N ≤ p ∧ P^a ≤ (p : ℝ) ∧ (p : ℝ) ≤ P^b := by
  have hA := (tendsto_rpow_atTop ha).eventually (eventually_ge_atTop (max (N : ℝ) 1))
  have hB := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℝ),hA,hB] with P hP hA hB
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hx1 : (1 : ℝ) ≤ P^a := (le_max_right _ _).trans hA
  have hxN : (N : ℝ) ≤ P^a := (le_max_left _ _).trans hA
  let n := Nat.ceil (P^a)
  have hn : n ≠ 0 := (Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hx1)).ne'
  obtain ⟨p,hp,hnp,hpn⟩ := Nat.exists_prime_lt_and_le_two_mul n hn
  have hnpR : (n : ℝ) < (p : ℝ) := by exact_mod_cast hnp
  have hlow : P^a ≤ (p : ℝ) := (Nat.le_ceil (P^a)).trans hnpR.le
  have hpnR : (p : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hpn
  have hceil : (n : ℝ) < P^a+1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hP0.le a)
  refine ⟨p,hp,by exact_mod_cast hxN.trans hlow,hlow,?_⟩
  calc
    (p : ℝ) ≤ 4*P^a := by nlinarith
    _ ≤ P^(b-a)*P^a := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hP0.le a)
    _ = P^b := by rw [← Real.rpow_add hP0]; congr 1; ring

theorem exists_auxiliary_cubic_prime :
    ∃ P0 : ℝ, 1 ≤ P0 ∧ ∀ P : ℝ, P0 < P → ∃ p : ℕ,
      p.Prime ∧ 173 ≤ p ∧ P^(1/10 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ P^(49/480 : ℝ) ∧
      (p : ℝ)^7 ≤ P ∧ 1 ≤ P/(p : ℝ) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (eventually_prime_in_power_interval (1/10 : ℝ) (49/480 : ℝ) (by norm_num) (by norm_num) 173)
  refine ⟨max 1 M,le_max_left _ _,fun P hP => ?_⟩
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP.le
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP1
  obtain ⟨p,hp,h173,hlow,hup⟩ := hM P ((le_max_right _ _).trans hP.le)
  refine ⟨p,hp,h173,hlow,hup,?_,?_⟩
  · calc
      (p : ℝ)^7 ≤ (P^(49/480 : ℝ))^7 := pow_le_pow_left₀ (Nat.cast_nonneg _) hup 7
      _ = P^((49/480 : ℝ)*(7 : ℕ)) := (Real.rpow_mul_natCast hP0.le _ 7).symm
      _ ≤ P^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
      _ = P := Real.rpow_one P
  · apply (le_div_iff₀ (Nat.cast_pos.mpr hp.pos)).mpr
    simp only [one_mul]
    exact hup.trans ((Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num : (49/480 : ℝ) ≤ 1)).trans_eq (Real.rpow_one P))
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.eventually_prime_in_power_interval
#print axioms WaringSiegel.WSL4Weil.exists_auxiliary_cubic_prime

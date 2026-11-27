import Waring.LocalSolubilityBase

/-! # Uniform positive local densities at the two Waring targets -/

noncomputable section
open scoped BigOperators
namespace Waring.LocalSolubility

theorem good_prime_powerSolutions_lower {k s p : ℕ} [NeZero p]
    (hp : p.Prime) (hk : 0 < k) (hks : k ≤ s) (hpk : ¬ p ∣ k) (r : ℕ) (n : ℤ) :
    p^(r*s) ≤ (powerSolutions k (s+1) (p^(r+1)) n).card := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,hb⟩ := prime_base_with_one hp hk hks n
  have hh := powerSolutions_card_lower_of_lifting hp.pos (pow_pos hp.pos r) 1 n b hb
    (by
      intro target htarget
      obtain ⟨y,hy,_⟩ := good_prime_power_lifts hp hpk htarget (by simp) r
      refine ⟨y,?_⟩
      simpa only [Nat.cast_mul,Nat.cast_pow,pow_succ'] using hy)
  rw [powerSolutions_card_congr_modulus (pow_succ' p r) k (s+1) n]
  simpa only [← pow_mul] using hh

theorem eighth_two_powerSolutions_lower (r : ℕ) (n : ℤ) :
    2^(37*r) ≤ (powerSolutions 8 38 (2^(r+5)) n).card := by
  obtain ⟨b,hb⟩ := base_with_one_of_modulus_le (k := 8) (s := 37) (B := 32)
    (by omega) (by omega) (by omega) n
  have hh := powerSolutions_card_lower_of_lifting (by omega : 0 < (32 : ℕ))
    (pow_pos (by omega : 0 < (2 : ℕ)) r) 1 n b hb
    (by
      intro target htarget
      obtain ⟨y,hy,_⟩ := eighth_two_power_lifts htarget (by simp) r
      refine ⟨y,?_⟩
      convert hy using 1 <;> norm_num [pow_add,mul_comm])
  have hq : 2^(r+5)=32*2^r := by norm_num [pow_add,mul_comm]
  rw [powerSolutions_card_congr_modulus hq 8 38 n]
  simpa only [← pow_mul,mul_comm] using hh

theorem ninth_three_powerSolutions_lower (r : ℕ) (n : ℤ) :
    3^(45*r) ≤ (powerSolutions 9 46 (3^(r+3)) n).card := by
  obtain ⟨b,hb⟩ := base_with_one_of_modulus_le (k := 9) (s := 45) (B := 27)
    (by omega) (by omega) (by omega) n
  have hh := powerSolutions_card_lower_of_lifting (by omega : 0 < (27 : ℕ))
    (pow_pos (by omega : 0 < (3 : ℕ)) r) 1 n b hb
    (by
      intro target htarget
      obtain ⟨y,hy,_⟩ := ninth_three_power_lifts htarget (by simp) r
      refine ⟨y,?_⟩
      convert hy using 1 <;> norm_num [pow_add,mul_comm])
  have hq : 3^(r+3)=27*3^r := by norm_num [pow_add,mul_comm]
  rw [powerSolutions_card_congr_modulus hq 9 46 n]
  simpa only [← pow_mul,mul_comm] using hh

def localDepth8 (p : ℕ) : ℕ := if p=2 then 5 else 1
def localDepth9 (p : ℕ) : ℕ := if p=3 then 3 else 1

/-- The lower density is uniform in the represented integer and in the
prime-power level. The prime-dependent base depth is explicit. -/
theorem degree8_local_count_lower {p : ℕ} [NeZero p] (hp : p.Prime) (r : ℕ) (n : ℤ) :
    p^(37*r) ≤ (powerSolutions 8 38 (p^(r+localDepth8 p)) n).card := by
  by_cases h2 : p=2
  · subst p
    simpa [localDepth8] using eighth_two_powerSolutions_lower r n
  · have hpk : ¬ p ∣ 8 := by
      intro h
      apply h2
      apply (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      exact hp.dvd_of_dvd_pow (show p ∣ 2^3 by norm_num; exact h)
    have hq : p^(r+localDepth8 p)=p^(r+1) := by simp [localDepth8,h2]
    rw [powerSolutions_card_congr_modulus hq 8 38 n]
    simpa only [mul_comm] using
      good_prime_powerSolutions_lower hp (by omega : 0 < (8 : ℕ))
        (by omega : 8 ≤ 37) hpk r n

theorem degree9_local_count_lower {p : ℕ} [NeZero p] (hp : p.Prime) (r : ℕ) (n : ℤ) :
    p^(45*r) ≤ (powerSolutions 9 46 (p^(r+localDepth9 p)) n).card := by
  by_cases h3 : p=3
  · subst p
    simpa [localDepth9] using ninth_three_powerSolutions_lower r n
  · have hpk : ¬ p ∣ 9 := by
      intro h
      apply h3
      apply (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      exact hp.dvd_of_dvd_pow (show p ∣ 3^2 by norm_num; exact h)
    have hq : p^(r+localDepth9 p)=p^(r+1) := by simp [localDepth9,h3]
    rw [powerSolutions_card_congr_modulus hq 9 46 n]
    simpa only [mul_comm] using
      good_prime_powerSolutions_lower hp (by omega : 0 < (9 : ℕ))
        (by omega : 9 ≤ 45) hpk r n

#print axioms degree8_local_count_lower
#print axioms degree9_local_count_lower
end Waring.LocalSolubility

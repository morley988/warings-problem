import WaringSiegel.WSL4WeilAuxiliaryPrimeChoice

/-! # The actual prime interval in field-volume variables -/
noncomputable section
set_option maxHeartbeats 700000
namespace WaringSiegel.WSL4Weil
open scoped Classical

theorem power_rpow_commute (P : ℝ) (hP : 0 ≤ P) (d : ℕ) (a : ℝ) :
    (P^a)^d = (P^d)^a := by
  rw [← Real.rpow_mul_natCast hP,← Real.rpow_natCast_mul hP]
  congr 1
  ring

theorem exists_auxiliary_cubic_prime_volume (d : ℕ) :
    ∃ P0 : ℝ, 1 ≤ P0 ∧ ∀ P : ℝ, P0 < P → ∃ p : ℕ,
      p.Prime ∧ 173 ≤ p ∧
      (P^d)^(1/10 : ℝ) ≤ (p : ℝ)^d ∧ (p : ℝ)^d ≤ (P^d)^(49/480 : ℝ) ∧
      (p : ℝ)^7 ≤ P ∧ 1 ≤ P/(p : ℝ) := by
  obtain ⟨P0,hP0,hchoice⟩ := exists_auxiliary_cubic_prime
  refine ⟨P0,hP0,fun P hP => ?_⟩
  have hP1 : 1 ≤ P := hP0.trans hP.le
  have hP0' : 0 ≤ P := zero_le_one.trans hP1
  obtain ⟨p,hp,h173,hlo,hhi,h7,hdiv⟩ := hchoice P hP
  refine ⟨p,hp,h173,?_,?_,h7,hdiv⟩
  · rw [← power_rpow_commute P hP0' d]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hP0' _) hlo d
  · rw [← power_rpow_commute P hP0' d]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hhi d
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.exists_auxiliary_cubic_prime_volume

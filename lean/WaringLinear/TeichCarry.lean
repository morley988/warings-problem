import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! # A short carry for odd prime-power summands

In the unramified scalar coefficient ring the consecutive lifts of the
residues modulo a prime have a carry of valuation exactly one.
The finite congruence below works for every positive power of an odd prime.
-/

namespace WaringLinear

/-- The carries of any function on consecutive integers telescope. -/
theorem consecutiveCarry_sum (f : ℕ → ℤ) (n : ℕ) :
    ∑ x ∈ Finset.range n, (f x + 1 - f (x + 1)) =
      f 0 + n - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Every prime-power exponent admits a three-term carry divisible by the
prime and nonzero modulo its square. The last of the three terms is signed. -/
theorem primePower_consecutive_carry (p a : ℕ) [Fact p.Prime] (ha : 0 < a) :
    ∃ x < p, (p : ℤ) ∣ (x : ℤ) ^ (p ^ a) + 1 - (x + 1 : ℤ) ^ (p ^ a) ∧
      ¬ (p : ℤ)^2 ∣ (x : ℤ) ^ (p ^ a) + 1 - (x + 1 : ℤ) ^ (p ^ a) := by
  classical
  have hp : p.Prime := Fact.out
  have hexp : 2 ≤ p ^ a := by
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
    rw [pow_succ]
    exact le_trans hp.two_le (Nat.le_mul_of_pos_left p (pow_pos hp.pos b))
  let f : ℕ → ℤ := fun x => (x : ℤ) ^ (p ^ a)
  have hdvd (x : ℕ) : (p : ℤ) ∣ f x + 1 - f (x + 1) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [f, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one]
    have hF (z : ZMod p) : z ^ (p ^ a) = z := by
      simpa only [ZMod.card p] using (FiniteField.pow_card_pow a z)
    rw [hF, hF, sub_self]
  have hnot : ¬ (p : ℤ)^2 ∣ (p : ℤ) := by
    exact_mod_cast (show ¬ p^2 ∣ p by
      intro h
      have := Nat.le_of_dvd hp.pos h
      nlinarith [hp.two_le])
  have hpow : (p : ℤ)^2 ∣ f p := by
    exact pow_dvd_pow (p : ℤ) hexp
  by_contra! hx
  have hsum : (p : ℤ)^2 ∣ ∑ x ∈ Finset.range p, (f x + 1 - f (x+1)) := by
    exact Finset.dvd_sum (fun x hx' => hx x (Finset.mem_range.mp hx') (hdvd x))
  rw [consecutiveCarry_sum] at hsum
  have hf0 : f 0 = 0 := by
    change (0 : ℤ) ^ (p ^ a) = 0
    exact zero_pow (by omega)
  rw [hf0, zero_add] at hsum
  exact hnot (by simpa only [sub_add_cancel] using dvd_add hsum hpow)

/-- For odd residue characteristic the signed carry is a sum of three
ordinary prime-power summands in the finite ring of precision two. -/
theorem primePower_three_residue_carry (p a : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ha : 0 < a) : ∃ u v w : ZMod (p^2),
    (p : ZMod (p^2)) ∣ u^(p^a) + v^(p^a) + w^(p^a) ∧
    u^(p^a) + v^(p^a) + w^(p^a) ≠ 0 := by
  obtain ⟨x, _, h, hn⟩ := primePower_consecutive_carry p a ha
  let z : ℤ := (x : ℤ) ^ (p^a) + 1 - (x+1 : ℤ) ^ (p^a)
  have hodd : Odd (p^a) := (Fact.out (p := p.Prime)).odd_of_ne_two hp2 |>.pow
  have hval : ((x : ZMod (p^2)) ^ (p^a) + (1 : ZMod (p^2)) ^ (p^a) +
      (-(x+1 : ZMod (p^2)))^(p^a)) = (z : ZMod (p^2)) := by
    rw [hodd.neg_pow]
    simp only [z, Int.cast_neg, Int.cast_add, Int.cast_pow, Int.cast_natCast, Int.cast_one,
      one_pow, sub_eq_add_neg]
  refine ⟨x,1,-(x+1 : ZMod (p^2)), ?_, ?_⟩
  · rw [hval]
    obtain ⟨t, ht⟩ := h
    refine ⟨(t : ZMod (p^2)), ?_⟩
    change ((z : ℤ) : ZMod (p^2)) = _
    change z = (p : ℤ) * t at ht
    rw [ht, Int.cast_mul, Int.cast_natCast]
  · rw [hval]
    intro hh
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p^2)).mp hh
    exact hn (by simpa only [Nat.cast_pow] using hv)

/-- The positive powers occurring in the carry are actual Teichmüller
residues, characterized at precision two by the equation t^p = t. -/
theorem primePower_teich_mod_square (p a : ℕ) [Fact p.Prime] (ha : 0 < a)
    (z : ZMod (p^2)) : (z ^ (p^a)) ^ p = z ^ (p^a) := by
  have hp : p.Prime := Fact.out
  have hb : (z ^ p) ^ p = z ^ p := by
    by_cases hd : p ∣ z.val
    · have hzero : z ^ p = 0 := by
        rw [← ZMod.natCast_zmod_val z, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        exact (pow_dvd_pow_of_dvd hd 2).trans (pow_dvd_pow _ hp.two_le)
      simp [hzero, hp.ne_zero]
    · have hc : z.val.Coprime (p^2) :=
        ((hp.coprime_iff_not_dvd.mpr hd).symm).pow_right _
      have hunit := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.pow_totient hc)
      have ht : Nat.totient (p^2) = p * (p-1) := by
        rw [Nat.totient_prime_pow hp (by decide : 0 < 2)]
        simp
      simp only [Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, ht, pow_mul] at hunit
      calc
        (z^p)^p = (z^p)^(p-1) * z^p := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
        _ = z^p := by rw [hunit, one_mul]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hz : z ^ (p ^ (b+1)) = (z^p) ^ (p^b) := by
    rw [pow_succ' p b, pow_mul]
  rw [hz, pow_right_comm (z^p) (p^b) p, hb]

/-- Three Teichmüller residues suffice to reach valuation exactly one. -/
theorem three_teich_carry (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ x y z : ZMod (p^2), x^p=x ∧ y^p=y ∧ z^p=z ∧
      (p : ZMod (p^2)) ∣ x+y+z ∧ x+y+z ≠ 0 := by
  obtain ⟨u,v,w,hd,hn⟩ := primePower_three_residue_carry p 1 hp2 (by decide)
  refine ⟨u^(p^1),v^(p^1),w^(p^1), ?_,?_,?_,hd,hn⟩ <;>
    apply primePower_teich_mod_square <;> decide

#print axioms consecutiveCarry_sum
#print axioms primePower_consecutive_carry
#print axioms primePower_three_residue_carry
#print axioms primePower_teich_mod_square
#print axioms three_teich_carry

end WaringLinear

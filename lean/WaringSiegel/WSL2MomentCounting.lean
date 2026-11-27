import WaringSiegel.WSL2MomentPolynomial

/-!
# Finite power-difference fibers and the fourth-moment divisor reduction

Every nonzero power difference is encoded by an actual nonzero divisor
`h = x-y`; at most `k-1` pairs remain for each shift.  The counting statements
are literal finite sets over the original integral domain.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

section Energy
variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- The actual zero-frequency fiber. -/
def zeroFrequencyCount (v : α → ι → ℤ) : ℕ :=
  (Finset.univ.filter (fun a => v a = 0)).card

theorem frequencyEnergy_eq_sum (v : α → ι → ℤ) :
    frequencyEnergy v = ∑ a, (frequencyFiber v a).card := by
  simp only [frequencyEnergy, frequencyFiber, Finset.card_eq_sum_ones,
    Finset.sum_filter, Fintype.sum_prod_type]

theorem frequencyEnergy_le_mul_card (v : α → ι → ℤ) (M : ℕ)
    (hM : ∀ a, (frequencyFiber v a).card ≤ M) :
    frequencyEnergy v ≤ M * Fintype.card α := by
  rw [frequencyEnergy_eq_sum]
  calc
    _ ≤ ∑ _a : α, M := Finset.sum_le_sum (fun a _ => hM a)
    _ = _ := by simp [Nat.mul_comm]

theorem zeroFrequencyCount_difference (v : α → ι → ℤ) :
    zeroFrequencyCount (fun p : α × α => v p.1 - v p.2) = frequencyEnergy v := by
  simp only [zeroFrequencyCount, frequencyEnergy, sub_eq_zero]

/-- Separate the possibly large zero fiber from uniformly bounded nonzero fibers. -/
theorem frequencyEnergy_le_zero_sq_add (v : α → ι → ℤ) (M : ℕ)
    (hM : ∀ a, v a ≠ 0 → (frequencyFiber v a).card ≤ M) :
    frequencyEnergy v ≤ (zeroFrequencyCount v)^2 + M * Fintype.card α := by
  rw [frequencyEnergy_eq_sum]
  have hf (a : α) : (frequencyFiber v a).card ≤
      (if v a = 0 then zeroFrequencyCount v else 0) + M := by
    by_cases hz : v a = 0
    · have heq : (frequencyFiber v a).card = zeroFrequencyCount v := by
        simp only [frequencyFiber, hz, zeroFrequencyCount, eq_comm]
      rw [heq, if_pos hz]
      omega
    · simpa only [if_neg hz, zero_add] using hM a hz
  have hsum : (∑ a, if v a = 0 then zeroFrequencyCount v else 0) =
      (zeroFrequencyCount v)^2 := by
    rw [← Finset.sum_filter]
    simp [zeroFrequencyCount, pow_two]
  calc
    _ ≤ ∑ a, ((if v a = 0 then zeroFrequencyCount v else 0) + M) :=
      Finset.sum_le_sum (fun a _ => hf a)
    _ = _ := by rw [Finset.sum_add_distrib, hsum]; simp [Nat.mul_comm]

end Energy

section PowerDifferences
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

/-- Actual ordered pairs from a finite root set having a prescribed power difference. -/
def powerDifferenceFiber (S : Finset R) (k : ℕ) (a : R) : Finset (R × R) :=
  (S.product S).filter (fun p => p.1^k - p.2^k = a)

/-- The actual allowed nonzero divisors, restricted to the difference set. -/
def powerDifferenceDivisors (S : Finset R) (a : R) : Finset R :=
  ((S.product S).image (fun p => p.1 - p.2)).filter (fun h => h ≠ 0 ∧ h ∣ a)

/-- The first difference of a pair is an actual ring divisor of its power difference. -/
theorem powerDifference_shift_mem_divisors (S : Finset R) (k : ℕ) {a : R} (ha : a ≠ 0)
    {p : R × R} (hp : p ∈ powerDifferenceFiber S k a) :
    p.1 - p.2 ∈ powerDifferenceDivisors S a := by
  obtain ⟨hpS, hpv⟩ := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨p, hpS, rfl⟩, ?_, ?_⟩
  · intro hz
    have heq := sub_eq_zero.mp hz
    apply ha
    rw [← hpv, heq, sub_self]
  · rw [← hpv]
    exact sub_dvd_pow_sub_pow p.1 p.2 k

/-- Once a nonzero shift is fixed, at most `k-1` pairs realize the power difference. -/
theorem powerDifference_shift_fiber_card_le (S : Finset R) (k : ℕ) (hk : 2 ≤ k)
    (a h : R) (hh : h ≠ 0) :
    ((powerDifferenceFiber S k a).filter (fun p => p.1 - p.2 = h)).card ≤ k - 1 := by
  let T := (powerDifferenceFiber S k a).filter (fun p => p.1 - p.2 = h)
  have hcard : T.card ≤ (S.filter (fun y => (y+h)^k-y^k = a)).card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      obtain ⟨hpT, hph⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpS, hpv⟩ := Finset.mem_filter.mp hpT
      apply Finset.mem_filter.mpr
      refine ⟨(Finset.mem_product.mp hpS).2, ?_⟩
      have heq : p.1 = p.2 + h := by
        simpa only [add_comm] using sub_eq_iff_eq_add.mp hph
      simpa only [← heq] using hpv
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      apply Prod.ext
      · rw [sub_eq_iff_eq_add.mp hp', sub_eq_iff_eq_add.mp hq', hpq]
      · exact hpq
  exact hcard.trans (shifted_power_fiber_card_le S k hk h hh a)

/-- Exact finite divisor reduction for every nonzero power-difference fiber. -/
theorem powerDifference_fiber_card_le_divisors (S : Finset R) (k : ℕ) (hk : 2 ≤ k)
    {a : R} (ha : a ≠ 0) :
    (powerDifferenceFiber S k a).card ≤ (k - 1) * (powerDifferenceDivisors S a).card := by
  let T := powerDifferenceFiber S k a
  have hi : T.image (fun p => p.1 - p.2) ⊆ powerDifferenceDivisors S a := by
    intro h hh
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
    exact powerDifference_shift_mem_divisors S k ha hp
  calc
    T.card ≤ (k - 1) * (T.image (fun p => p.1 - p.2)).card := by
      apply Finset.card_le_mul_card_image T (k - 1)
      intro h hh
      have hh0 := (Finset.mem_filter.mp (hi hh)).2.1
      exact powerDifference_shift_fiber_card_le S k hk a h hh0
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hi)

end PowerDifferences
end WaringSiegel.WSL2

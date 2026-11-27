import WaringSiegel.WSL2MomentCounting

/-!
# Actual monomial fourth moments reduced to bounded ring divisors

The divisor parameter below is an explicitly defined finite maximum over
actual nonzero power differences.  No fourth-moment or divisor-growth estimate
is assumed in the main finite inequality.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

variable {R ι α : Type*} [CommRing R] [IsDomain R] [CharZero R]
variable [Fintype ι] [Fintype α]

/-- Maximum number of allowed nonzero divisors among the nonzero power differences. -/
def nodeDivisorMaximum (nodes : α → R) (k : ℕ) : ℕ :=
  (Finset.univ : Finset (α × α)).sup (fun p =>
    if nodes p.1 ^ k - nodes p.2 ^ k = 0 then 0 else
      (powerDifferenceDivisors (Finset.univ.image nodes) (nodes p.1 ^ k - nodes p.2 ^ k)).card)

theorem nodeDivisorMaximum_bounds (nodes : α → R) (k : ℕ) (p : α × α)
    (hp : nodes p.1 ^ k - nodes p.2 ^ k ≠ 0) :
    (powerDifferenceDivisors (Finset.univ.image nodes) (nodes p.1 ^ k - nodes p.2 ^ k)).card ≤
      nodeDivisorMaximum nodes k := by
  have h := Finset.le_sup (f := fun p : α × α =>
    if nodes p.1 ^ k - nodes p.2 ^ k = 0 then 0 else
      (powerDifferenceDivisors (Finset.univ.image nodes) (nodes p.1 ^ k - nodes p.2 ^ k)).card)
    (Finset.mem_univ p)
  simpa only [if_neg hp] using h

/-- A nonzero frequency fiber is bounded by the actual finite divisor maximum. -/
theorem monomial_difference_frequency_fiber_le (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (nodes : α → R) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 2 ≤ k) (p : α × α)
    (hp : coord (nodes p.1 ^ k) - coord (nodes p.2 ^ k) ≠ 0) :
    (frequencyFiber (fun q : α × α => coord (nodes q.1 ^ k) - coord (nodes q.2 ^ k)) p).card ≤
      (k - 1) * nodeDivisorMaximum nodes k := by
  let a : R := nodes p.1 ^ k - nodes p.2 ^ k
  let S := Finset.univ.image nodes
  have ha : a ≠ 0 := by
    intro hz
    apply hp
    rw [← map_sub]
    change coord a = 0
    rw [hz, map_zero]
  have hmap : (frequencyFiber
      (fun q : α × α => coord (nodes q.1 ^ k) - coord (nodes q.2 ^ k)) p).card ≤
      (powerDifferenceFiber S k a).card := by
    apply Finset.card_le_card_of_injOn (fun q : α × α => (nodes q.1, nodes q.2))
    · intro q hq
      have heq := (Finset.mem_filter.mp hq).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨q.1, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨q.2, Finset.mem_univ _, rfl⟩
      · apply hcoord
        simpa only [a, map_sub] using heq.symm
    · intro q hq t ht hqt
      exact Prod.ext (hnodes (congrArg Prod.fst hqt)) (hnodes (congrArg Prod.snd hqt))
  exact hmap.trans ((powerDifference_fiber_card_le_divisors S k hk ha).trans
    (Nat.mul_le_mul_left _ (nodeDivisorMaximum_bounds nodes k p ha)))

/-- Literal equal-difference energy bound, including the large zero fiber. -/
theorem monomial_difference_energy_le (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (nodes : α → R) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 2 ≤ k) :
    frequencyEnergy (fun p : α × α => coord (nodes p.1 ^ k) - coord (nodes p.2 ^ k)) ≤
      (k * Fintype.card α)^2 +
        ((k - 1) * nodeDivisorMaximum nodes k) * (Fintype.card α)^2 := by
  let v := fun a => coord (nodes a ^ k)
  have hz : zeroFrequencyCount (fun p : α × α => v p.1 - v p.2) ≤ k * Fintype.card α := by
    rw [zeroFrequencyCount_difference]
    apply frequencyEnergy_le_mul_card _ k
    intro a
    have h := indexed_power_fiber_card_le nodes hnodes k (by omega) (nodes a ^ k)
    simpa only [frequencyFiber, v, hcoord.eq_iff, eq_comm] using h
  have he := frequencyEnergy_le_zero_sq_add (fun p : α × α => v p.1 - v p.2)
    ((k - 1) * nodeDivisorMaximum nodes k)
    (fun p hp => monomial_difference_frequency_fiber_le coord hcoord nodes hnodes k hk p hp)
  have hsq := Nat.pow_le_pow_left hz 2
  have hcard : Fintype.card (α × α) = (Fintype.card α)^2 := by simp [pow_two]
  rw [hcard] at he
  exact he.trans (Nat.add_le_add_right hsq _)

/-- A fully proved fourth-moment inequality in terms of the finite divisor parameter. -/
theorem monomial_fourth_moment_le (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (nodes : α → R) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 2 ≤ k) (w : α → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖finiteWeylSum coord k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
      ((k : ℝ)^2 + (k - 1 : ℕ) * (nodeDivisorMaximum nodes k : ℝ)) *
        (Fintype.card α : ℝ)^2 * W^4 := by
  have he := monomial_difference_energy_le coord hcoord nodes hnodes k hk
  have heR : (frequencyEnergy
      (fun p : α × α => coord (nodes p.1 ^ k) - coord (nodes p.2 ^ k)) : ℝ) ≤
      ((k : ℝ)^2 + (k - 1 : ℕ) * (nodeDivisorMaximum nodes k : ℝ)) *
        (Fintype.card α : ℝ)^2 := by
    have hcast := Nat.cast_le (α := ℝ).mpr he
    push_cast at hcast
    nlinarith only [hcast]
  exact (integral_norm_frequencySum_fourth_le_energy
    (fun a => coord (nodes a ^ k)) w W hW hw).trans
    (mul_le_mul_of_nonneg_right heR (by positivity))

/-- Exact specialization to actual algebraic-integer Weyl sums. -/
theorem numberField_monomial_fourth_moment_le (K : Type*) [Field K] [NumberField K]
    {β : Type*} [Fintype β] (nodes : β → 𝓞 K) (hnodes : Function.Injective nodes)
    (k : ℕ) (hk : 2 ≤ k) (w : β → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖ ^ 4 ∂latticeHaar) ≤
      ((k : ℝ)^2 + (k - 1 : ℕ) * (nodeDivisorMaximum nodes k : ℝ)) *
        (Fintype.card β : ℝ)^2 * W^4 :=
  monomial_fourth_moment_le (integerCoordinates K) (integerCoordinates_injective K)
    nodes hnodes k hk w W hW hw

end WaringSiegel.WSL2

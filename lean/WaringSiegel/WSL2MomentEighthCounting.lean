import WaringSiegel.WSL2MomentEighthReduction
import WaringSiegel.WSL2MomentHuaCounting
import WaringSiegel.WSL2Collision

/-!
# Arithmetic fiber bounds for the eighth-moment collision count

The change of variables from two correlation base points to their difference
is injective, and every surviving tuple is an actual double polynomial
difference. The large zero fiber is kept separate.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

theorem finite_collision_card_real_le {α β R : Type*} [Zero R]
    (A : Finset α) (B : Finset β) (f : α → R) (g : β → R) (Z M : ℝ)
    (hM : 0 ≤ M) (hz : ((B.filter (fun b => g b = 0)).card : ℝ) ≤ Z)
    (hnz : ∀ a ∈ A, f a ≠ 0 → ((B.filter (fun b => g b = f a)).card : ℝ) ≤ M) :
    (((A.product B).filter (fun p => f p.1 = g p.2)).card : ℝ) ≤
      ((A.filter (fun a => f a = 0)).card : ℝ) * Z + (A.card : ℝ) * M := by
  rw [finite_collision_card_eq_sum, Nat.cast_sum]
  calc
    (∑ a ∈ A, ((B.filter (fun b => g b = f a)).card : ℝ)) ≤
        ∑ a ∈ A, ((if f a = 0 then Z else 0) + M) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : f a = 0
      · rw [h, if_pos rfl]
        linarith
      · rw [if_neg h, zero_add]
        exact hnz a ha h
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]

variable {R ι : Type*} [CommRing R] [IsDomain R] [CharZero R] [Fintype ι]

def fourthPowerValue (k : ℕ) (q : (R × R) × (R × R)) : R :=
  (q.1.1 ^ k - q.1.2 ^ k) - (q.2.1 ^ k - q.2.2 ^ k)

def correlationPowerValue (k : ℕ) (q : Σ _ : R, R × R) : R :=
  ((q.2.2 + q.1)^k - q.2.2^k) - ((q.2.1 + q.1)^k - q.2.1^k)

theorem fourthFrequency_power_eq (coord : R →+ (ι → ℤ)) (k : ℕ)
    (q : (R × R) × (R × R)) :
    fourthFrequency (fun x => coord (x^k)) q = coord (fourthPowerValue k q) := by
  simp only [fourthFrequency, fourthPowerValue, map_sub]

theorem correlationFrequency_power_eq (coord : R →+ (ι → ℤ)) (k : ℕ)
    (q : Σ _ : R, R × R) :
    correlationFrequency (fun x => coord (x^k)) q = coord (correlationPowerValue k q) := by
  simp only [correlationFrequency, correlationPowerValue, map_sub]

theorem correlation_power_fiber_card_le_double (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (k : ℕ) (a : R) :
    ((correlationPairs S H).filter (fun q => correlationPowerValue k q = a)).card ≤
      (doubleDifferenceFiber S H k a).card := by
  apply Finset.card_le_card_of_injOn
    (fun q : Σ _ : R, R × R => (q.2.2 - q.2.1, (q.1, q.2.1)))
  · intro q hq
    obtain ⟨hqmem, hqeq⟩ := Finset.mem_filter.mp hq
    obtain ⟨hh, hxy⟩ := Finset.mem_sigma.mp hqmem
    obtain ⟨hxO, hyO⟩ := Finset.mem_product.mp hxy
    have hx := (Finset.mem_filter.mp hxO).1
    have hy := (Finset.mem_filter.mp hyO).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨hH _ hy _ hx, Finset.mem_product.mpr ⟨hh, hx⟩⟩, ?_⟩
    have hxy : q.2.1 + (q.2.2 - q.2.1) = q.2.2 := by abel
    simpa only [polynomialDifference_eval, eval_pow, eval_X, hxy, correlationPowerValue] using hqeq
  · intro q hq r hr heq
    have hj : q.2.2 - q.2.1 = r.2.2 - r.2.1 := congrArg Prod.fst heq
    have hh : q.1 = r.1 := congrArg (fun t : R × (R × R) => t.2.1) heq
    have hx : q.2.1 = r.2.1 := congrArg (fun t : R × (R × R) => t.2.2) heq
    have hy : q.2.2 = r.2.2 := by rw [hx] at hj; exact sub_left_injective hj
    exact Sigma.ext hh (heq_of_eq (Prod.ext hx hy))

theorem correlation_power_zero_fiber_le (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (k : ℕ) (hk : 3 ≤ k) :
    ((correlationPairs S H).filter (fun q => correlationPowerValue k q = 0)).card ≤
      2 * H.card * S.card + (k-2)*H.card^2 :=
  (correlation_power_fiber_card_le_double S H hH k 0).trans
    (doubleDifference_zero_fiber_card_le S H k hk)

theorem correlation_power_nonzero_fiber_le (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (k : ℕ) (hk : 3 ≤ k)
    {a : R} (ha : a ≠ 0) :
    ((correlationPairs S H).filter (fun q => correlationPowerValue k q = a)).card ≤
      (k-2)*(H.filter (fun h => h ≠ 0 ∧ h ∣ a)).card^2 :=
  (correlation_power_fiber_card_le_double S H hH k a).trans
    (doubleDifference_fiber_card_le_divisors S H k hk ha)

theorem integral_fourth_power_eq_zero_count (S : Finset R)
    (coord : R →+ (ι → ℤ)) (hcoord : Function.Injective coord) (k : ℕ) :
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x^k)) θ‖^4 ∂latticeHaar) =
      ((((S.product S).product (S.product S)).filter (fun q => fourthPowerValue k q = 0)).card : ℝ) := by
  calc
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x^k)) θ‖^4 ∂latticeHaar) =
        (∫ θ, ((‖finiteFrequencySum S (fun x => coord (x^k)) θ‖^4 : ℝ) : ℂ)
          ∂latticeHaar).re := by rw [integral_complex_ofReal]; rfl
    _ = _ := by
      simp_rw [finiteFrequencySum_norm_fourth_expansion]
      rw [integral_finiteFrequencySum]
      simp only [fourthFrequency_power_eq, ← map_zero coord, hcoord.eq_iff, Complex.natCast_re]

/-- The zero-case induction input and nonzero ring divisors are now the only
finite parameters in the actual eighth moment. -/
theorem integral_eighth_le_fourth_and_divisors (S H : Finset R)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H)
    (coord : R →+ (ι → ℤ)) (hcoord : Function.Injective coord)
    (k : ℕ) (hk : 3 ≤ k) (D : ℝ)
    (hD : ∀ q ∈ (S.product S).product (S.product S), fourthPowerValue k q ≠ 0 →
      ((H.filter (fun h => h ≠ 0 ∧ h ∣ fourthPowerValue k q)).card : ℝ) ≤ D) :
    (∫ θ, ‖finiteFrequencySum S (fun x => coord (x^k)) θ‖^8 ∂latticeHaar) ≤
      (H.card : ℝ) *
        ((∫ θ, ‖finiteFrequencySum S (fun x => coord (x^k)) θ‖^4 ∂latticeHaar) *
          (2*(H.card : ℝ)*S.card + (k-2 : ℕ)*(H.card : ℝ)^2) +
          (S.card : ℝ)^4 * (k-2 : ℕ) * D^2) := by
  have hzero : (((correlationPairs S H).filter (fun q => correlationPowerValue k q = 0)).card : ℝ) ≤
      2*(H.card : ℝ)*S.card + (k-2 : ℕ)*(H.card : ℝ)^2 := by
    exact_mod_cast correlation_power_zero_fiber_le S H hH k hk
  have hnz (q) (hq : q ∈ (S.product S).product (S.product S)) (hne : fourthPowerValue k q ≠ 0) :
      (((correlationPairs S H).filter (fun b => correlationPowerValue k b = fourthPowerValue k q)).card : ℝ) ≤
        (k-2 : ℕ)*D^2 := by
    have h := correlation_power_nonzero_fiber_le S H hH k hk hne
    have hc : (((correlationPairs S H).filter (fun b => correlationPowerValue k b = fourthPowerValue k q)).card : ℝ) ≤
        (k-2 : ℕ)*(((H.filter (fun h => h ≠ 0 ∧ h ∣ fourthPowerValue k q)).card : ℝ)^2) := by
      exact_mod_cast h
    exact hc.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hD q hq hne) _) (by positivity))
  have hc := finite_collision_card_real_le ((S.product S).product (S.product S))
    (correlationPairs S H) (fourthPowerValue k) (correlationPowerValue k)
    (2*(H.card : ℝ)*S.card + (k-2 : ℕ)*(H.card : ℝ)^2)
    ((k-2 : ℕ)*D^2) (by positivity) hzero hnz
  rw [← integral_fourth_power_eq_zero_count S coord hcoord k] at hc
  have hcard : (((S.product S).product (S.product S)).card : ℝ) = (S.card : ℝ)^4 := by
    simp only [Finset.product_eq_sprod, Finset.card_product, Nat.cast_mul]
    ring
  rw [hcard] at hc
  have ha := integral_eighth_le_collision_count S H hH (fun x => coord (x^k))
  simp only [fourthFrequency_power_eq, correlationFrequency_power_eq, hcoord.eq_iff] at ha
  exact ha.trans (by
    have hmul := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ H.card by positivity)
    convert hmul using 1 <;> ring)

end WaringSiegel.WSL2

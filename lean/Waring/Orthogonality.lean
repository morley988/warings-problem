import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact Fourier orthogonality for finite representation problems

These lemmas use mathlib's additive-circle characters and normalized Haar measure.
They identify finite character integrals with exact counts of frequency equations.
No asymptotic estimate or Waring bound is assumed here.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Waring

variable {T : ℝ} [Fact (0 < T)]

/-- A nonconstant integer-frequency character has mean zero; the constant has mean one. -/
theorem integral_fourier_character (n : ℤ) :
    (∫ x : AddCircle T, fourier n x ∂AddCircle.haarAddCircle) =
      if n = 0 then (1 : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hn (Fact.out : 0 < T))

/-- Character functions are integrable on the compact additive circle. -/
theorem integrable_fourier_character (n : ℤ) :
    Integrable (fun x : AddCircle T => fourier n x) AddCircle.haarAddCircle := by
  exact (fourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrating a finite character sum counts exactly its zero frequencies. -/
theorem integral_finite_frequency_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) :
    (∫ x : AddCircle T, ∑ i ∈ s, fourier (a i) x ∂AddCircle.haarAddCircle) =
      ((s.filter fun i => a i = 0).card : ℂ) := by
  classical
  rw [integral_finset_sum s (fun i _ => integrable_fourier_character (a i))]
  simp only [integral_fourier_character]
  simp

/-- Twisting a finite character sum by frequency `-n` extracts the coefficient of `n`. -/
theorem integral_finite_frequency_coefficient {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (n : ℤ) :
    (∫ x : AddCircle T,
      (∑ i ∈ s, fourier (a i) x) * fourier (-n) x ∂AddCircle.haarAddCircle) =
      ((s.filter fun i => a i = n).card : ℂ) := by
  classical
  simp_rw [Finset.sum_mul, ← fourier_add]
  rw [integral_finite_frequency_sum]
  simp only [← sub_eq_add_neg, sub_eq_zero]

omit [Fact (0 < T)] in
/-- The product of finitely many characters has frequency equal to their summed frequencies. -/
theorem prod_fourier_character {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (x : AddCircle T) :
    (∏ i ∈ s, fourier (a i) x) = fourier (∑ i ∈ s, a i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, fourier_add]

omit [Fact (0 < T)] in
/-- Expanding a product of finite character sums enumerates all finite choices. -/
theorem prod_sum_fourier_character {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (a : ∀ i, κ i → ℤ)
    (x : AddCircle T) :
    (∏ i, ∑ j, fourier (a i j) x) =
      ∑ f : ∀ i, κ i, fourier (∑ i, a i (f i)) x := by
  classical
  rw [Fintype.prod_sum]
  congr 1
  ext f
  exact prod_fourier_character Finset.univ (fun i => a i (f i)) x

/-- The circle integral of a product of finite sums is an exact representation count. -/
theorem integral_product_frequency_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (a : ∀ i, κ i → ℤ) (n : ℤ) :
    (∫ x : AddCircle T,
      (∏ i, ∑ j, fourier (a i j) x) * fourier (-n) x ∂AddCircle.haarAddCircle) =
      ((Finset.univ.filter fun f : ∀ i, κ i => ∑ i, a i (f i) = n).card : ℂ) := by
  classical
  simp_rw [prod_sum_fourier_character a]
  exact integral_finite_frequency_coefficient (T := T) (ι := ∀ i, κ i)
    Finset.univ (fun f : ∀ i, κ i => ∑ i, a i (f i)) n

/-- A power of one finite exponential sum counts ordered tuples with the given total frequency. -/
theorem integral_power_frequency_coefficient {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (s : ℕ) (n : ℤ) :
    (∫ x : AddCircle T,
      (∑ j, fourier (a j) x) ^ s * fourier (-n) x ∂AddCircle.haarAddCircle) =
      ((Finset.univ.filter fun f : Fin s → κ => ∑ i, a (f i) = n).card : ℂ) := by
  classical
  simpa using integral_product_frequency_coefficient
    (T := T) (ι := Fin s) (κ := fun _ => κ) (fun _ j => a j) n

/-- Normalized Haar integration is ordinary integration over one period, with its length factor. -/
theorem haar_integral_eq_interval_integral (f : AddCircle T → ℂ) (a : ℝ) :
    (∫ x : AddCircle T, f x ∂AddCircle.haarAddCircle) =
      (1 / T) • ∫ x in a..a + T, f (x : AddCircle T) := by
  simpa [fourierCoeff] using fourierCoeff_eq_intervalIntegral f 0 a

/-- On a period of length one, the finite-frequency coefficient integral is the exact count. -/
theorem interval_integral_finite_frequency_coefficient {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑ i ∈ s, fourier (a i) (x : AddCircle (1 : ℝ))) *
        fourier (-n) (x : AddCircle (1 : ℝ))) =
      ((s.filter fun i => a i = n).card : ℂ) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have h := haar_integral_eq_interval_integral (T := 1)
    (fun x => (∑ i ∈ s, fourier (a i) x) * fourier (-n) x) 0
  simp only [one_div_one, zero_add, one_smul] at h
  rw [← h]
  exact integral_finite_frequency_coefficient s a n

/-- Ordinary circle-method integrals of powers of finite sums count finite tuples. -/
theorem interval_integral_power_frequency_coefficient {κ : Type*} [Fintype κ]
    (a : κ → ℤ) (s : ℕ) (n : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑ j, fourier (a j) (x : AddCircle (1 : ℝ))) ^ s *
        fourier (-n) (x : AddCircle (1 : ℝ))) =
      ((Finset.univ.filter fun f : Fin s → κ => ∑ i, a (f i) = n).card : ℂ) := by
  letI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have h := haar_integral_eq_interval_integral (T := 1)
    (fun x => (∑ j, fourier (a j) x) ^ s * fourier (-n) x) 0
  simp only [one_div_one, zero_add, one_smul] at h
  rw [← h]
  exact integral_power_frequency_coefficient a s n

/-- Distinct integer frequencies have exactly their cardinality as their second moment. -/
theorem interval_integral_sq_norm_frequency_sum {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (ha : Function.Injective a) :
    (∫ x in (0 : ℝ)..1,
      ‖∑ i ∈ s, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ 2) = (s.card : ℝ) := by
  classical
  let F : ℝ → ℂ := fun x => ∑ i ∈ s, fourier (a i) (x : AddCircle (1 : ℝ))
  have hcont : Continuous F :=
    continuous_finset_sum s (fun i _ =>
      (fourier (a i)).continuous.comp (AddCircle.continuous_mk' 1))
  have hi (j : ι) : IntervalIntegrable
      (fun x : ℝ => F x * fourier (-a j) (x : AddCircle (1 : ℝ))) volume 0 1 :=
    (hcont.mul ((fourier (-a j)).continuous.comp
      (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  have hfilt (j : ι) (hj : j ∈ s) : (s.filter fun i => a i = a j) = {j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact ha h.2
    · intro h
      subst i
      exact ⟨hj, rfl⟩
  have hconj (x : ℝ) : conj (F x) =
      ∑ j ∈ s, fourier (-a j) (x : AddCircle (1 : ℝ)) := by
    change conj (∑ j ∈ s, fourier (a j) (x : AddCircle (1 : ℝ))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    exact fourier_neg.symm
  have hcomplex : (∫ x in (0 : ℝ)..1, F x * conj (F x)) = (s.card : ℂ) := by
    calc
      (∫ x in (0 : ℝ)..1, F x * conj (F x)) =
          ∫ x in (0 : ℝ)..1,
            ∑ j ∈ s, F x * fourier (-a j) (x : AddCircle (1 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro x _hx
        change F x * conj (F x) =
          ∑ j ∈ s, F x * fourier (-a j) (x : AddCircle (1 : ℝ))
        rw [hconj x, Finset.mul_sum]
      _ = ∑ j ∈ s, ∫ x in (0 : ℝ)..1,
            F x * fourier (-a j) (x : AddCircle (1 : ℝ)) :=
        intervalIntegral.integral_finset_sum (fun j _ => hi j)
      _ = ∑ j ∈ s, ((s.filter fun i => a i = a j).card : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact interval_integral_finite_frequency_coefficient s a (a j)
      _ = ∑ _j ∈ s, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hfilt j hj]
        simp
      _ = (s.card : ℂ) := by simp
  have hnorm : ∀ x : ℝ, ((‖F x‖ ^ 2 : ℝ) : ℂ) = F x * conj (F x) := by
    intro x
    simpa using (Complex.mul_conj' (F x)).symm
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  change (∫ x in (0 : ℝ)..1, ((‖F x‖ ^ 2 : ℝ) : ℂ)) = (s.card : ℂ)
  simp_rw [hnorm]
  exact hcomplex

end Waring

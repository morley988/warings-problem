import Waring.EvenMoments

/-!
# Mixed even moments and legitimate subsum comparisons

An integral of a product of even powers is a nonnegative integer solution
count. Enlarging either variable set gives an inclusion of solution sets.
Injective changes of variables allow frequency-preserving substitutions
before this inclusion is used.
-/

noncomputable section

open scoped BigOperators

namespace Waring

/-- The mixed even moment of two finite exponential sums. -/
def mixedFrequencyEvenMoment {ι κ : Type*} (A : Finset ι) (a : ι → ℤ) (p : ℕ)
    (B : Finset κ) (b : κ → ℤ) (q : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ (2 * p) *
      ‖∑ j ∈ B, fourier (b j) (x : AddCircle (1 : ℝ))‖ ^ (2 * q)

/-- The expanded choices for one side of a mixed equal-sum equation. -/
def mixedTuples {ι κ : Type*} (A : Finset ι) (p : ℕ) (B : Finset κ) (q : ℕ) :
    Finset ((Fin p → ι) × (Fin q → κ)) :=
  finiteTuples A p ×ˢ finiteTuples B q

/-- Total frequency for one mixed tuple. -/
def mixedFrequency {ι κ : Type*} (a : ι → ℤ) (b : κ → ℤ) {p q : ℕ}
    (f : (Fin p → ι) × (Fin q → κ)) : ℤ :=
  (∑ i, a (f.1 i)) + ∑ j, b (f.2 j)

/-- The exact equal-sum pairs of mixed tuples. -/
def mixedEqualSumPairs {ι κ : Type*} (A : Finset ι) (a : ι → ℤ) (p : ℕ)
    (B : Finset κ) (b : κ → ℤ) (q : ℕ) :=
  ((mixedTuples A p B q) ×ˢ (mixedTuples A p B q)).filter
    (fun f => mixedFrequency a b f.1 = mixedFrequency a b f.2)

/-- Expanding the two powers enumerates mixed tuples and adds their frequencies. -/
theorem product_sum_powers_fourier {ι κ : Type*} (A : Finset ι) (a : ι → ℤ) (p : ℕ)
    (B : Finset κ) (b : κ → ℤ) (q : ℕ) {T : ℝ} (x : AddCircle T) :
    (∑ i ∈ A, fourier (a i) x) ^ p * (∑ j ∈ B, fourier (b j) x) ^ q =
      ∑ f ∈ mixedTuples A p B q, fourier (mixedFrequency a b f) x := by
  rw [sum_pow_fourier, sum_pow_fourier, Finset.sum_mul]
  simp_rw [Finset.mul_sum, ← fourier_add]
  rw [mixedTuples, Finset.sum_product]
  rfl

/-- A mixed even moment is the second moment of its expanded finite frequency family. -/
theorem mixedFrequencyEvenMoment_eq_frequency {ι κ : Type*}
    (A : Finset ι) (a : ι → ℤ) (p : ℕ) (B : Finset κ) (b : κ → ℤ) (q : ℕ) :
    mixedFrequencyEvenMoment A a p B b q =
      frequencyEvenMoment (mixedTuples A p B q) (mixedFrequency a b) 1 := by
  unfold mixedFrequencyEvenMoment frequencyEvenMoment
  apply intervalIntegral.integral_congr
  intro x _hx
  change
    ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ (2 * p) *
      ‖∑ j ∈ B, fourier (b j) (x : AddCircle (1 : ℝ))‖ ^ (2 * q) =
        ‖∑ f ∈ mixedTuples A p B q,
          fourier (mixedFrequency a b f) (x : AddCircle (1 : ℝ))‖ ^ (2 * 1)
  rw [← product_sum_powers_fourier, norm_mul, norm_pow, norm_pow, mul_pow]
  simp only [mul_one, ← pow_mul, Nat.mul_comm p 2, Nat.mul_comm q 2]

/-- The mixed moment is exactly the count of equal-sum mixed tuple pairs. -/
theorem mixedFrequencyEvenMoment_eq_card {ι κ : Type*}
    (A : Finset ι) (a : ι → ℤ) (p : ℕ) (B : Finset κ) (b : κ → ℤ) (q : ℕ) :
    mixedFrequencyEvenMoment A a p B b q =
      ((mixedEqualSumPairs A a p B b q).card : ℝ) := by
  unfold mixedFrequencyEvenMoment
  have hpoint (x : ℝ) :
    ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ (2 * p) *
      ‖∑ j ∈ B, fourier (b j) (x : AddCircle (1 : ℝ))‖ ^ (2 * q) =
        ‖∑ f ∈ mixedTuples A p B q,
          fourier (mixedFrequency a b f) (x : AddCircle (1 : ℝ))‖ ^ 2 := by
    rw [← product_sum_powers_fourier, norm_mul, norm_pow, norm_pow, mul_pow]
    simp only [← pow_mul, Nat.mul_comm p 2, Nat.mul_comm q 2]
  simp_rw [hpoint]
  exact interval_integral_sq_norm_eq_collision_count _ _

/-- Componentwise inclusion of the two summation sets includes all mixed tuples. -/
theorem mixedTuples_mono {ι κ : Type*} {A C : Finset ι} {B D : Finset κ}
    (hAC : A ⊆ C) (hBD : B ⊆ D) (p q : ℕ) :
    mixedTuples A p B q ⊆ mixedTuples C p D q :=
  Finset.product_subset_product (finiteTuples_mono hAC p) (finiteTuples_mono hBD q)

/-- Componentwise inclusion gives mixed even-moment monotonicity through finite counts. -/
theorem mixedFrequencyEvenMoment_mono {ι κ : Type*} {A C : Finset ι} {B D : Finset κ}
    (hAC : A ⊆ C) (hBD : B ⊆ D) (a : ι → ℤ) (p : ℕ) (b : κ → ℤ) (q : ℕ) :
    mixedFrequencyEvenMoment A a p B b q ≤ mixedFrequencyEvenMoment C a p D b q := by
  rw [mixedFrequencyEvenMoment_eq_frequency, mixedFrequencyEvenMoment_eq_frequency]
  exact frequencyEvenMoment_mono (mixedTuples_mono hAC hBD p q) _ 1

/-- An injective substitution preserves a finite sum and hence its mixed moment. -/
theorem mixedFrequencyEvenMoment_image_left {ι κ ν : Type*} [DecidableEq κ]
    (A : Finset ι) (f : ι → κ) (hf : Function.Injective f) (b : κ → ℤ) (p : ℕ)
    (C : Finset ν) (c : ν → ℤ) (q : ℕ) :
    mixedFrequencyEvenMoment (A.image f) b p C c q =
      mixedFrequencyEvenMoment A (fun i => b (f i)) p C c q := by
  classical
  unfold mixedFrequencyEvenMoment
  have hsum (x : ℝ) :
      (∑ j ∈ A.image f, fourier (b j) (x : AddCircle (1 : ℝ))) =
        ∑ i ∈ A, fourier (b (f i)) (x : AddCircle (1 : ℝ)) :=
    Finset.sum_image (fun i _ j _ hij => hf hij)
  simp_rw [hsum]

/-- Splitting the exponent of one sum gives the corresponding two-block mixed moment. -/
theorem frequencyEvenMoment_eq_mixed {ι : Type*} (A : Finset ι) (a : ι → ℤ) (p q : ℕ) :
    frequencyEvenMoment A a (p + q) = mixedFrequencyEvenMoment A a p A a q := by
  unfold frequencyEvenMoment mixedFrequencyEvenMoment
  simp only [Nat.mul_add, pow_add]

/-- Replacing one block through an injective frequency-preserving embedding is valid after
integration. No comparison of pointwise absolute values is used. -/
theorem pure_evenMoment_le_mixed_of_embedding {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (B : Finset κ) (f : ι → κ) (hf : Function.Injective f)
    (b : κ → ℤ) (hAB : A.image f ⊆ B) (p q : ℕ) :
    frequencyEvenMoment A (fun i => b (f i)) (p + q) ≤
      mixedFrequencyEvenMoment B b p A (fun i => b (f i)) q := by
  rw [frequencyEvenMoment_eq_mixed]
  rw [← mixedFrequencyEvenMoment_image_left A f hf b p A (fun i => b (f i)) q]
  exact mixedFrequencyEvenMoment_mono hAB (Finset.Subset.refl _) b p _ q

end Waring

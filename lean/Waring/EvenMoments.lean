import Waring.SmoothSeeds
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod

/-!
# Even moments are exact equal-sum counts

The monotonicity proved here is an integral/counting statement. It does not
assert the false pointwise comparison between absolute values of a subsum and
the corresponding full exponential sum.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Waring

/-- All length-`r` ordered tuples with entries in a finite set. -/
def finiteTuples {ι : Type*} (A : Finset ι) (r : ℕ) : Finset (Fin r → ι) :=
  Fintype.piFinset (fun _ : Fin r => A)

/-- Pairs of tuples whose integer frequencies have equal total sums. -/
def equalSumPairs {ι : Type*} (A : Finset ι) (a : ι → ℤ) (r : ℕ) :
    Finset ((Fin r → ι) × (Fin r → ι)) :=
  ((finiteTuples A r) ×ˢ (finiteTuples A r)).filter
    (fun p => ∑ i, a (p.1 i) = ∑ i, a (p.2 i))

/-- A generic even integral moment on one period. -/
def frequencyEvenMoment {ι : Type*} (A : Finset ι) (a : ι → ℤ) (r : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ (2 * r)

/-- Expanding a finite power enumerates the tuple frequencies exactly. -/
theorem sum_pow_fourier {ι : Type*} (A : Finset ι) (a : ι → ℤ) (r : ℕ)
    {T : ℝ} (x : AddCircle T) :
    (∑ i ∈ A, fourier (a i) x) ^ r =
      ∑ f ∈ finiteTuples A r, fourier (∑ i, a (f i)) x := by
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro f _hf
  exact prod_fourier_character Finset.univ (fun i => a (f i)) x

/-- With repeated frequencies allowed, the second moment counts all frequency collisions. -/
theorem interval_integral_sq_norm_eq_collision_count {ι : Type*} (A : Finset ι)
    (a : ι → ℤ) :
    (∫ x in (0 : ℝ)..1,
      ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ 2) =
      (((A ×ˢ A).filter fun p => a p.1 = a p.2).card : ℝ) := by
  classical
  have hconj (x : ℝ) :
      conj (∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))) =
        ∑ j ∈ A, fourier (-a j) (x : AddCircle (1 : ℝ)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    exact fourier_neg.symm
  have hpoint (x : ℝ) :
      ((‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ A ×ˢ A, fourier (a p.1 - a p.2) (x : AddCircle (1 : ℝ)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    rw [hconj x, Finset.sum_mul]
    simp_rw [Finset.mul_sum, ← fourier_add]
    rw [Finset.sum_product]
    rfl
  have h := interval_integral_finite_frequency_coefficient
    (A ×ˢ A) (fun p => a p.1 - a p.2) 0
  simp only [neg_zero, fourier_zero, mul_one, sub_eq_zero] at h
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hpoint]
  exact h

/-- Every even finite exponential-sum moment is an exact count of equal-sum tuple pairs. -/
theorem frequencyEvenMoment_eq_card {ι : Type*} (A : Finset ι) (a : ι → ℤ) (r : ℕ) :
    frequencyEvenMoment A a r = ((equalSumPairs A a r).card : ℝ) := by
  unfold frequencyEvenMoment equalSumPairs
  have hpoint (x : ℝ) :
      ‖∑ i ∈ A, fourier (a i) (x : AddCircle (1 : ℝ))‖ ^ (2 * r) =
        ‖∑ f ∈ finiteTuples A r,
          fourier (∑ i, a (f i)) (x : AddCircle (1 : ℝ))‖ ^ 2 := by
    rw [← sum_pow_fourier, norm_pow, ← pow_mul, Nat.mul_comm r 2]
  simp_rw [hpoint]
  exact interval_integral_sq_norm_eq_collision_count (finiteTuples A r)
    (fun f => ∑ i, a (f i))

/-- Enlarging the summation set enlarges its tuple set. -/
theorem finiteTuples_mono {ι : Type*} {A B : Finset ι} (hAB : A ⊆ B) (r : ℕ) :
    finiteTuples A r ⊆ finiteTuples B r :=
  Fintype.piFinset_subset _ _ (fun _ => hAB)

/-- The equal-sum solutions for a subset are literally a subset of those for the larger set. -/
theorem equalSumPairs_mono {ι : Type*} {A B : Finset ι} (hAB : A ⊆ B)
    (a : ι → ℤ) (r : ℕ) : equalSumPairs A a r ⊆ equalSumPairs B a r := by
  exact Finset.filter_subset_filter _
    (Finset.product_subset_product (finiteTuples_mono hAB r) (finiteTuples_mono hAB r))

/-- Even moments are monotone under inclusion of summation sets, by the exact count identity. -/
theorem frequencyEvenMoment_mono {ι : Type*} {A B : Finset ι} (hAB : A ⊆ B)
    (a : ι → ℤ) (r : ℕ) : frequencyEvenMoment A a r ≤ frequencyEvenMoment B a r := by
  rw [frequencyEvenMoment_eq_card, frequencyEvenMoment_eq_card]
  exact_mod_cast Finset.card_le_card (equalSumPairs_mono hAB a r)

namespace SmoothMoments

/-- The actual smooth moment is the generic finite-frequency moment. -/
theorem smoothMoment_even_eq_frequency (k r : ℕ) (P R : ℝ) :
    smoothMoment k (2 * r) P R =
      frequencyEvenMoment (smoothNumbers P R) (fun n => ((n ^ k : ℕ) : ℤ)) r := by
  unfold smoothMoment smoothWeyl frequencyEvenMoment
  simp_rw [phase_eq_fourier]

/-- Exact equal-sum representation count for every even smooth moment. -/
theorem smoothMoment_even_eq_card (k r : ℕ) (P R : ℝ) :
    smoothMoment k (2 * r) P R =
      ((equalSumPairs (smoothNumbers P R) (fun n => ((n ^ k : ℕ) : ℤ)) r).card : ℝ) := by
  rw [smoothMoment_even_eq_frequency, frequencyEvenMoment_eq_card]

/-- Smoothness inclusion gives even-moment monotonicity without a pointwise subsum claim. -/
theorem smoothMoment_even_mono_cutoff (k r : ℕ) (P : ℝ) {R S : ℝ} (hRS : R ≤ S) :
    smoothMoment k (2 * r) P R ≤ smoothMoment k (2 * r) P S := by
  rw [smoothMoment_even_eq_frequency, smoothMoment_even_eq_frequency]
  exact frequencyEvenMoment_mono (smoothNumbers_mono_cutoff hRS) _ r

/-- Increasing the length cutoff includes the smaller smooth-number set. -/
theorem smoothNumbers_mono_length {P Q R : ℝ} (hPQ : P ≤ Q) :
    smoothNumbers P R ⊆ smoothNumbers Q R := by
  intro n hn
  rcases mem_smoothNumbers.mp hn with ⟨⟨hnpos, hnP⟩, hs⟩
  exact mem_smoothNumbers.mpr ⟨⟨hnpos, hnP.trans (Nat.floor_mono hPQ)⟩, hs⟩

/-- Increasing the length cutoff increases each even smooth moment. -/
theorem smoothMoment_even_mono_length (k r : ℕ) {P Q : ℝ} (hPQ : P ≤ Q) (R : ℝ) :
    smoothMoment k (2 * r) P R ≤ smoothMoment k (2 * r) Q R := by
  rw [smoothMoment_even_eq_frequency, smoothMoment_even_eq_frequency]
  exact frequencyEvenMoment_mono (smoothNumbers_mono_length hPQ) _ r

end SmoothMoments
end Waring

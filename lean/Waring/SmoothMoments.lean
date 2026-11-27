import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Smooth Weyl sums and genuinely quantified admissible exponents

This file defines the actual finite exponential sums and their real moments.
`AdmissibleExponent k p lam` is the uniform analytic assertion for the full
exponent lam, not a free predicate standing for a numerical certificate.

The elementary closure theorems here do not assert that the improved table
entries are admissible. That connection remains an explicit open task.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Waring.SmoothMoments

/-- Every prime factor of `n` is at most the real smoothness cutoff `R`. -/
def IsSmooth (n : ℕ) (R : ℝ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ n → (q : ℝ) ≤ R

/-- Positive `R`-smooth naturals of size at most `P`. -/
def smoothNumbers (P R : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 ⌊P⌋₊).filter (fun n => IsSmooth n R)

@[simp] theorem mem_smoothNumbers {n : ℕ} {P R : ℝ} :
    n ∈ smoothNumbers P R ↔ (1 ≤ n ∧ n ≤ ⌊P⌋₊) ∧ IsSmooth n R := by
  classical
  simp [smoothNumbers]

theorem smoothNumbers_mono_cutoff {P R S : ℝ} (hRS : R ≤ S) :
    smoothNumbers P R ⊆ smoothNumbers P S := by
  intro n hn
  rcases mem_smoothNumbers.mp hn with ⟨hb, hs⟩
  exact mem_smoothNumbers.mpr ⟨hb, fun q hq hd => (hs q hq hd).trans hRS⟩

/-- The phase `e(alpha n^k)` with the standard `2 pi i` normalization. -/
def phase (k n : ℕ) (α : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * α * (n : ℝ) ^ k : ℝ) : ℂ) * Complex.I)

/-- The pure smooth degree-`k` Weyl sum. -/
def smoothWeyl (k : ℕ) (P R α : ℝ) : ℂ :=
  ∑ n ∈ smoothNumbers P R, phase k n α

/-- Full integral moment order `p` on one period. -/
def smoothMoment (k p : ℕ) (P R : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖smoothWeyl k P R α‖ ^ p

theorem continuous_phase (k n : ℕ) : Continuous (phase k n) := by
  unfold phase
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_id).mul continuous_const)).mul continuous_const)

theorem continuous_smoothWeyl (k : ℕ) (P R : ℝ) :
    Continuous (smoothWeyl k P R) := by
  unfold smoothWeyl
  exact continuous_finset_sum _ (fun n _ => continuous_phase k n)

theorem smoothMoment_integrable (k p : ℕ) (P R : ℝ) :
    IntervalIntegrable (fun α => ‖smoothWeyl k P R α‖ ^ p) volume 0 1 :=
  ((continuous_smoothWeyl k P R).norm.pow p).intervalIntegrable 0 1

theorem smoothMoment_nonneg (k p : ℕ) (P R : ℝ) :
    0 ≤ smoothMoment k p P R := by
  unfold smoothMoment
  exact intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun α => pow_nonneg (norm_nonneg _) _)

@[simp] theorem norm_phase (k n : ℕ) (α : ℝ) : ‖phase k n α‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  have hz : (((2 * Real.pi * α * (n : ℝ) ^ k : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_self]
  rw [hz, Real.exp_zero]

theorem norm_smoothWeyl_le_card (k : ℕ) (P R α : ℝ) :
    ‖smoothWeyl k P R α‖ ≤ (smoothNumbers P R).card := by
  unfold smoothWeyl
  calc
    ‖∑ n ∈ smoothNumbers P R, phase k n α‖ ≤
        ∑ n ∈ smoothNumbers P R, ‖phase k n α‖ := norm_sum_le _ _
    _ = (smoothNumbers P R).card := by simp

theorem smoothNumbers_card_le (P R : ℝ) :
    (smoothNumbers P R).card ≤ ⌊P⌋₊ := by
  classical
  calc
    (smoothNumbers P R).card ≤ (Finset.Icc 1 ⌊P⌋₊).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = ⌊P⌋₊ := by simp

theorem norm_smoothWeyl_le (k : ℕ) {P : ℝ} (R α : ℝ) (hP : 0 ≤ P) :
    ‖smoothWeyl k P R α‖ ≤ P := by
  calc
    ‖smoothWeyl k P R α‖ ≤ (smoothNumbers P R).card := norm_smoothWeyl_le_card _ _ _ _
    _ ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le P R
    _ ≤ P := Nat.floor_le hP

/-- The elementary moment bound, before any number theoretic improvement. -/
theorem smoothMoment_le_trivial (k p : ℕ) {P : ℝ} (R : ℝ) (hP : 0 ≤ P) :
    smoothMoment k p P R ≤ P ^ p := by
  have hpoint : ∀ α : ℝ, ‖smoothWeyl k P R α‖ ^ p ≤ P ^ p :=
    fun α => pow_le_pow_left₀ (norm_nonneg _) (norm_smoothWeyl_le k R α hP) p
  calc
    smoothMoment k p P R ≤ ∫ _α in (0 : ℝ)..1, P ^ p :=
      intervalIntegral.integral_mono zero_le_one (smoothMoment_integrable k p P R)
        intervalIntegrable_const hpoint
    _ = P ^ p := by simp

/-- Uniform smooth moment bound with a full exponent `lam`.

For each epsilon, the same constants work for all sufficiently large P and
all real cutoffs `1 ≤ R ≤ P^η`. In particular this retains the finite common
smoothness requirement needed by the iterative proof.
-/
def AdmissibleExponent (k p : ℕ) (lam : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P ^ η →
        smoothMoment k p P R ≤ C * P ^ (lam + ε)

/-- The corresponding excess notation in the manuscript. -/
def AdmissibleExcess (k p : ℕ) (Δ : ℝ) : Prop :=
  AdmissibleExponent k p ((p : ℝ) - k + Δ)

/-- Upward rounding of an admissible full exponent is safe. -/
theorem admissibleExponent_mono {k p : ℕ} {lam mu : ℝ}
    (h : AdmissibleExponent k p lam) (hlammu : lam ≤ mu) :
    AdmissibleExponent k p mu := by
  intro ε hε
  rcases h ε hε with ⟨η, hη, C, hC, P₀, hP₀, hbound⟩
  refine ⟨η, hη, C, hC, P₀, hP₀, ?_⟩
  intro P hP R hR hRP
  exact (hbound P hP R hR hRP).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hP₀.trans hP) (add_le_add_right hlammu ε)) hC.le)

/-- Upward rounding is safe also in excess notation. -/
theorem admissibleExcess_mono {k p : ℕ} {Δ Ε : ℝ}
    (h : AdmissibleExcess k p Δ) (hΔΕ : Δ ≤ Ε) :
    AdmissibleExcess k p Ε :=
  admissibleExponent_mono h (add_le_add_left hΔΕ _)

/-- A nonvacuous base case: the trivial full exponent is admissible. -/
theorem admissibleExponent_trivial (k p : ℕ) : AdmissibleExponent k p p := by
  intro ε hε
  refine ⟨1, zero_lt_one, 1, zero_lt_one, 1, le_rfl, ?_⟩
  intro P hP R _hR _hRP
  calc
    smoothMoment k p P R ≤ P ^ p := smoothMoment_le_trivial k p R (zero_le_one.trans hP)
    _ = P ^ (p : ℝ) := (Real.rpow_natCast P p).symm
    _ ≤ 1 * P ^ ((p : ℝ) + ε) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hP (le_add_of_nonneg_right hε.le)

/-- Two admissible estimates can share smoothness, constant and length cutoff.
Iterating this theorem gives the finite common-choice step; it asserts no
uniform smoothness for an infinite sequence of updates.
-/
theorem admissibleExponent_pair {k p q : ℕ} {lam mu : ℝ}
    (h₁ : AdmissibleExponent k p lam) (h₂ : AdmissibleExponent k q mu)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P ^ η →
        smoothMoment k p P R ≤ C * P ^ (lam + ε) ∧
        smoothMoment k q P R ≤ C * P ^ (mu + ε) := by
  rcases h₁ ε hε with ⟨η₁, hη₁, C₁, hC₁, P₁, hP₁, hb₁⟩
  rcases h₂ ε hε with ⟨η₂, hη₂, C₂, hC₂, P₂, hP₂, hb₂⟩
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, max C₁ C₂,
    hC₁.trans_le (le_max_left _ _), max P₁ P₂,
    hP₁.trans (le_max_left _ _), ?_⟩
  intro P hP R hR hRP
  have hP1 : P₁ ≤ P := (le_max_left _ _).trans hP
  have hP2 : P₂ ≤ P := (le_max_right _ _).trans hP
  have hPone : 1 ≤ P := hP₁.trans hP1
  have hR1 : R ≤ P ^ η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hPone (min_le_left _ _))
  have hR2 : R ≤ P ^ η₂ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hPone (min_le_right _ _))
  constructor
  · exact (hb₁ P hP1 R hR hR1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (zero_le_one.trans hPone) _))
  · exact (hb₂ P hP2 R hR hR2).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (zero_le_one.trans hPone) _))


/-- A whole finite collection of admissible moments shares one positive
smoothness parameter, one constant and one lower length cutoff. -/
theorem admissibleExponent_finset {ι : Type*} (s : Finset ι)
    (degree order : ι → ℕ) (exponent : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∀ i ∈ s, AdmissibleExponent (degree i) (order i) (exponent i)) →
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P ^ η →
        ∀ i ∈ s, smoothMoment (degree i) (order i) P R ≤
          C * P ^ (exponent i + ε) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _h
      refine ⟨1, zero_lt_one, 1, zero_lt_one, 1, le_rfl, ?_⟩
      intro P _hP R _hR _hRP i hi
      exact False.elim (Finset.notMem_empty i hi)
  | @insert i s _hi ih =>
      intro h
      have hs : ∀ a ∈ s, AdmissibleExponent (degree a) (order a) (exponent a) :=
        fun a ha => h a (Finset.mem_insert_of_mem ha)
      rcases ih hs with ⟨η₁, hη₁, C₁, hC₁, P₁, hP₁, hb₁⟩
      rcases h i (Finset.mem_insert_self i s) ε hε with
        ⟨η₂, hη₂, C₂, hC₂, P₂, hP₂, hb₂⟩
      refine ⟨min η₁ η₂, lt_min hη₁ hη₂, max C₁ C₂,
        hC₁.trans_le (le_max_left _ _), max P₁ P₂,
        hP₁.trans (le_max_left _ _), ?_⟩
      intro P hP R hR hRP a ha
      have hP1 : P₁ ≤ P := (le_max_left _ _).trans hP
      have hP2 : P₂ ≤ P := (le_max_right _ _).trans hP
      have hPone : 1 ≤ P := hP₁.trans hP1
      have hR1 : R ≤ P ^ η₁ := hRP.trans
        (Real.rpow_le_rpow_of_exponent_le hPone (min_le_left _ _))
      have hR2 : R ≤ P ^ η₂ := hRP.trans
        (Real.rpow_le_rpow_of_exponent_le hPone (min_le_right _ _))
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (hb₂ P hP2 R hR hR2).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg (zero_le_one.trans hPone) _))
      · exact (hb₁ P hP1 R hR hR1 a ha).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg (zero_le_one.trans hPone) _))

/-- An admissible estimate may be used at any fixed positive power of the
ambient length. The smoothness exponent is shrunk accordingly, and the
arbitrarily small loss is measured relative to the ambient length. -/
theorem admissibleExponent_rescale {k p : ℕ} {lam a : ℝ}
    (h : AdmissibleExponent k p lam) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P ^ η →
        smoothMoment k p (P ^ a) R ≤ C * P ^ (a * lam + ε) := by
  rcases h (ε / a) (div_pos hε ha) with ⟨η, hη, C, hC, P₁, hP₁, hb⟩
  refine ⟨a * η, mul_pos ha hη, C, hC, max 1 (P₁ ^ a⁻¹), le_max_left _ _, ?_⟩
  intro P hP R hR hRP
  have hPone : 1 ≤ P := (le_max_left _ _).trans hP
  have hPnonneg : 0 ≤ P := zero_le_one.trans hPone
  have hP₁nonneg : 0 ≤ P₁ := zero_le_one.trans hP₁
  have hlength : P₁ ≤ P ^ a := by
    calc
      P₁ = (P₁ ^ a⁻¹) ^ a := (Real.rpow_inv_rpow hP₁nonneg ha.ne').symm
      _ ≤ P ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hP₁nonneg _)
        ((le_max_right _ _).trans hP) ha.le
  have hRscale : R ≤ (P ^ a) ^ η := by
    rw [← Real.rpow_mul hPnonneg]
    exact hRP
  have hexponent : a * (lam + ε / a) = a * lam + ε := by
    rw [mul_add, mul_div_cancel₀ ε ha.ne']
  calc
    smoothMoment k p (P ^ a) R ≤ C * (P ^ a) ^ (lam + ε / a) :=
      hb (P ^ a) hlength R hR hRscale
    _ = C * P ^ (a * lam + ε) := by
      rw [← Real.rpow_mul hPnonneg, hexponent]

#print axioms admissibleExponent_mono
#print axioms admissibleExponent_trivial
#print axioms admissibleExponent_pair
#print axioms admissibleExponent_finset
#print axioms admissibleExponent_rescale

end Waring.SmoothMoments

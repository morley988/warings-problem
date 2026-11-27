import Waring.SeedCompletionBackwardMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# One Cauchy step over the complete next-stage auxiliary sum

The next-stage variables retain their old-parameter and extracted-factor
labels. Their counts are summed before Cauchy is applied. This yields the
literal complete auxiliary moment, without a factor for the number of
labels. In particular the theorem applies to labels `(oldParameters,w)`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Waring.SeedCompletionBackwardAggregate
open SeedCompletionBackward SeedCompletionBackwardCount
open SeedCompletionBackwardMoments IntegerDifferencePolynomial

/-- Tagging the first family preserves exactly the sum of the cross counts. -/
theorem crossFrequencyPairs_sigma_card {κ ι ν γ : Type*}
    (C : Finset κ) (A : κ → Finset ι) (B : Finset ν)
    (f : κ → ι → γ) (g : ν → γ) :
    (crossFrequencyPairs (C.sigma A) B (fun x => f x.1 x.2) g).card =
      ∑ c ∈ C, (crossFrequencyPairs (A c) B (f c) g).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_equiv (Equiv.sigmaProdDistrib (fun _ : κ => ι) ν)
  intro x
  simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product,
    Finset.mem_sigma,Equiv.sigmaProdDistrib_apply]
  tauto

/-- All literal next-stage centers and heights, retaining the original label. -/
def aggregateNextDomain {κ : Type*} (C : Finset κ) (w : κ → ℤ) (P : ℤ) (k : ℕ) :
    Finset (Σ _ : κ, ℤ × ℤ) :=
  C.sigma (fun c => nextParameterDomain (w c) P k)

def aggregateNextPhase {κ : Type*} (k : ℕ) (params : κ → List (ℤ × ℤ))
    (w : κ → ℤ) (p : Σ _ : κ, ℤ × ℤ) : ℤ :=
  nextIntegerPhase k (params p.1) (w p.1) p.2

/-- The complete next auxiliary moment, with every label inside the square. -/
def aggregateNextMoment {κ ι : Type*} (k : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (w : κ → ℤ) (P : ℤ)
    (B : Finset ι) (U : ι → ℤ) : ℝ :=
  secondMoment (aggregateNextDomain C w P k ×ˢ B)
    (fun p => aggregateNextPhase k params w p.1 + (2 : ℤ)^k*U p.2)

/-- The global cross count is exactly the sum of the old-parameter/factor
next counts. The correspondence is a bijection, not a cardinality estimate. -/
theorem sum_nextStepSolutions_card_eq_cross {κ ι : Type*} (k : ℕ) (C : Finset κ)
    (params : κ → List (ℤ × ℤ)) (w : κ → ℤ) (P : ℤ) (B : Finset ι) (U : ι → ℤ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) (hw : ∀ c ∈ C, w c ≠ 0) :
    (∑ c ∈ C, (nextStepSolutions k (realParameters (params c)) (w c) P B
      (fun u => (U u : ℝ))).card) =
      (crossFrequencyPairs (aggregateNextDomain C w P k ×ˢ B) B
        (fun p => aggregateNextPhase k params w p.1 + (2 : ℤ)^k*U p.2)
        (fun u => (2 : ℤ)^k*U u)).card := by
  classical
  have heq : (crossFrequencyPairs (aggregateNextDomain C w P k ×ˢ B) B
      (fun p => aggregateNextPhase k params w p.1 + (2 : ℤ)^k*U p.2)
      (fun u => (2 : ℤ)^k*U u)).card =
      (crossFrequencyPairs
        (C.sigma (fun c => nextParameterDomain (w c) P k ×ˢ B)) B
        (fun p => nextIntegerPhase k (params p.1) (w p.1) p.2.1 + (2 : ℤ)^k*U p.2.2)
        (fun u => (2 : ℤ)^k*U u)).card := by
    apply Finset.card_equiv
      (Equiv.prodCongr (Equiv.sigmaProdDistrib (fun _ : κ => ℤ × ℤ) ι) (Equiv.refl ι))
    intro p
    simp only [crossFrequencyPairs,aggregateNextDomain,aggregateNextPhase,
      Finset.mem_filter,Finset.mem_product,Finset.mem_sigma,
      Equiv.prodCongr_apply]
    tauto
  rw [heq, crossFrequencyPairs_sigma_card C
    (fun c => nextParameterDomain (w c) P k ×ˢ B) B
    (fun c p => nextIntegerPhase k (params c) (w c) p.1 + (2 : ℤ)^k*U p.2)
    (fun u => (2 : ℤ)^k*U u)]
  apply Finset.sum_congr rfl
  intro c hc
  exact nextStepSolutions_card_eq_integer_cross k (params c) (hm c hc) (w c) P
    (hw c hc) B U

/-- The integral has the entire next auxiliary exponential sum inside its
square, multiplied by the unchanged doubled-tuple square. -/
theorem aggregateNextMoment_eq_product_integral {κ ι : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (P : ℤ) (B : Finset ι) (U : ι → ℤ) :
    aggregateNextMoment k C params w P B U =
      ∫ α in (0 : ℝ)..1,
        ‖∑ p ∈ aggregateNextDomain C w P k,
          fourier (aggregateNextPhase k params w p) (α : AddCircle (1 : ℝ))‖^2 *
        ‖∑ u ∈ B, fourier ((2 : ℤ)^k*U u) (α : AddCircle (1 : ℝ))‖^2 := by
  unfold aggregateNextMoment secondMoment
  congr 1
  funext α
  have hs : (∑ p ∈ aggregateNextDomain C w P k ×ˢ B,
      fourier (aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2)
        (α : AddCircle (1 : ℝ))) =
      (∑ p ∈ aggregateNextDomain C w P k,
        fourier (aggregateNextPhase k params w p) (α : AddCircle (1 : ℝ))) *
      (∑ u ∈ B, fourier ((2 : ℤ)^k*U u) (α : AddCircle (1 : ℝ))) := by
    simp only [Finset.sum_product,fourier_add,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs,norm_mul,mul_pow]

/-- One finite Cauchy inequality after summing every old label. There is
no cardinality penalty for either old parameters or extracted factors. -/
theorem sum_next_step_count_le_sqrt_moments {κ ι : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (P : ℤ) (B : Finset ι) (U : ι → ℤ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) (hw : ∀ c ∈ C, w c ≠ 0) :
    (∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) P B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
        Real.sqrt (aggregateNextMoment k C params w P B U * secondMoment B U) := by
  have hcount : (∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) P B
      (fun u => (U u : ℝ))).card : ℝ)) =
      ((crossFrequencyPairs (aggregateNextDomain C w P k ×ˢ B) B
        (fun p => aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2)
        (fun u => (2 : ℤ)^k*U u)).card : ℝ) := by
    exact_mod_cast sum_nextStepSolutions_card_eq_cross k C params w P B U hm hw
  rw [hcount]
  have hc := crossFrequencyPairs_card_sq_le (aggregateNextDomain C w P k ×ˢ B) B
    (fun p => aggregateNextPhase k params w p.1+(2 : ℤ)^k*U p.2)
    (fun u => (2 : ℤ)^k*U u)
  rw [← secondMoment_eq_count,← secondMoment_eq_count,
    secondMoment_mul_frequency B U ((2 : ℤ)^k) (by positivity)] at hc
  apply (Real.le_sqrt (by positivity) (mul_nonneg
    (secondMoment_nonneg _ _) (secondMoment_nonneg _ _))).mpr
  exact hc

/-- The complete aggregated backward step. The diagonal retains only the
number of old central points, while the next term uses one global moment. -/
theorem sum_backward_count_le_moments {κ ι : Type*}
    (k : ℕ) (C : Finset κ) (params : κ → List (ℤ × ℤ)) (w : κ → ℤ)
    (P : ℤ) (Z : κ → Finset ℤ) (B : Finset ι) (U : ι → ℤ)
    (hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0) (hw : ∀ c ∈ C, 0 < w c)
    (hZ : ∀ c ∈ C, Z c ⊆ Finset.Icc 1 P) :
    (∑ c ∈ C, ((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
      (∑ c ∈ C, ((Z c).card : ℝ))*secondMoment B U +
        2*Real.sqrt (aggregateNextMoment k C params w P B U * secondMoment B U) := by
  have hsum : (∑ c ∈ C, ((stepSolutions k (realParameters (params c)) (w c) (Z c) B
      (fun u => (U u : ℝ))).card : ℝ)) ≤
      (∑ c ∈ C, ((Z c).card : ℝ))*secondMoment B U +
        2*∑ c ∈ C, ((nextStepSolutions k (realParameters (params c)) (w c) P B
          (fun u => (U u : ℝ))).card : ℝ) := by
    rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro c hc
    have h := step_card_le_tuple_diagonal_add_next k (realParameters (params c))
      (w c) P (Z c) B (fun u => (U u : ℝ)) (hw c hc) (hZ c hc)
    rw [crossFrequencyPairs_intCast] at h
    rw [secondMoment_eq_count]
    exact_mod_cast h
  exact hsum.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (sum_next_step_count_le_sqrt_moments k C params w P B U hm
      (fun c hc => (hw c hc).ne')) (by norm_num)) _)

#print axioms sum_nextStepSolutions_card_eq_cross
#print axioms sum_next_step_count_le_sqrt_moments
#print axioms sum_backward_count_le_moments

end Waring.SeedCompletionBackwardAggregate

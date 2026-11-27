import Waring.SeedCompletionBackwardCount
import Waring.IntegerDifferencePolynomial
import Waring.EvenMoments

/-!
# Backward differencing with the actual auxiliary integral

The finite count changes of variables now feed actual circle integrals.
The integer polynomial representation proves that each next-stage phase is
an integer frequency. Fourier orthogonality and finite Cauchy therefore
give the backward square-root estimate without an assumed moment estimate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Waring.SeedCompletionBackwardMoments
open Differences SeedCompletionBackward SeedCompletionBackwardCount
open IntegerDifferencePolynomial

/-- The literal complete second moment of an integer-frequency family. -/
def secondMoment {ι : Type*} (A : Finset ι) (f : ι → ℤ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖∑ x ∈ A, fourier (f x) (α : AddCircle (1 : ℝ))‖^2

theorem secondMoment_eq_count {ι : Type*} (A : Finset ι) (f : ι → ℤ) :
    secondMoment A f = ((crossFrequencyPairs A A f f).card : ℝ) := by
  unfold secondMoment
  rw [interval_integral_sq_norm_eq_collision_count]
  unfold crossFrequencyPairs
  congr

theorem secondMoment_nonneg {ι : Type*} (A : Finset ι) (f : ι → ℤ) :
    0 ≤ secondMoment A f := by
  rw [secondMoment_eq_count]
  positivity

theorem crossFrequencyPairs_intCast {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) :
    crossFrequencyPairs A B (fun x => (f x : ℝ)) (fun y => (g y : ℝ)) =
      crossFrequencyPairs A B f g := by
  classical
  ext p
  simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product,Int.cast_inj]

theorem secondMoment_mul_frequency {ι : Type*} (A : Finset ι) (f : ι → ℤ)
    (c : ℤ) (hc : c ≠ 0) : secondMoment A (fun x => c*f x) = secondMoment A f := by
  rw [secondMoment_eq_count,secondMoment_eq_count]
  apply congrArg (fun s : Finset (ι × ι) => (s.card : ℝ))
  ext p
  simp only [crossFrequencyPairs,Finset.mem_filter,Finset.mem_product]
  exact and_congr_right (fun _ => ⟨fun h => mul_left_cancel₀ hc h,
    fun h => congrArg (fun t => c*t) h⟩)

def doubleHeights (params : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  params.map (fun hm => (2*hm.1,hm.2))

theorem realParameters_doubleHeights (params : List (ℤ × ℤ)) :
    realParameters (doubleHeights params) = scaleHeights 2 (realParameters params) := by
  simp [doubleHeights,realParameters,scaleHeights,List.map_map]

/-- The exact next-stage integer frequency, with the new height first. -/
def nextIntegerPhase (k : ℕ) (params : List (ℤ × ℤ)) (w : ℤ) (p : ℤ × ℤ) : ℤ :=
  (powerPolynomial k ((p.2,w) :: doubleHeights params)).eval p.1

theorem nextPhase_eq_integer (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (w : ℤ) (hw : w ≠ 0) (p : ℤ × ℤ) :
    nextPhase k (realParameters params) w p = (nextIntegerPhase k params w p : ℝ) := by
  have hnew : ∀ q ∈ (p.2,w) :: doubleHeights params, q.2 ≠ 0 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hw
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
      exact hm r hr
  have h := powerPolynomial_eval_int k ((p.2,w) :: doubleHeights params) hnew p.1
  have hreal : realParameters ((p.2,w) :: doubleHeights params) =
      ((p.2 : ℝ),(w : ℝ)) :: scaleHeights 2 (realParameters params) := by
    change ((p.2 : ℝ),(w : ℝ)) :: realParameters (doubleHeights params) = _
    rw [realParameters_doubleHeights]
  rw [hreal] at h
  exact h.symm

/-- The next count is an exact integer-frequency cross count, because the
polynomial representation proves integrality at every actual center. -/
theorem nextStepSolutions_card_eq_integer_cross {ι : Type*} (k : ℕ)
    (params : List (ℤ × ℤ)) (hm : ∀ p ∈ params, p.2 ≠ 0)
    (w P : ℤ) (hw : w ≠ 0) (B : Finset ι) (U : ι → ℤ) :
    (nextStepSolutions k (realParameters params) w P B (fun u => (U u : ℝ))).card =
      (crossFrequencyPairs (nextParameterDomain w P k ×ˢ B) B
        (fun p => nextIntegerPhase k params w p.1 + (2 : ℤ)^k*U p.2)
        (fun u => (2 : ℤ)^k*U u)).card := by
  rw [nextStepSolutions_card_eq_cross]
  have hf : (fun p : (ℤ × ℤ) × ι => nextPhase k (realParameters params) w p.1 +
      (2 : ℝ)^k*(U p.2 : ℝ)) =
      (fun p => ((nextIntegerPhase k params w p.1 + (2 : ℤ)^k*U p.2 : ℤ) : ℝ)) := by
    funext p
    rw [nextPhase_eq_integer k params hm w hw]
    push_cast
    rfl
  have hg : (fun u => (2 : ℝ)^k*(U u : ℝ)) =
      (fun u => (((2 : ℤ)^k*U u : ℤ) : ℝ)) := by
    funext u
    push_cast
    rfl
  rw [hf,hg,crossFrequencyPairs_intCast]

/-- The next auxiliary moment on the literal enlarged domain. -/
def nextAuxiliaryMoment {ι : Type*} (k : ℕ) (params : List (ℤ × ℤ))
    (w P : ℤ) (B : Finset ι) (U : ι → ℤ) : ℝ :=
  secondMoment (nextParameterDomain w P k ×ˢ B)
    (fun p => nextIntegerPhase k params w p.1 + (2 : ℤ)^k*U p.2)

/-- This is the usual product of the auxiliary square and the doubled
smooth-tuple square, integrated on one complete period. -/
theorem nextAuxiliaryMoment_eq_product_integral {ι : Type*} (k : ℕ)
    (params : List (ℤ × ℤ)) (w P : ℤ) (B : Finset ι) (U : ι → ℤ) :
    nextAuxiliaryMoment k params w P B U =
      ∫ α in (0 : ℝ)..1,
        ‖∑ p ∈ nextParameterDomain w P k,
          fourier (nextIntegerPhase k params w p) (α : AddCircle (1 : ℝ))‖^2 *
        ‖∑ u ∈ B, fourier ((2 : ℤ)^k*U u) (α : AddCircle (1 : ℝ))‖^2 := by
  unfold nextAuxiliaryMoment secondMoment
  congr 1
  funext α
  have hs : (∑ p ∈ nextParameterDomain w P k ×ˢ B,
      fourier (nextIntegerPhase k params w p.1+(2 : ℤ)^k*U p.2)
        (α : AddCircle (1 : ℝ))) =
      (∑ p ∈ nextParameterDomain w P k,
        fourier (nextIntegerPhase k params w p) (α : AddCircle (1 : ℝ))) *
      (∑ u ∈ B, fourier ((2 : ℤ)^k*U u) (α : AddCircle (1 : ℝ))) := by
    simp only [Finset.sum_product,fourier_add,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  rw [hs,norm_mul,mul_pow]

/-- The source Schwarz step now involves the actual auxiliary integral,
with no epsilon loss and no assumed moment bound. -/
theorem next_step_count_le_sqrt_moments {ι : Type*} (k : ℕ)
    (params : List (ℤ × ℤ)) (hm : ∀ p ∈ params, p.2 ≠ 0)
    (w P : ℤ) (hw : w ≠ 0) (B : Finset ι) (U : ι → ℤ) :
    ((nextStepSolutions k (realParameters params) w P B (fun u => (U u : ℝ))).card : ℝ) ≤
      Real.sqrt (nextAuxiliaryMoment k params w P B U * secondMoment B U) := by
  rw [nextStepSolutions_card_eq_integer_cross k params hm w P hw]
  have hc := crossFrequencyPairs_card_sq_le (nextParameterDomain w P k ×ˢ B) B
    (fun p => nextIntegerPhase k params w p.1+(2 : ℤ)^k*U p.2)
    (fun u => (2 : ℤ)^k*U u)
  rw [← secondMoment_eq_count,← secondMoment_eq_count,
    secondMoment_mul_frequency B U ((2 : ℤ)^k) (by positivity)] at hc
  apply (Real.le_sqrt (by positivity) (mul_nonneg
    (secondMoment_nonneg _ _) (secondMoment_nonneg _ _))).mpr
  exact hc

/-- The complete actual backward step: the original congruent count is
bounded by its tuple diagonal and the geometric mean of the next auxiliary
moment and the original tuple moment. All source phases are literal. -/
theorem backward_count_le_moments {ι : Type*} (k : ℕ)
    (params : List (ℤ × ℤ)) (hm : ∀ p ∈ params, p.2 ≠ 0)
    (w P : ℤ) (Z : Finset ℤ) (B : Finset ι) (U : ι → ℤ)
    (hw : 0 < w) (hZ : Z ⊆ Finset.Icc 1 P) :
    ((stepSolutions k (realParameters params) w Z B (fun u => (U u : ℝ))).card : ℝ) ≤
      (Z.card : ℝ)*secondMoment B U +
        2*Real.sqrt (nextAuxiliaryMoment k params w P B U * secondMoment B U) := by
  have hc := step_card_le_tuple_diagonal_add_next k (realParameters params) w P Z B
    (fun u => (U u : ℝ)) hw hZ
  rw [crossFrequencyPairs_intCast] at hc
  have hR : ((stepSolutions k (realParameters params) w Z B (fun u => (U u : ℝ))).card : ℝ) ≤
      (Z.card : ℝ)*((crossFrequencyPairs B B U U).card : ℝ) +
        2*((nextStepSolutions k (realParameters params) w P B (fun u => (U u : ℝ))).card : ℝ) := by
    exact_mod_cast hc
  rw [← secondMoment_eq_count] at hR
  exact hR.trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (next_step_count_le_sqrt_moments k params hm w P hw.ne' B U) (by norm_num)) _)

#print axioms nextPhase_eq_integer
#print axioms next_step_count_le_sqrt_moments
#print axioms backward_count_le_moments

end Waring.SeedCompletionBackwardMoments

import Waring.MixedEvenMoments
import Waring.AuxiliaryL2Grouping
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Module.BigOperators

/-!
# Homogeneous block reduction for the actual finite counts

For s positive, AM--GM applied to the s squared absolute values gives
`prod_i |f_i|^2 <= (1/s) sum_i |f_i|^(2s)`. Multiplication by the squared
polynomial sum and exact Fourier orthogonality turn this into a bound for
the genuine heterogeneous collision count. Summing coefficient tuples then
gives the factor `(number of coefficients)^(s-1)` exactly.

Together with finite Cauchy over coefficient tuples, this is the same
`(number of coefficients)^(2s-1)` homogeneous reduction as the two Holder
applications in the good branch of the fundamental efficient-differencing
lemma. Subsum comparisons are used only after integration, through actual
solution-set inclusion.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Waring.PolicyCompletionHolder
open AuxiliaryL2Grouping

def frequencySum {α : Type*} (A : Finset α) (f : α → ℤ) (x : ℝ) : ℂ :=
  ∑ a ∈ A, fourier (f a) (x : AddCircle (1 : ℝ))

theorem continuous_frequencySum {α : Type*} (A : Finset α) (f : α → ℤ) :
    Continuous (frequencySum A f) :=
  continuous_finset_sum A (fun a _ =>
    (fourier (f a)).continuous.comp (AddCircle.continuous_mk' 1))

/-- The equally weighted finite AM--GM inequality, with natural powers. -/
theorem prod_le_average_pow {s : ℕ} (hs : 0 < s) (v : Fin s → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (∏ i, v i) ≤ (s : ℝ)⁻¹ * ∑ i, (v i)^s := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin s => (s : ℝ)⁻¹) (fun i => (v i)^s)
    (fun _ _ => by positivity)
    (by simp [hs0]) (fun i _ => pow_nonneg (hv i) _)
  have hpow (i : Fin s) : ((v i)^s)^((s : ℝ)⁻¹)=v i := by
    rw [← Real.rpow_natCast_mul (hv i),mul_inv_cancel₀ hs0,Real.rpow_one]
  simpa only [hpow,← Finset.mul_sum] using hm

def tupleFrequency {α β : Type*} {s : ℕ} (f : α → ℤ) (g : Fin s → β → ℤ)
    (x : α × (Fin s → β)) : ℤ := f x.1+∑ i, g i (x.2 i)

def tupleCollision {α β : Type*} (s : ℕ) (A : Finset α) (B : Finset β)
    (f : α → ℤ) (g : Fin s → β → ℤ) :=
  collisionPairs (A ×ˢ finiteTuples B s) (tupleFrequency f g)

theorem frequencySum_tuple {α β : Type*} (s : ℕ) (A : Finset α) (B : Finset β)
    (f : α → ℤ) (g : Fin s → β → ℤ) (x : ℝ) :
    frequencySum (A ×ˢ finiteTuples B s) (tupleFrequency f g) x =
      frequencySum A f x * ∏ i, frequencySum B (g i) x := by
  classical
  unfold frequencySum
  rw [Finset.prod_univ_sum]
  simp only [Finset.sum_mul,Finset.mul_sum]
  simp_rw [prod_fourier_character]
  simp only [← fourier_add]
  rw [Finset.sum_product]
  exact Finset.sum_comm

/-- Exact orthogonality for the heterogeneous tuple family. -/
theorem tupleCollision_eq_integral {α β : Type*} (s : ℕ) (A : Finset α) (B : Finset β)
    (f : α → ℤ) (g : Fin s → β → ℤ) :
    ((tupleCollision s A B f g).card : ℝ) =
      ∫ x in (0 : ℝ)..1, ‖frequencySum A f x‖^2 *
        ∏ i, ‖frequencySum B (g i) x‖^2 := by
  have heq (x : ℝ) :
      ‖frequencySum (A ×ˢ finiteTuples B s) (tupleFrequency f g) x‖^2 =
        ‖frequencySum A f x‖^2 * ∏ i, ‖frequencySum B (g i) x‖^2 := by
    rw [frequencySum_tuple,norm_mul,norm_prod,mul_pow,Finset.prod_pow]
  simp_rw [← heq]
  exact (interval_integral_sq_norm_eq_collision_count _ _).symm

/-- A homogeneous mixed moment with one polynomial variable is exactly
the corresponding tuple collision count, without length-one tuple wrappers. -/
theorem mixedMoment_one_eq_tupleCollision {α β : Type*} (s : ℕ)
    (A : Finset α) (B : Finset β) (f : α → ℤ) (g : β → ℤ) :
    mixedFrequencyEvenMoment A f 1 B g s =
      ((tupleCollision s A B f (fun _ => g)).card : ℝ) := by
  rw [tupleCollision_eq_integral]
  simp only [mixedFrequencyEvenMoment,frequencySum,mul_one,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← pow_mul]

/-- An actual heterogeneous solution count is at most the arithmetic mean
of the homogeneous mixed moments on the same polynomial domain. -/
theorem tupleCollision_le_average {α β : Type*} {s : ℕ} (hs : 0 < s)
    (A : Finset α) (B : Finset β) (f : α → ℤ) (g : Fin s → β → ℤ) :
    ((tupleCollision s A B f g).card : ℝ) ≤
      (s : ℝ)⁻¹ * ∑ i, mixedFrequencyEvenMoment A f 1 B (g i) s := by
  have hF := (continuous_frequencySum A f).norm.pow 2
  have hG (i : Fin s) := (continuous_frequencySum B (g i)).norm.pow (2*s)
  have hleft := hF.mul (continuous_finset_prod Finset.univ
    (fun i _ => (continuous_frequencySum B (g i)).norm.pow 2))
  have hright : Continuous (fun x : ℝ => (s : ℝ)⁻¹ *
      ∑ i, (‖frequencySum A f x‖^2 * ‖frequencySum B (g i) x‖^(2*s))) :=
    continuous_const.mul (continuous_finset_sum Finset.univ
      (fun i _ => hF.mul (hG i)))
  rw [tupleCollision_eq_integral]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1,
        (s : ℝ)⁻¹ * ∑ i, (‖frequencySum A f x‖^2 * ‖frequencySum B (g i) x‖^(2*s)) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hleft.intervalIntegrable 0 1) (hright.intervalIntegrable 0 1)
      intro x hx
      have hprod := prod_le_average_pow hs (fun i => ‖frequencySum B (g i) x‖^2)
        (fun i => sq_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hprod (sq_nonneg ‖frequencySum A f x‖)
      simpa only [← pow_mul,Finset.mul_sum,mul_assoc,mul_left_comm] using hmul
    _ = (s : ℝ)⁻¹ * ∑ i, mixedFrequencyEvenMoment A f 1 B (g i) s := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finset_sum (fun i _ => (hF.mul (hG i)).intervalIntegrable 0 1)]
      simp only [mixedFrequencyEvenMoment,frequencySum,mul_one]

/-- Exact counting of the occurrences of each coefficient in all ordered
coefficient tuples. -/
theorem sum_tuple_average {γ : Type*} (W : Finset γ) {s : ℕ} (hs : 0 < s)
    (H : γ → ℝ) :
    (∑ w ∈ finiteTuples W s, (s : ℝ)⁻¹ * ∑ i, H (w i)) =
      (W.card : ℝ)^(s-1) * ∑ w ∈ W, H w := by
  classical
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp only [finiteTuples,Fintype.sum_piFinset_apply,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_pow,Finset.sum_const,Finset.card_univ]
  field_simp

/-- Summing heterogeneous counts over all coefficient tuples costs exactly
`#W^(s-1)`. Enlarging the polynomial domains is justified by finite counts. -/
theorem sum_tupleCollision_le_homogeneous {α β γ : Type*} {s : ℕ} (hs : 0 < s)
    (W : Finset γ) (A : (Fin s → γ) → Finset α) (Agood : γ → Finset α)
    (B : Finset β) (f : α → ℤ) (g : γ → β → ℤ)
    (hsub : ∀ w ∈ finiteTuples W s, ∀ i, A w ⊆ Agood (w i)) :
    (∑ w ∈ finiteTuples W s,
      ((tupleCollision s (A w) B f (fun i => g (w i))).card : ℝ)) ≤
      (W.card : ℝ)^(s-1) * ∑ w ∈ W, mixedFrequencyEvenMoment (Agood w) f 1 B (g w) s := by
  calc
    _ ≤ ∑ w ∈ finiteTuples W s,
        (s : ℝ)⁻¹ * ∑ i, mixedFrequencyEvenMoment (Agood (w i)) f 1 B (g (w i)) s := by
      apply Finset.sum_le_sum
      intro w hw
      apply (tupleCollision_le_average hs (A w) B f (fun i => g (w i))).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact mixedFrequencyEvenMoment_mono (B := B) (D := B)
        (hsub w hw i) (Finset.Subset.refl B) f 1 (g (w i)) s
    _ = _ := sum_tuple_average W (s := s) hs
      (fun w => mixedFrequencyEvenMoment (Agood w) f 1 B (g w) s)

#print axioms tupleCollision_le_average
#print axioms sum_tupleCollision_le_homogeneous

end Waring.PolicyCompletionHolder

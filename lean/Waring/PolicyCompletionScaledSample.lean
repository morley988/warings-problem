import Waring.PolicyCompletionScaledBounds
import Waring.PolicyCompletionBasicSource
import Waring.PolicyCompletionShallowSource

/-! A fixed dilation of the integer sampling ranges can be put inside an
arbitrarily small exponent enlargement. The loss is proved for the actual
nonnegative finite moment and its actual normalizing denominator. -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionScaledSample
open NormalizedCoefficient CartesianFloorScales PolicyCompletionBasicRanges
open RationalHeight

theorem normalized_sample_mono_cutoffs {P : ℝ} (hP : 0 < P)
    (A : Finset ℕ) (d r : ℕ) (phi α : ℝ) (σ : ℕ → ℝ)
    {H J H' J' : ℕ} (hH : 0 < H) (hJ : 0 < J)
    (hHH : H ≤ H') (hJJ : J ≤ J') :
    normalizedSampledCoefficient A d r P phi H J α σ ≤
      ((H' : ℝ)*J'/((H : ℝ)*J))*
        normalizedSampledCoefficient A d r P phi H' J' α σ := by
  have hHp : 0 < H' := hH.trans_le hHH
  have hJp : 0 < J' := hJ.trans_le hJJ
  have hnum :
      (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
        ‖CoefficientPower.coefficientWeyl A d (α*(h : ℝ)^3*((j : ℝ)+σ h))‖^(2*r)) ≤
      ∑ h ∈ Finset.Icc 1 H', ∑ j ∈ Finset.range J',
        ‖CoefficientPower.coefficientWeyl A d (α*(h : ℝ)^3*((j : ℝ)+σ h))‖^(2*r) := by
    calc
      _ ≤ ∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J',
          ‖CoefficientPower.coefficientWeyl A d (α*(h : ℝ)^3*((j : ℝ)+σ h))‖^(2*r) := by
        apply Finset.sum_le_sum
        intro h hh
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJJ)
          (by intros; positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc (le_refl 1) hHH) (by intros; positivity)
  unfold normalizedSampledCoefficient
  calc
    _ ≤ _ / ((H : ℝ)*J*P^((2*r : ℕ)*phi)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by
      have hH0 : (H : ℝ) ≠ 0 := by positivity
      have hJ0 : (J : ℝ) ≠ 0 := by positivity
      have hH'0 : (H' : ℝ) ≠ 0 := by positivity
      have hJ'0 : (J' : ℝ) ≠ 0 := by positivity
      have hM0 : P^((2*r : ℕ)*phi) ≠ 0 := (Real.rpow_pos_of_pos hP _).ne'
      field_simp

theorem fixed_dilation_sample_le {P CH CJ h j δ : ℝ}
    (hP : 1 ≤ P) (hCH : 1 ≤ CH) (hCJ : 1 ≤ CJ)
    (hh : 0 < h) (hj : 0 ≤ j) (hδ : 0 ≤ δ)
    (hCHsmall : CH ≤ P^δ) (hCJsmall : CJ ≤ P^δ)
    (hHpow : 2 ≤ P^h)
    (A : Finset ℕ) (d r : ℕ) (phi α : ℝ) (σ : ℕ → ℝ) :
    normalizedSampledCoefficient A d r P phi ⌊CH*P^h⌋₊ ⌈CJ*P^j⌉₊ α σ ≤
      (4*P^(2*δ))*normalizedSampledCoefficient A d r P phi
        (sourceH P (h+δ)) (sourceJ P (j+δ)) α σ := by
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hPh : 0 < P^h := Real.rpow_pos_of_pos hPp _
  have hPj : 0 < P^j := Real.rpow_pos_of_pos hPp _
  have hCHp : 0 < CH := zero_lt_one.trans_le hCH
  have hCJp : 0 < CJ := zero_lt_one.trans_le hCJ
  have hHbase : 2 ≤ CH*P^h := hHpow.trans (le_mul_of_one_le_left hPh.le hCH)
  have hH : 0 < ⌊CH*P^h⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hJ : 0 < ⌈CJ*P^j⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hHH : ⌊CH*P^h⌋₊ ≤ sourceH P (h+δ) := by
    apply Nat.floor_mono
    calc
      _ ≤ P^δ*P^h := mul_le_mul_of_nonneg_right hCHsmall hPh.le
      _ = _ := by rw [← Real.rpow_add hPp]; congr 1; ring
  have hJJ : ⌈CJ*P^j⌉₊ ≤ sourceJ P (j+δ) := by
    apply Nat.ceil_mono
    calc
      _ ≤ P^δ*P^j := mul_le_mul_of_nonneg_right hCJsmall hPj.le
      _ = _ := by rw [← Real.rpow_add hPp]; congr 1; ring
  have hHlo : P^h ≤ 2*(⌊CH*P^h⌋₊ : ℝ) := by
    have hf := half_le_floor hHbase
    have hl := le_mul_of_one_le_left hPh.le hCH
    linarith
  have hJlo : P^j ≤ (⌈CJ*P^j⌉₊ : ℝ) :=
    (le_mul_of_one_le_left hPj.le hCJ).trans (Nat.le_ceil _)
  have hHup : (sourceH P (h+δ) : ℝ) ≤ P^(h+δ) := Nat.floor_le
    (Real.rpow_nonneg hPp.le _)
  have hJup : (sourceJ P (j+δ) : ℝ) ≤ 2*P^(j+δ) := ceil_le_twice
    (Real.one_le_rpow hP (by linarith))
  have hratio : ((sourceH P (h+δ) : ℝ)*sourceJ P (j+δ))/
      ((⌊CH*P^h⌋₊ : ℝ)*⌈CJ*P^j⌉₊) ≤ 4*P^(2*δ) := by
    apply (div_le_iff₀ (by positivity : 0 < (⌊CH*P^h⌋₊ : ℝ)*⌈CJ*P^j⌉₊)).mpr
    calc
      _ ≤ P^(h+δ)*(2*P^(j+δ)) := by gcongr
      _ = 2*P^(2*δ)*(P^h*P^j) := by
        rw [Real.rpow_add hPp,Real.rpow_add hPp]
        rw [show 2*δ=δ+δ by ring,Real.rpow_add hPp]
        ring
      _ ≤ 2*P^(2*δ)*((2*(⌊CH*P^h⌋₊ : ℝ))*(⌈CJ*P^j⌉₊ : ℝ)) := by gcongr
      _ = _ := by ring
  have hn := normalized_sample_mono_cutoffs hPp A d r phi α σ hH hJ hHH hJJ
  apply hn.trans
  exact mul_le_mul_of_nonneg_right hratio (by
    unfold normalizedSampledCoefficient
    positivity)

#print axioms fixed_dilation_sample_le
end Waring.PolicyCompletionScaledSample

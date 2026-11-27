import Waring.SeedCompletionNaturalCross
import Waring.SeedCompletionSourceCount

/-! # Exact full-box mixed moments and the Cauchy split -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open CartesianProductSampling PolicyCompletionHolder PolicyCompletionSourceMajor
open EndgameCompletion SmoothMoments PolicyCompletionFundamental PolicyCompletionGoodBranch
open SeedCompletionCrossCauchy

def naturalCenters (L : ℝ) : Finset ℤ := Finset.Icc 1 (⌊L⌋₊:ℤ)

def boxMixedMoment {j : ℕ} (k s : ℕ) (L P R : ℝ) (M : Fin j → ℝ) (Y : ℝ) : ℝ :=
  ∫ α in (0:ℝ)..1,‖boxSourceFamily k L P R M α‖^2*‖smoothWeyl k Y R α‖^(2*s)

theorem boxMixedMoment_nonneg {j : ℕ} (k s : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (Y : ℝ) : 0≤boxMixedMoment k s L P R M Y := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro α hα
  positivity

theorem sum_int_naturalCenters (f : ℤ → ℂ) (L : ℝ) :
    (∑ z∈naturalCenters L,f z)=∑ n∈ordinaryNumbers L,f (n:ℤ) := by
  symm
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
  · intro n hn m hm heq
    exact_mod_cast heq
  · intro z hz
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hz
    exact ⟨z.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Int.toNat_of_nonneg (by omega)⟩
  · intro n hn
    rfl

theorem natural_auxiliary_frequency {j : ℕ} (k : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (α : ℝ) :
    frequencySum (naturalBoxLabels k L P R M ×ˢ naturalCenters L)
      (polynomialValue (fun c => powerPolynomial k (naturalParameters c.1 c.2))) α=
      boxSourceFamily k L P R M α := by
  classical
  simp only [frequencySum,naturalBoxLabels,Finset.sum_product,polynomialValue,
    sum_int_naturalCenters,boxSourceFamily,sourceFamily,integerPolynomialWeyl_eq_frequency]

theorem sourceMixedMoment_eq_boxMixed {j : ℕ} (k s : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (Y : ℝ) :
    sourceMixedMoment k s (naturalBoxLabels k L P R M)
      (fun c => naturalParameters c.1 c.2) (naturalCenters L) Y R=
      boxMixedMoment k s L P R M Y := by
  unfold sourceMixedMoment mixedFrequencyEvenMoment boxMixedMoment
  apply intervalIntegral.integral_congr
  intro α hα
  change ‖frequencySum (naturalBoxLabels k L P R M ×ˢ naturalCenters L)
      (polynomialValue (fun c => powerPolynomial k (naturalParameters c.1 c.2))) α‖^2*
      ‖frequencySum (smoothNumbers Y R) (fun n => ((n^k:ℕ):ℤ)) α‖^(2*s)=_
  rw [natural_auxiliary_frequency]
  simp only [frequencySum,smoothWeyl,phase_eq_fourier]

theorem boxMixedMoment_eq_frequency {j : ℕ} (k s : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (Y : ℝ) :
    boxMixedMoment k s L P R M Y=
      mixedFrequencyEvenMoment (naturalBoxDomain k L P R M) (naturalPhase k) 1
        (smoothNumbers Y R) (fun n => ((n^k:ℕ):ℤ)) s := by
  simp only [boxMixedMoment,mixedFrequencyEvenMoment,mul_one,
    boxSourceFamily_eq_frequency,frequencySum,smoothWeyl,phase_eq_fourier]

theorem boxCrossMoment_le_mixed {j : ℕ} (k s u t : ℕ) (hut : u+t=2*s)
    (L P R : ℝ) (M : Fin j → ℝ) (Y : ℝ) :
    boxCrossMoment k s L P R M Y≤
      (boxMixedMoment k u L P R M Y)^(1/2:ℝ)*
        (smoothMoment k (2*t) Y R)^(1/2:ℝ) := by
  have H := frequencyCrossMoment_le_mixed (naturalBoxDomain k L P R M) (naturalPhase k)
    (smoothNumbers Y R) (fun n => ((n^k:ℕ):ℤ)) s u t hut
  rw [← boxMixedMoment_eq_frequency,← smoothMoment_even_eq_frequency] at H
  simpa only [frequencyCrossMoment,boxCrossMoment,boxSourceFamily_eq_frequency,
    frequencySum,smoothWeyl,phase_eq_fourier] using H

#print axioms sourceMixedMoment_eq_boxMixed
#print axioms boxCrossMoment_le_mixed
end Waring.SeedCompletionNaturalBox

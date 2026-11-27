import Waring.SeedCompletionNaturalUpdate
import Waring.SeedCompletionBoxPermutation

/-! # The initial pure smooth moment enters the full-box recurrence by counts -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges CartesianProductSampling SeedCompletionSourceBounds
open SmoothMoments

def emptyPhi : Fin 0 → ℝ := Fin.elim0

theorem initial_smooth_le_powerBoxMixed (k s : ℕ) (P R : ℝ) :
    smoothMoment k (2*(s+1)) P R≤powerBoxMixed k s 1 emptyPhi P R := by
  classical
  let e : ℕ → NaturalLabel 0 × ℕ := fun n => ((Fin.elim0,Fin.elim0),n)
  have he : Function.Injective e := fun n m h => congrArg Prod.snd h
  have hphase : (fun n => naturalPhase k (e n))=fun n => ((n^k:ℕ):ℤ) := by
    funext n
    simp [naturalPhase,e,naturalParameters,powerPolynomial]
  have himage : (smoothNumbers P R).image e⊆naturalBoxDomain k P P R (fun i => P^(emptyPhi i)) := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,Finset.mem_Icc.mpr (mem_smoothNumbers.mp hn).1⟩
    · apply mem_positiveBox.mpr
      intro i
      exact Fin.elim0 i
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact Fin.elim0 i
  have H := mixedFrequencyEvenMoment_mono himage (Finset.Subset.refl (smoothNumbers P R))
    (naturalPhase k) 1 (fun n => ((n^k:ℕ):ℤ)) s
  rw [mixedFrequencyEvenMoment_image_left _ e he,hphase,
    ← frequencyEvenMoment_eq_mixed,← smoothMoment_even_eq_frequency] at H
  rw [← boxMixedMoment_eq_frequency] at H
  simpa only [powerBoxMixed,total,Finset.univ_eq_empty,Finset.sum_empty,sub_zero,
    Real.rpow_one,one_mul,Nat.add_comm 1 s] using H

theorem first_box_admissible {k s : ℕ} {ψ lam χ : ℝ}
    (hk : 2≤k) (hψ : 0≤ψ) (hψk : (k:ℝ)*ψ≤1)
    (hU : AdmissibleExponent k (2*(s+1)) lam)
    (hX : SourcePowerBound (powerBoxCross k (s+1) 2 (Fin.cons ψ emptyPhi)) χ) :
    AdmissibleExponent k (2*(s+2))
      ((2*((s:ℝ)+1)-1)*ψ+max (1+ψ+(1-ψ)*lam) χ) := by
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hψ1 : ψ≤1 := by nlinarith [mul_nonneg (show 0≤(k:ℝ)-1 by linarith) hψ]
  have H := powerBoxMixed_power (j := 0) (s := s) (D := 1) emptyPhi hk
    (by omega) (le_refl 1) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    hψ hψk (by simpa [total] using hψ1) hU (by simpa only [mul_one] using hX)
  have H' : SourcePowerBound (powerBoxMixed k (s+1) 1 emptyPhi)
      ((2*((s:ℝ)+1)-1)*ψ+max (1+ψ+(1-ψ)*lam) χ) := by
    simpa only [parameterExponent,total,Finset.univ_eq_empty,Finset.sum_empty,
      Nat.cast_zero,mul_zero,zero_add,sub_zero] using H
  have HP : SourcePowerBound (fun P R => smoothMoment k (2*(s+2)) P R)
      ((2*((s:ℝ)+1)-1)*ψ+max (1+ψ+(1-ψ)*lam) χ) := by
    apply H'.of_le (fun P R _ _ => smoothMoment_nonneg ..)
    intro P R hP hR
    convert initial_smooth_le_powerBoxMixed k (s+1) P R using 1 <;> omega
  exact admissible_of_source_bound HP

#print axioms initial_smooth_le_powerBoxMixed
#print axioms first_box_admissible
end Waring.SeedCompletionNaturalBox

import Waring.SeedCompletionCrossCauchy
import Waring.FirstStageRecurrence

/-!
# Exact transport of the first cross integral into the next source moment

The first aggregate domain is reindexed injectively into the complete
first-difference source family. Both factors are squared before either
domain is enlarged. The ordinary center and parameter sets are exposed
so the fully proved source recurrence can be applied to them directly.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionInitialMixed
open SmoothMoments FirstStageTransport FirstDifferenceSecond PolicyCompletionHolder
open PolicyCompletionFundamental PolicyCompletionGoodBranch IntegerDifferencePolynomial
open SeedCompletionCrossCauchy SeedCompletionSharpBackward PolicyCompletionNextDomain

theorem mixedMoment_le_of_injOn {ι κ ν : Type*} [DecidableEq κ]
    (A : Finset ι) (B : Finset κ) (f : ι → κ)
    (hf : Set.InjOn f (↑A : Set ι)) (g : κ → ℤ) (a : ι → ℤ)
    (hphase : ∀ x ∈ A,g (f x)=a x) (hAB : A.image f ⊆ B)
    (p : ℕ) (D : Finset ν) (d : ν → ℤ) (q : ℕ) :
    mixedFrequencyEvenMoment A a p D d q ≤ mixedFrequencyEvenMoment B g p D d q := by
  have heq : mixedFrequencyEvenMoment A a p D d q =
      mixedFrequencyEvenMoment (A.image f) g p D d q := by
    unfold mixedFrequencyEvenMoment
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [Finset.sum_image (fun i hi j hj hij => hf hi hj hij)]
    have hsum : (∑ i ∈ A,fourier (a i) (x : AddCircle (1 : ℝ))) =
        ∑ i ∈ A,fourier (g (f i)) (x : AddCircle (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hphase i hi]
    rw [hsum]
  rw [heq]
  exact mixedFrequencyEvenMoment_mono hAB (Finset.Subset.refl _) g p d q

def firstLabels (H Q R M : ℝ) : Finset (ℕ × ℕ) :=
  Finset.Icc 1 ⌊H⌋₊ ×ˢ CoefficientPower.coefficientBlock Q R M

def firstCenters (P : ℝ) : Finset ℤ :=
  (Finset.Icc 1 ⌊2*P⌋₊).image (fun n : ℕ => (n : ℤ))

def firstParameters (c : ℕ × ℕ) : List (ℤ × ℤ) := [((c.1 : ℤ),(c.2 : ℤ))]

theorem first_source_mixed_eq (k u : ℕ) (P H Q R M Y : ℝ) :
    sourceMixedMoment k u (firstLabels H Q R M) firstParameters (firstCenters P) Y R =
      mixedFrequencyEvenMoment (sourceFirstDomain P H Q R M) (firstFrequency k) 1
        (smoothNumbers Y R) (fun n => ((n^k : ℕ) : ℤ)) u := by
  unfold sourceMixedMoment mixedFrequencyEvenMoment
  have hsum (x : ℝ) :
      (∑ p ∈ firstLabels H Q R M ×ˢ firstCenters P,
        fourier (polynomialValue (fun c => powerPolynomial k (firstParameters c)) p)
          (x : AddCircle (1 : ℝ))) =
      ∑ p ∈ sourceFirstDomain P H Q R M,fourier (firstFrequency k p)
        (x : AddCircle (1 : ℝ)) := by
    simp only [firstLabels,firstCenters,sourceFirstDomain,Finset.sum_product]
    simp_rw [Finset.sum_image (fun i _ j _ hij => Int.natCast_inj.mp hij)]
    rfl
  simp_rw [hsum]

/-- Cauchy with any exact integer split, then literal first-source domain
enlargement and the proved doubling of the short smooth variables. -/
theorem firstCross_le_source_mixed (k s u t : ℕ) (hut : u+t=2*s)
    {P R M : ℝ} (hP : 1 ≤ P) (hM : 1 ≤ M) (hR : 2 ≤ R) :
    firstCross k s P R M ≤
      (sourceMixedMoment k u (firstLabels (P/M^k) P R M) firstParameters
        (firstCenters P) (2*(P/M)) R)^(1/2 : ℝ)*
          (smoothMoment k (2*t) (P/M) R)^(1/2 : ℝ) := by
  have h := nextSmoothCrossIntegral_le_mixed k s u t hut ({()} : Finset Unit)
    (fun _ => []) (CoefficientPower.coefficientBlock P R M) (⌊P⌋₊ : ℤ) (P/M) R
  change firstCross k s P R M ≤ _ at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply Real.rpow_le_rpow _ _ (by norm_num)
  · rw [nextSmoothMoment_eq_mixed,mixedFrequencyEvenMoment_eq_card]
    positivity
  · rw [nextSmoothMoment_eq_mixed,first_source_mixed_eq]
    apply (mixedMoment_le_of_injOn (initialNextDomain k P R M)
      (sourceFirstDomain P (P/M^k) P R M) firstIndex (firstIndex_injOn k P R M)
      (firstFrequency k) _ (fun _ hp => firstIndex_phase hp)
      (initialNextDomain_image_subset k hP hM) 1 (smoothNumbers (P/M) R)
      (fun n => (2 : ℤ)^k*(n : ℤ)^k) u).trans
    have hfreq : (fun n : ℕ => (2 : ℤ)^k*(n : ℤ)^k) =
        fun n : ℕ => ((2*n : ℕ) : ℤ)^k := by
      funext n
      simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow]
    rw [hfreq,← mixedMoment_image_right _ _ _ (smoothNumbers (P/M) R)
      (fun n : ℕ => 2*n) (fun x y hxy => by change 2*x=2*y at hxy; omega)
      (fun n : ℕ => (n : ℤ)^k) u]
    have hsub : (smoothNumbers (P/M) R).image (fun n => 2*n) ⊆
        smoothNumbers (2*(P/M)) R := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      exact double_smooth_mem (div_nonneg (zero_le_one.trans hP) (zero_le_one.trans hM)) hR hm
    simpa only [Nat.cast_pow] using mixedFrequencyEvenMoment_mono (Finset.Subset.refl _)
      hsub (firstFrequency k) 1 (fun n : ℕ => (n : ℤ)^k) u

#print axioms first_source_mixed_eq
#print axioms firstCross_le_source_mixed
end Waring.SeedCompletionInitialMixed

import Waring.SeedCompletionNaturalTransport
import Waring.SeedCompletionCrossCauchy

/-! # The actual common-modulus count bounded by the full next source box

The finite injection enlarges the signed equation before any absolute
value is taken. The resulting first-power cross integral is consequently
that of the complete literal source family.
-/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open CartesianProductSampling PolicyCompletionHolder PolicyCompletionSourceMajor
open EndgameCompletion SmoothMoments SeedCompletionBackwardAggregate
open SeedCompletionBackwardMoments PolicyCompletionNextDomain CoefficientPower
open SeedCompletionEnlargedCross PolicyCompletionGoodBranch PolicyCompletionGoodRecurrence

def boxCrossMoment {j : ℕ} (k s : ℕ) (L P R : ℝ) (M : Fin j → ℝ) (Y : ℝ) : ℝ :=
  ∫ α in (0:ℝ)..1,‖boxSourceFamily k L P R M α‖*‖smoothWeyl k Y R α‖^(2*s)

theorem boxCrossMoment_nonneg {j : ℕ} (k s : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (Y : ℝ) : 0≤boxCrossMoment k s L P R M Y := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro α hα
  positivity

theorem frequencySum_smoothTuples (k s : ℕ) (Y R α : ℝ) :
    frequencySum (finiteTuples (smoothNumbers Y R) s) (smoothTupleValue k s) α=
      (smoothWeyl k Y R α)^s := by
  simp only [frequencySum,smoothTupleValue,smoothWeyl,phase_eq_fourier,Nat.cast_pow]
  exact (sum_pow_fourier (smoothNumbers Y R) (fun n => (n:ℤ)^k) s (α:AddCircle (1:ℝ))).symm

theorem crossIntegral_box {j : ℕ} (k s : ℕ) (L P R : ℝ)
    (M : Fin j → ℝ) (Y : ℝ) :
    crossIntegral (naturalBoxDomain k L P R M) (naturalPhase k)
      (finiteTuples (smoothNumbers Y R) s) (smoothTupleValue k s)=
      boxCrossMoment k s L P R M Y := by
  simp only [crossIntegral,boxCrossMoment,frequencySum_smoothTuples,
    ← boxSourceFamily_eq_frequency,norm_pow,← pow_mul,Nat.mul_comm s 2]

def doubleTuple {s : ℕ} (u : Fin s → ℕ) : Fin s → ℕ := fun i => 2*u i

theorem doubleTuple_injective {s : ℕ} : Function.Injective (@doubleTuple s) := by
  intro u v huv
  funext i
  have H := congrFun huv i
  change 2*u i=2*v i at H
  omega

theorem doubleTuple_frequency (k s : ℕ) (u : Fin s → ℕ) :
    smoothTupleValue k s (doubleTuple u)=(2:ℤ)^k*smoothTupleValue k s u := by
  simp only [smoothTupleValue,doubleTuple,Nat.cast_mul,Nat.cast_ofNat,mul_pow,Finset.mul_sum]

theorem doubleTuple_mem {s : ℕ} {Y R : ℝ} (hY : 0≤Y) (hR : 2≤R)
    {u : Fin s → ℕ} (hu : u∈finiteTuples (smoothNumbers Y R) s) :
    doubleTuple u∈finiteTuples (smoothNumbers (2*Y) R) s := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact double_smooth_mem hY hR (Fintype.mem_piFinset.mp hu i)

theorem commonModulus_sum_le_box {j : ℕ} (k s : ℕ)
    {L P Q R V : ℝ} {M : Fin j → ℝ} (Z : Finset ℤ)
    (hL : 0≤L) (hQ : 0≤Q) (hV : 0<V) (hM : ∀ i,0<M i)
    (hVR : V*R≤P) (hR : 2≤R) (hZ : Z⊆Finset.Icc 1 (⌊L⌋₊:ℤ)) :
    (∑ w∈coefficientBlock Q R V,
      ((commonModulusSolutions (naturalBoxLabels k L P R M ×ˢ Z)
        (smoothNumbers (Q/V) R)
        (fun c => powerPolynomial k (naturalParameters c.1 c.2)) s k w).card:ℝ)) ≤
      ((naturalBoxLabels k L P R M).card:ℝ)*((coefficientBlock Q R V).card:ℝ)*
        (Z.card:ℝ)*smoothMoment k (2*s) (Q/V) R+
        2*boxCrossMoment k s (2*L) P R (Fin.cons V M) (2*(Q/V)) := by
  have H := commonModulus_sum_le_enlarged k s (naturalBoxLabels k L P R M)
    (fun c => naturalParameters c.1 c.2) (coefficientBlock Q R V) (⌊L⌋₊:ℤ) Z (Q/V) R
    (naturalBoxDomain k (2*L) P R (Fin.cons V M))
    (finiteTuples (smoothNumbers (2*(Q/V)) R) s) (naturalPhase k) (smoothTupleValue k s)
    nextNaturalEncode doubleTuple ?_ ?_ hZ
    (nextNaturalEncode_injOn k _ _ _) doubleTuple_injective.injOn
    (fun a ha => nextNaturalEncode_mem_box k hL hV hM hVR ha)
    (fun b hb => doubleTuple_mem (div_nonneg hQ hV.le) hR hb) ?_
    (fun b _ => doubleTuple_frequency k s b)
  · simpa only [crossIntegral_box] using H
  · intro c hc p hp
    obtain ⟨hh,hm⟩ := Finset.mem_product.mp hc
    have H := naturalParameters_pos c.1 c.2
      (fun i => (mem_positiveBox.mp hh i).1)
      (boxCoefficientTuples_pos P R M hm)
    exact (H p hp).2.ne'
  · intro w hw
    exact (mem_smoothNumbers.mp (Finset.mem_filter.mp hw).1).1.1
  · intro a ha
    obtain ⟨hc,ha⟩ := Finset.mem_sigma.mp ha
    obtain ⟨hx,ht⟩ := Finset.mem_product.mp ha
    apply nextNaturalEncode_frequency
    · exact le_trans (by norm_num) (Finset.mem_Icc.mp hx).1
    · exact le_trans (by norm_num) (Finset.mem_Icc.mp ht).1

#print axioms commonModulus_sum_le_box
end Waring.SeedCompletionNaturalBox

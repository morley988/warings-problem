import Waring.SeedCompletionNinthFirst
import Waring.SeedCompletionNinthSecond
import Waring.PolicyCompletionFourthMoment
import Waring.SeedCompletionBackwardMoments
import Waring.PolicyCompletionHolder

/-!
# Fourth moment of the literal degree-nine first auxiliary sum

The ordinary positive-pair difference is encoded by its sum and difference
of centers. Doubling the old height gives the actual second centered phase;
its fixed integer dilation preserves the integrated second moment. The
three-divisor bound can therefore be inserted into the proved Weyl step.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SeedCompletionNinthFourth
open IntegerDifferencePolynomial SeedCompletionBackward SeedCompletionBackwardMoments
open PolicyCompletionHolder UnseparatedDifferencing QuadraticModulation

abbrev Label := ℕ × ℕ

def firstPhase (b : Label) (z : ℤ) : ℤ :=
  (powerPolynomial 9 [((b.1 : ℤ),(b.2 : ℤ))]).eval z

def positiveDifferenceDomain (B : Finset Label) (Z : Finset ℤ) :=
  B ×ˢ positivePairs Z

def positiveDifferencePhase (p : Label × (ℤ × ℤ)) : ℤ :=
  firstPhase p.1 p.2.1-firstPhase p.1 p.2.2

/-- The literal Weyl difference is the positive-pair Fourier sum. -/
theorem firstDifference_eq_frequencySum (B : Finset Label) (Z : Finset ℤ) (N : ℕ)
    (hwidth : ∀ z ∈ Z, ∀ w ∈ Z, z-w ≤ (N : ℤ)) (α : ℝ) :
    firstDifference B (fun _ => Z)
      (fun b z => fourier (firstPhase b z) (α : AddCircle (1 : ℝ))) N =
      frequencySum (positiveDifferenceDomain B Z) positiveDifferencePhase α := by
  rw [firstDifference_eq]
  unfold frequencySum positiveDifferenceDomain
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← positive_pairs_eq_differences Z _ N hwidth]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← fourier_neg,← fourier_add]
  rfl

/-- The actual integer backward identity for a single old parameter. -/
theorem integer_backward_identity (h m z z' : ℤ) (hm : m ≠ 0) :
    (powerPolynomial 9 [(z-z',1),(2*h,m)]).eval (z+z') =
      (2 : ℤ)^9*((powerPolynomial 9 [(h,m)]).eval z-
        (powerPolynomial 9 [(h,m)]).eval z') := by
  have hmold : ∀ p ∈ [(h,m)], p.2 ≠ 0 := by simp [hm]
  have hmnew : ∀ p ∈ [(z-z',1),(2*h,m)], p.2 ≠ 0 := by simp [hm]
  apply (Int.cast_injective (α := ℝ))
  push_cast
  rw [powerPolynomial_eval_int 9 _ hmnew,
    powerPolynomial_eval_int 9 _ hmold,powerPolynomial_eval_int 9 _ hmold]
  have H := backward_phase_identity 9 (realParameters [(h,m)]) (z : ℝ) (z' : ℝ)
    ((z-z' : ℤ) : ℝ) 1 (by push_cast; simp)
  simpa only [realParameters,scaleHeights,List.map_cons,List.map_nil,
    Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_one,Int.cast_add,
    one_pow,div_one,show (2 : ℝ)^9=512 by norm_num] using H

def differenceCode (p : Label × (ℤ × ℤ)) : SeedCompletionNinthSecond.Index :=
  (2*p.1.1,p.1.2,(p.2.1-p.2.2).toNat,(p.2.1+p.2.2).toNat)

theorem differenceCode_injOn (B : Finset Label) (Z : Finset ℤ)
    (hZ : ∀ z ∈ Z, 1 ≤ z) :
    Set.InjOn differenceCode (positiveDifferenceDomain B Z) := by
  intro x hx y hy heq
  have hxp := Finset.mem_filter.mp (Finset.mem_product.mp hx).2
  have hyp := Finset.mem_filter.mp (Finset.mem_product.mp hy).2
  have hx1 := hZ x.2.1 (Finset.mem_product.mp hxp.1).1
  have hx2 := hZ x.2.2 (Finset.mem_product.mp hxp.1).2
  have hy1 := hZ y.2.1 (Finset.mem_product.mp hyp.1).1
  have hy2 := hZ y.2.2 (Finset.mem_product.mp hyp.1).2
  have hh : 2*x.1.1=2*y.1.1 := congrArg (fun p : SeedCompletionNinthSecond.Index => p.1) heq
  have hm : x.1.2=y.1.2 := congrArg (fun p : SeedCompletionNinthSecond.Index => p.2.1) heq
  have hd : (x.2.1-x.2.2).toNat=(y.2.1-y.2.2).toNat :=
    congrArg (fun p : SeedCompletionNinthSecond.Index => p.2.2.1) heq
  have hs : (x.2.1+x.2.2).toNat=(y.2.1+y.2.2).toNat :=
    congrArg (fun p : SeedCompletionNinthSecond.Index => p.2.2.2) heq
  have hdi : x.2.1-x.2.2=y.2.1-y.2.2 := by omega
  have hsi : x.2.1+x.2.2=y.2.1+y.2.2 := by omega
  exact Prod.ext (Prod.ext (by omega) hm) (Prod.ext (by omega) (by omega))

/-- The encoded frequency is exactly the common integer dilation of the
positive-pair frequency, with no remainders or discarded labels. -/
theorem differenceCode_phase (b : Label) (z z' : ℤ)
    (hm : 0 < b.2) (hz : 1 ≤ z) (hz' : 1 ≤ z') (horder : z' < z) :
    (powerPolynomial 9
      [(((differenceCode (b,(z,z'))).2.2.1 : ℤ),1),
        (((differenceCode (b,(z,z'))).1 : ℤ),((differenceCode (b,(z,z'))).2.1 : ℤ))]).eval
      ((differenceCode (b,(z,z'))).2.2.2 : ℤ) =
      (2 : ℤ)^9*positiveDifferencePhase (b,(z,z')) := by
  simp only [differenceCode,Nat.cast_mul,Nat.cast_ofNat]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ z-z'),
    Int.toNat_of_nonneg (by omega : 0 ≤ z+z')]
  exact integer_backward_identity (b.1 : ℤ) (b.2 : ℤ) z z'
    (by exact_mod_cast hm.ne')

/-- A second moment is preserved under injective reindexing of a finite domain. -/
theorem secondMoment_image {ι κ : Type*} [DecidableEq κ] (A : Finset ι)
    (code : ι → κ) (hcode : Set.InjOn code A) (f : κ → ℤ) :
    secondMoment (A.image code) f = secondMoment A (fun x => f (code x)) := by
  unfold secondMoment
  have hs (α : ℝ) :
      (∑ y ∈ A.image code, fourier (f y) (α : AddCircle (1 : ℝ))) =
      ∑ x ∈ A, fourier (f (code x)) (α : AddCircle (1 : ℝ)) :=
    Finset.sum_image (fun x hx y hy h => hcode hx hy h)
  simp_rw [hs]

/-- The second energy of the literal ordinary difference is the actual
encoded centered-difference second moment. -/
theorem positive_difference_second_eq (B : Finset Label) (Z : Finset ℤ)
    (hB : ∀ b ∈ B, 0 < b.2) (hZ : ∀ z ∈ Z, 1 ≤ z) :
    secondMoment (positiveDifferenceDomain B Z) positiveDifferencePhase =
      secondMoment ((positiveDifferenceDomain B Z).image differenceCode)
        (fun p => (powerPolynomial 9
          [((p.2.2.1 : ℤ),1),((p.1 : ℤ),(p.2.1 : ℤ))]).eval (p.2.2.2 : ℤ)) := by
  rw [secondMoment_image _ _ (differenceCode_injOn B Z hZ)]
  have hs : secondMoment (positiveDifferenceDomain B Z)
      (fun p => (powerPolynomial 9
        [(((differenceCode p).2.2.1 : ℤ),1),
          (((differenceCode p).1 : ℤ),((differenceCode p).2.1 : ℤ))]).eval
        ((differenceCode p).2.2.2 : ℤ)) =
      secondMoment (positiveDifferenceDomain B Z) (fun p => (2 : ℤ)^9*positiveDifferencePhase p) := by
    unfold secondMoment
    congr 1
    funext α
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hb := (Finset.mem_product.mp hp).1
    have hz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
    exact congrArg (fun t : ℤ => fourier t (α : AddCircle (1 : ℝ)))
      (differenceCode_phase p.1 p.2.1 p.2.2 (hB p.1 hb)
        (hZ p.2.1 (Finset.mem_product.mp hz.1).1)
        (hZ p.2.2 (Finset.mem_product.mp hz.1).2) hz.2)
  rw [hs,secondMoment_mul_frequency _ _ ((2 : ℤ)^9) (by norm_num)]

#print axioms integer_backward_identity
#print axioms positive_difference_second_eq
end Waring.SeedCompletionNinthFourth

import Waring.SeedCompletionNinthFourthBounds

/-! # Exact ordinary differencing transport for every degree

This module preserves the original positive-pair frequencies. The second
phase is exactly their common nonzero integer dilation.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SeedCompletionFirstWeyl
open IntegerDifferencePolynomial SeedCompletionBackward SeedCompletionBackwardMoments
open PolicyCompletionHolder UnseparatedDifferencing QuadraticModulation
open SeedCompletionNinthFourth (secondMoment_image)
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card secondMoment_congr)

abbrev Label := ℕ × ℕ
abbrev SecondIndex := (ℕ×ℕ)×(ℕ×ℕ)

def firstPhase (k : ℕ) (b : Label) (z : ℤ) : ℤ :=
  (powerPolynomial k [((b.1 : ℤ),(b.2 : ℤ))]).eval z

def positiveDifferenceDomain (B : Finset Label) (Z : Finset ℤ) :=
  B ×ˢ positivePairs Z

def positiveDifferencePhase (k : ℕ) (p : Label × (ℤ × ℤ)) : ℤ :=
  firstPhase k p.1 p.2.1-firstPhase k p.1 p.2.2

theorem firstDifference_eq_frequencySum (k : ℕ) (B : Finset Label) (Z : Finset ℤ) (N : ℕ)
    (hwidth : ∀ z ∈ Z, ∀ w ∈ Z, z-w ≤ (N : ℤ)) (α : ℝ) :
    firstDifference B (fun _ => Z)
      (fun b z => fourier (firstPhase k b z) (α : AddCircle (1 : ℝ))) N =
      frequencySum (positiveDifferenceDomain B Z) (positiveDifferencePhase k) α := by
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

theorem integer_backward_identity (k : ℕ) (h m z z' : ℤ) (hm : m ≠ 0) :
    (powerPolynomial k [(z-z',1),(2*h,m)]).eval (z+z') =
      (2 : ℤ)^k*((powerPolynomial k [(h,m)]).eval z-
        (powerPolynomial k [(h,m)]).eval z') := by
  have hmold : ∀ p ∈ [(h,m)], p.2 ≠ 0 := by simp [hm]
  have hmnew : ∀ p ∈ [(z-z',1),(2*h,m)], p.2 ≠ 0 := by simp [hm]
  apply (Int.cast_injective (α := ℝ))
  push_cast
  rw [powerPolynomial_eval_int k _ hmnew,
    powerPolynomial_eval_int k _ hmold,powerPolynomial_eval_int k _ hmold]
  have H := backward_phase_identity k (realParameters [(h,m)]) (z : ℝ) (z' : ℝ)
    ((z-z' : ℤ) : ℝ) 1 (by push_cast; simp)
  simpa only [realParameters,scaleHeights,List.map_cons,List.map_nil,
    Int.cast_sub,Int.cast_mul,Int.cast_ofNat,Int.cast_one,Int.cast_add,
    one_pow,div_one] using H

def differenceCode (p : Label × (ℤ × ℤ)) : SecondIndex :=
  ((2*p.1.1,(p.2.1-p.2.2).toNat),(p.1.2,(p.2.1+p.2.2).toNat))

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
  have hh : 2*x.1.1=2*y.1.1 := congrArg (fun p : SecondIndex => p.1.1) heq
  have hm : x.1.2=y.1.2 := congrArg (fun p : SecondIndex => p.2.1) heq
  have hd : (x.2.1-x.2.2).toNat=(y.2.1-y.2.2).toNat :=
    congrArg (fun p : SecondIndex => p.1.2) heq
  have hs : (x.2.1+x.2.2).toNat=(y.2.1+y.2.2).toNat :=
    congrArg (fun p : SecondIndex => p.2.2) heq
  have hdi : x.2.1-x.2.2=y.2.1-y.2.2 := by omega
  have hsi : x.2.1+x.2.2=y.2.1+y.2.2 := by omega
  exact Prod.ext (Prod.ext (by omega) hm) (Prod.ext (by omega) (by omega))

def secondPhase (k : ℕ) (p : SecondIndex) : ℤ :=
  (powerPolynomial k [((p.1.2 : ℤ),1),((p.1.1 : ℤ),(p.2.1 : ℤ))]).eval (p.2.2 : ℤ)

theorem differenceCode_phase (k : ℕ) (b : Label) (z z' : ℤ)
    (hm : 0 < b.2) (hz : 1 ≤ z) (hz' : 1 ≤ z') (horder : z' < z) :
    secondPhase k (differenceCode (b,(z,z'))) =
      (2 : ℤ)^k*positiveDifferencePhase k (b,(z,z')) := by
  simp only [secondPhase,differenceCode,Nat.cast_mul,Nat.cast_ofNat]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ z-z'),
    Int.toNat_of_nonneg (by omega : 0 ≤ z+z')]
  exact integer_backward_identity k (b.1 : ℤ) (b.2 : ℤ) z z'
    (by exact_mod_cast hm.ne')

theorem positive_difference_second_eq (k : ℕ) (B : Finset Label) (Z : Finset ℤ)
    (hB : ∀ b ∈ B, 0 < b.2) (hZ : ∀ z ∈ Z, 1 ≤ z) :
    secondMoment (positiveDifferenceDomain B Z) (positiveDifferencePhase k) =
      secondMoment ((positiveDifferenceDomain B Z).image differenceCode) (secondPhase k) := by
  rw [secondMoment_image _ _ (differenceCode_injOn B Z hZ)]
  have hs := secondMoment_congr (positiveDifferenceDomain B Z)
    (fun p => secondPhase k (differenceCode p))
    (fun p => (2 : ℤ)^k*positiveDifferencePhase k p) (by
      intro p hp
      have hb := (Finset.mem_product.mp hp).1
      have hz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
      exact differenceCode_phase k p.1 p.2.1 p.2.2 (hB p.1 hb)
        (hZ p.2.1 (Finset.mem_product.mp hz.1).1)
        (hZ p.2.2 (Finset.mem_product.mp hz.1).2) hz.2)
  rw [hs,secondMoment_mul_frequency _ _ ((2 : ℤ)^k) (by positivity)]

def familyFirstSum (k : ℕ) (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  familySum B (fun _ => centers N)
    (fun b z => fourier (firstPhase k b z) (α : AddCircle (1 : ℝ)))

def familyDifferenceSum (k : ℕ) (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  firstDifference B (fun _ => centers N)
    (fun b z => fourier (firstPhase k b z) (α : AddCircle (1 : ℝ))) N

theorem familyDifference_second_eq (k : ℕ) (B : Finset Label) (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖familyDifferenceSum k B N α‖^2) =
      secondMoment (positiveDifferenceDomain B (centers N)) (positiveDifferencePhase k) := by
  unfold familyDifferenceSum
  simp_rw [firstDifference_eq_frequencySum k B (centers N) N (centers_width N)]
  rfl

#print axioms integer_backward_identity
#print axioms positive_difference_second_eq
end Waring.SeedCompletionFirstWeyl

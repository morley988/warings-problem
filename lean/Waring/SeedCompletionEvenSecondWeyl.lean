import Waring.SeedCompletionFamilyWeyl
import Waring.SeedCompletionEvenTripleBox
import Waring.SeedCompletionEvenDoubleSource
import Waring.SeedCompletionEvenFourth

/-! # Exact ordinary differencing of the even-degree j=2 auxiliary family -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.SeedCompletionEvenSecondWeyl
open IntegerDifferencePolynomial SeedCompletionBackwardMoments SeedCompletionBackwardCount
open PolicyCompletionHolder UnseparatedDifferencing QuadraticModulation
open SeedCompletionEvenDouble (Pair)
open SeedCompletionEvenTriple (Heights)
open SeedCompletionNinthFourth (secondMoment_image)
open SeedCompletionNinthFourthBounds (centers centers_pos centers_width centers_card
  secondMoment_congr sum_natural_centers)

abbrev Label := Pair×Pair
abbrev ThirdIndex := Heights×(Pair×ℕ)

def firstPhase (d : ℕ) (b : Label) (z : ℤ) : ℤ :=
  (powerPolynomial (2*d) [((b.1.2 : ℤ),(b.2.2 : ℤ)),((b.1.1 : ℤ),(b.2.1 : ℤ))]).eval z

def positiveDifferenceDomain (B : Finset Label) (Z : Finset ℤ) := B ×ˢ positivePairs Z

def positiveDifferencePhase (d : ℕ) (p : Label×(ℤ×ℤ)) : ℤ :=
  firstPhase d p.1 p.2.1-firstPhase d p.1 p.2.2

def differenceCode (p : Label×(ℤ×ℤ)) : ThirdIndex :=
  (((2*p.1.1.1,2*p.1.1.2),(p.2.1-p.2.2).toNat),(p.1.2,(p.2.1+p.2.2).toNat))

def thirdPhase (d : ℕ) (p : ThirdIndex) : ℤ :=
  (powerPolynomial (2*d) [((p.1.2 : ℤ),1),((p.1.1.2 : ℤ),(p.2.1.2 : ℤ)),
    ((p.1.1.1 : ℤ),(p.2.1.1 : ℤ))]).eval (p.2.2 : ℤ)

theorem firstDifference_eq_frequencySum (d : ℕ) (B : Finset Label) (Z : Finset ℤ) (N : ℕ)
    (hwidth : ∀ z ∈ Z,∀ w ∈ Z,z-w ≤ (N : ℤ)) (α : ℝ) :
    firstDifference B (fun _ => Z)
      (fun b z => fourier (firstPhase d b z) (α : AddCircle (1 : ℝ))) N =
      frequencySum (positiveDifferenceDomain B Z) (positiveDifferencePhase d) α := by
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

theorem differenceCode_injOn (B : Finset Label) (Z : Finset ℤ)
    (hZ : ∀ z ∈ Z,1 ≤ z) : Set.InjOn differenceCode (positiveDifferenceDomain B Z) := by
  intro x hx y hy he
  have hxp := Finset.mem_filter.mp (Finset.mem_product.mp hx).2
  have hyp := Finset.mem_filter.mp (Finset.mem_product.mp hy).2
  have hx1 := hZ x.2.1 (Finset.mem_product.mp hxp.1).1
  have hx2 := hZ x.2.2 (Finset.mem_product.mp hxp.1).2
  have hy1 := hZ y.2.1 (Finset.mem_product.mp hyp.1).1
  have hy2 := hZ y.2.2 (Finset.mem_product.mp hyp.1).2
  have hh1 : 2*x.1.1.1=2*y.1.1.1 := congrArg (fun p : ThirdIndex => p.1.1.1) he
  have hh2 : 2*x.1.1.2=2*y.1.1.2 := congrArg (fun p : ThirdIndex => p.1.1.2) he
  have hm : x.1.2=y.1.2 := congrArg (fun p : ThirdIndex => p.2.1) he
  have hd : (x.2.1-x.2.2).toNat=(y.2.1-y.2.2).toNat :=
    congrArg (fun p : ThirdIndex => p.1.2) he
  have hs : (x.2.1+x.2.2).toNat=(y.2.1+y.2.2).toNat :=
    congrArg (fun p : ThirdIndex => p.2.2) he
  exact Prod.ext (Prod.ext (Prod.ext (by omega) (by omega)) hm)
    (Prod.ext (by omega) (by omega))

theorem differenceCode_phase (d : ℕ) (b : Label) (z z' : ℤ)
    (hm : 0 < b.2.1 ∧ 0 < b.2.2) (hz : 1 ≤ z) (hz' : 1 ≤ z') (horder : z' < z) :
    thirdPhase d (differenceCode (b,(z,z')))=(2 : ℤ)^(2*d)*positiveDifferencePhase d (b,(z,z')) := by
  simp only [thirdPhase,differenceCode,Nat.cast_mul,Nat.cast_ofNat]
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ z-z'),
    Int.toNat_of_nonneg (by omega : 0 ≤ z+z')]
  have H := SeedCompletionFamilyWeyl.integer_backward_identity (2*d)
    [((b.1.2 : ℤ),(b.2.2 : ℤ)),((b.1.1 : ℤ),(b.2.1 : ℤ))] (by
      intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl
      · change (b.2.2 : ℤ) ≠ 0
        exact_mod_cast hm.2.ne'
      · change (b.2.1 : ℤ) ≠ 0
        exact_mod_cast hm.1.ne') z z'
  simpa only [doubleHeights,List.map_cons,List.map_nil] using H

theorem positive_difference_second_eq (d : ℕ) (B : Finset Label) (Z : Finset ℤ)
    (hB : ∀ b ∈ B,0 < b.2.1 ∧ 0 < b.2.2) (hZ : ∀ z ∈ Z,1 ≤ z) :
    secondMoment (positiveDifferenceDomain B Z) (positiveDifferencePhase d) =
      secondMoment ((positiveDifferenceDomain B Z).image differenceCode) (thirdPhase d) := by
  rw [secondMoment_image _ _ (differenceCode_injOn B Z hZ)]
  have hs := secondMoment_congr (positiveDifferenceDomain B Z)
    (fun p => thirdPhase d (differenceCode p)) (fun p => (2 : ℤ)^(2*d)*positiveDifferencePhase d p) (by
      intro p hp
      have hb := (Finset.mem_product.mp hp).1
      have hz := Finset.mem_filter.mp (Finset.mem_product.mp hp).2
      exact differenceCode_phase d p.1 p.2.1 p.2.2 (hB p.1 hb)
        (hZ p.2.1 (Finset.mem_product.mp hz.1).1)
        (hZ p.2.2 (Finset.mem_product.mp hz.1).2) hz.2)
  rw [hs,secondMoment_mul_frequency _ _ ((2 : ℤ)^(2*d)) (by positivity)]

def familySum (d : ℕ) (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  UnseparatedDifferencing.familySum B (fun _ => centers N)
    (fun b z => fourier (firstPhase d b z) (α : AddCircle (1 : ℝ)))

def differenceSum (d : ℕ) (B : Finset Label) (N : ℕ) (α : ℝ) : ℂ :=
  firstDifference B (fun _ => centers N)
    (fun b z => fourier (firstPhase d b z) (α : AddCircle (1 : ℝ))) N

theorem familySum_eq_actualSum (d : ℕ) (H B : Finset Pair) (N : ℕ) (α : ℝ) :
    familySum d (H ×ˢ B) N α =
      SeedCompletionEvenDoubleBox.actualSum d H B (Finset.Icc 1 N) α := by
  unfold familySum UnseparatedDifferencing.familySum SeedCompletionEvenDoubleBox.actualSum
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro m hm
  symm
  exact sum_natural_centers N
    (fun z => fourier ((powerPolynomial (2*d) [((h.2 : ℤ),(m.2 : ℤ)),
      ((h.1 : ℤ),(m.1 : ℤ))]).eval z) (α : AddCircle (1 : ℝ)))

theorem difference_second_eq (d : ℕ) (B : Finset Label) (N : ℕ) :
    (∫ α in (0 : ℝ)..1,‖differenceSum d B N α‖^2)=
      secondMoment (positiveDifferenceDomain B (centers N)) (positiveDifferencePhase d) := by
  unfold differenceSum
  simp_rw [firstDifference_eq_frequencySum d B (centers N) N (centers_width N)]
  rfl

#print axioms positive_difference_second_eq
#print axioms familySum_eq_actualSum
end Waring.SeedCompletionEvenSecondWeyl

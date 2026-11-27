import Waring.PolicyCompletionMajorSourceBound
import Waring.PolicyCompletionScaledBounds
import Waring.CartesianMomentAdapters

/-! # The source family is exactly the Cartesian family used by every cap -/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionSourceCartesian
open PolicyCompletionMajorFamily PolicyCompletionSourceMajor PolicyCompletionMajorBoxRanges
open PolicyCompletionMajorPowerRanges PolicyCompletionScaledBounds
open CartesianProductSampling CartesianMomentAdapters CartesianPolynomialBounds
open PolynomialSumReduction IntegerDifferencePolynomial

theorem naturalParameters_real {j : ℕ} (h m : Fin j → ℕ) :
    realParameters (naturalParameters h m)=parameters (realTuple h) (realTuple m) := by
  simp [realParameters,naturalParameters,parameters,realTuple,List.map_ofFn,Function.comp_def]

theorem sum_int_Icc_nat_complex (N : ℕ) (f : ℤ → ℂ) :
    (∑ z∈Finset.Icc (1:ℤ) (N:ℤ),f z)=∑ n∈Finset.Icc 1 N,f (n:ℤ) := by
  symm
  apply Finset.sum_bij (fun (n:ℕ) _ => (n:ℤ))
  · intro n hn
    have hh := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩
  · intro n hn m hm heq
    exact_mod_cast heq
  · intro z hz
    have hh := Finset.mem_Icc.mp hz
    have hz0 : 0≤z := by omega
    exact ⟨z.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,Int.toNat_of_nonneg hz0⟩
  · intro n hn
    rfl

theorem sourceFamily_eq_cartesian {j : ℕ} (k : ℕ) (bounds : Fin j → ℕ)
    (C : Fin j → Finset ℕ) (L α : ℝ) (hC : ∀ i,∀ m∈C i,m≠0) :
    sourceFamily k (positiveBox bounds) (Fintype.piFinset C) L α=
      polynomialFamily k (cartesianParameters (realBox bounds) (realCoefficientSets C))
        Prod.fst Prod.snd α 1 (⌊L⌋₊:ℤ) := by
  have hpi : Fintype.piFinset (realCoefficientSets C)=(Fintype.piFinset C).image realTuple := by
    unfold realCoefficientSets realTuple
    exact Fintype.piFinset_image (fun _ (n:ℕ) => (n:ℝ)) C
  unfold sourceFamily polynomialFamily UnseparatedDifferencing.familySum cartesianParameters realBox
  rw [Finset.sum_product,hpi]
  rw [Finset.sum_image (fun _ _ _ _ heq => realTuple_injective heq)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_image (fun _ _ _ _ heq => realTuple_injective heq)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integerPolynomialWeyl_eq_source_sum k _ ?_,naturalParameters_real,
    sum_int_Icc_nat_complex]
  · rfl
  · simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast hC i (m i) (Fintype.mem_piFinset.mp hm i)

theorem source_box_power_eq_cartesian {j : ℕ} (k : ℕ) {P : ℝ} (hP : 0<P)
    (D R α : ℝ) (φ : Fin j → ℝ) :
    boxSourceFamily k (D*P) P R (fun i => P^(φ i)) α=
      polynomialFamily k
        (cartesianParameters (realBox (scaledBounds D P (shiftExponents k φ)))
          (realCoefficientSets (fun i => CoefficientPower.coefficientBlock P R (P^(φ i)))))
        Prod.fst Prod.snd α 1 (⌊D*P⌋₊:ℤ) := by
  have hb : boxHeightBounds k (D*P) (fun i => P^(φ i))=scaledBounds D P (shiftExponents k φ) := by
    funext i
    unfold boxHeightBounds scaledBounds
    rw [boxHeights_power k hP D φ i]
  unfold boxSourceFamily boxCoefficientTuples
  rw [hb]
  apply sourceFamily_eq_cartesian
  intro i m hm
  have hp := (SmoothMoments.mem_smoothNumbers.mp (Finset.mem_filter.mp hm).1).1.1
  omega

#print axioms sourceFamily_eq_cartesian
#print axioms source_box_power_eq_cartesian
end Waring.PolicyCompletionSourceCartesian

import Waring.DifferencePolynomials
import Waring.UnseparatedDifferencing
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# From the five source polynomials to actual quadratic interval sums

The original interval is Cartesian. Ordinary differencing retains the one
original coefficient tuple. Only after those differences do we replace
`z` by `xi = 2*z + sum(shifts)`. The resulting interval and parity class
depend on the ordinary shifts, independently of every coefficient variable.
-/

noncomputable section
open scoped BigOperators
namespace Waring.PolynomialSumReduction
open Differences UnseparatedDifferencing QuadraticModulation

def parameters {j : ℕ} (h m : Fin j → ℝ) : List (ℝ × ℝ) :=
  List.ofFn (fun i => (h i, m i))

def coefficientPolynomial {j : ℕ} (p : ℕ) (h m : Fin j → ℝ) : ℝ :=
  ∑ i, (h i)^2 * (m i)^p

def normalForm {j : ℕ} (p : ℕ) (A Γ U : ℝ) (h m : Fin j → ℝ) (ξ : ℝ) : ℝ :=
  A*Γ*(3*ξ^2+U+4*coefficientPolynomial p h m)

def parityInterval (a b s : ℤ) : Finset ℤ :=
  (Finset.Icc (2*a+s) (2*b+s)).filter (fun ξ => ξ%2=s%2)

/-- Exact reindexing, including empty intervals. The endpoints and residue
contain no coefficient parameter. -/
theorem sum_parity_reindex (a b s : ℤ) (f : ℤ → ℂ) :
    (∑ z ∈ Finset.Icc a b, f (2*z+s)) = ∑ ξ ∈ parityInterval a b s, f ξ := by
  classical
  apply Finset.sum_bij (fun z _ => 2*z+s)
  · intro z hz
    rcases Finset.mem_Icc.mp hz with ⟨ha,hb⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro z hz w hw heq
    omega
  · intro ξ hξ
    rcases Finset.mem_filter.mp hξ with ⟨hξ,hmod⟩
    rcases Finset.mem_Icc.mp hξ with ⟨ha,hb⟩
    refine ⟨(ξ-s)/2, Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro z hz
    rfl

theorem normalForm_sum_reindex {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (h m : Fin j → ℝ) (a b s : ℤ) :
    (∑ z ∈ Finset.Icc a b,
      e (α*normalForm p A Γ U h m (2*(z:ℝ)+(s:ℝ)))) =
      ∑ ξ ∈ parityInterval a b s, e (α*normalForm p A Γ U h m (ξ:ℝ)) := by
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
    sum_parity_reindex a b s (fun ξ => e (α*normalForm p A Γ U h m (ξ:ℝ)))

theorem reduction_k8_j4 (h m : Fin 4 → ℝ) (u v z : ℝ)
    (hm : ∀ i, m i ≠ 0) :
    ordinaryDifference (ordinaryDifference (modifiedCenteredPower 8 (parameters h m)) u) v z =
      normalForm 16 26880 ((∏ i, h i)*u*v) (u^2+v^2) h m (2*z+u+v) := by
  have H := quadratic_reduction_k8_j4 (h 0) (m 0) (h 1) (m 1) (h 2) (m 2)
    (h 3) (m 3) u v z (hm 0) (hm 1) (hm 2) (hm 3)
  norm_num only [] at H
  simpa [parameters, List.ofFn_succ, normalForm, coefficientPolynomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using H

theorem reduction_k8_j5 (h m : Fin 5 → ℝ) (u z : ℝ)
    (hm : ∀ i, m i ≠ 0) :
    ordinaryDifference (modifiedCenteredPower 8 (parameters h m)) u z =
      normalForm 16 53760 ((∏ i, h i)*u) (u^2) h m (2*z+u) := by
  have H := quadratic_reduction_k8_j5 (h 0) (m 0) (h 1) (m 1) (h 2) (m 2)
    (h 3) (m 3) (h 4) (m 4) u z (hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  norm_num only [] at H
  simpa [parameters, List.ofFn_succ, normalForm, coefficientPolynomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using H

theorem reduction_k8_j6 (h m : Fin 6 → ℝ) (z : ℝ)
    (hm : ∀ i, m i ≠ 0) :
    modifiedCenteredPower 8 (parameters h m) z =
      normalForm 16 107520 (∏ i, h i) 0 h m (2*z) := by
  have H := quadratic_reduction_k8_j6 (h 0) (m 0) (h 1) (m 1) (h 2) (m 2)
    (h 3) (m 3) (h 4) (m 4) (h 5) (m 5) z
    (hm 0) (hm 1) (hm 2) (hm 3) (hm 4) (hm 5)
  norm_num only [] at H
  simpa [parameters, List.ofFn_succ, normalForm, coefficientPolynomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using H

theorem reduction_k9_j5 (h m : Fin 5 → ℝ) (u v z : ℝ)
    (hm : ∀ i, m i ≠ 0) :
    ordinaryDifference (ordinaryDifference (modifiedCenteredPower 9 (parameters h m)) u) v z =
      normalForm 18 483840 ((∏ i, h i)*u*v) (u^2+v^2) h m (2*z+u+v) := by
  have H := quadratic_reduction_k9_j5 (h 0) (m 0) (h 1) (m 1) (h 2) (m 2)
    (h 3) (m 3) (h 4) (m 4) u v z (hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  norm_num only [] at H
  simpa [parameters, List.ofFn_succ, normalForm, coefficientPolynomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using H

theorem reduction_k9_j6 (h m : Fin 6 → ℝ) (u z : ℝ)
    (hm : ∀ i, m i ≠ 0) :
    ordinaryDifference (modifiedCenteredPower 9 (parameters h m)) u z =
      normalForm 18 967680 ((∏ i, h i)*u) (u^2) h m (2*z+u) := by
  have H := quadratic_reduction_k9_j6 (h 0) (m 0) (h 1) (m 1) (h 2) (m 2)
    (h 3) (m 3) (h 4) (m 4) (h 5) (m 5) u z
    (hm 0) (hm 1) (hm 2) (hm 3) (hm 4) (hm 5)
  norm_num only [] at H
  simpa [parameters, List.ofFn_succ, normalForm, coefficientPolynomial,
    Fin.sum_univ_succ, Fin.prod_univ_succ, mul_assoc, add_assoc] using H

/-- The exact first differenced sum on its shortened Cartesian interval. -/
theorem firstDifference_interval_phase {ι : Type*} (B : Finset ι)
    (φ : ι → ℝ → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) :
    firstDifference B (fun _ => Finset.Icc a b) (fun i z => e (α*φ i z)) N =
      ∑ i ∈ B, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
        ∑ z ∈ Finset.Icc a (b-u), e (α*ordinaryDifference (φ i) (u:ℝ) (z:ℝ)) := by
  classical
  simp only [firstDifference, familySum, differenceParameters, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u hu
  have hu0 : 0 ≤ u := by have := (Finset.mem_Icc.mp hu).1; omega
  rw [differenceDomain_interval a b u i hu0]
  apply Finset.sum_congr rfl
  intro z hz
  rw [differenceFunction_phase]
  congr 1
  simp only [ordinaryDifference, Int.cast_add]
  ring

/-- The exact second difference still uses the same one original index i. -/
theorem secondDifference_interval_phase {ι : Type*} (B : Finset ι)
    (φ : ι → ℝ → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) :
    secondDifference B (fun _ => Finset.Icc a b) (fun i z => e (α*φ i z)) N =
      ∑ i ∈ B, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
        ∑ v ∈ Finset.Icc (1:ℤ) (N:ℤ),
          ∑ z ∈ Finset.Icc a (b-u-v),
            e (α*ordinaryDifference (ordinaryDifference (φ i) (u:ℝ)) (v:ℝ) (z:ℝ)) := by
  classical
  simp only [secondDifference, firstDifference, familySum, differenceParameters,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  have hu0 : 0 ≤ u := by have := (Finset.mem_Icc.mp hu).1; omega
  have hv0 : 0 ≤ v := by have := (Finset.mem_Icc.mp hv).1; omega
  rw [secondDifferenceDomain_interval a b u v i hu0 hv0]
  apply Finset.sum_congr rfl
  intro z hz
  rw [secondDifferenceFunction_phase]
  congr 1
  simp only [ordinaryDifference, Int.cast_add]
  ring

/-- The actual original finite family, with its full modified centered power. -/
def polynomialFamily {ι : Type*} {j : ℕ} (k : ℕ) (B : Finset ι)
    (h m : ι → Fin j → ℝ) (α : ℝ) (a b : ℤ) : ℂ :=
  familySum B (fun _ => Finset.Icc a b)
    (fun i z => e (α*modifiedCenteredPower k (parameters (h i) (m i)) z))

def reducedFirstSum {ι : Type*} {j : ℕ} (p : ℕ) (A : ℝ) (B : Finset ι)
    (h m : ι → Fin j → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) : ℂ :=
  ∑ i ∈ B, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
    ∑ ξ ∈ parityInterval a (b-u) u,
      e (α*normalForm p A ((∏ l, h i l)*(u:ℝ)) ((u:ℝ)^2) (h i) (m i) (ξ:ℝ))

def reducedSecondSum {ι : Type*} {j : ℕ} (p : ℕ) (A : ℝ) (B : Finset ι)
    (h m : ι → Fin j → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) : ℂ :=
  ∑ i ∈ B, ∑ u ∈ Finset.Icc (1:ℤ) (N:ℤ),
    ∑ v ∈ Finset.Icc (1:ℤ) (N:ℤ),
      ∑ ξ ∈ parityInterval a (b-u-v) (u+v),
        e (α*normalForm p A ((∏ l, h i l)*(u:ℝ)*(v:ℝ))
          ((u:ℝ)^2+(v:ℝ)^2) (h i) (m i) (ξ:ℝ))

theorem firstDifference_reduced {ι : Type*} {j : ℕ} (k p : ℕ) (A : ℝ)
    (B : Finset ι) (h m : ι → Fin j → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ)
    (hred : ∀ i ∈ B, ∀ u z : ℝ,
      ordinaryDifference (modifiedCenteredPower k (parameters (h i) (m i))) u z =
        normalForm p A ((∏ l, h i l)*u) (u^2) (h i) (m i) (2*z+u)) :
    firstDifference B (fun _ => Finset.Icc a b)
      (fun i z => e (α*modifiedCenteredPower k (parameters (h i) (m i)) z)) N =
      reducedFirstSum p A B h m α a b N := by
  rw [firstDifference_interval_phase]
  unfold reducedFirstSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [hred i hi]
  exact normalForm_sum_reindex p A _ _ α (h i) (m i) a (b-u) u

theorem secondDifference_reduced {ι : Type*} {j : ℕ} (k p : ℕ) (A : ℝ)
    (B : Finset ι) (h m : ι → Fin j → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ)
    (hred : ∀ i ∈ B, ∀ u v z : ℝ,
      ordinaryDifference (ordinaryDifference
        (modifiedCenteredPower k (parameters (h i) (m i))) u) v z =
        normalForm p A ((∏ l, h i l)*u*v) (u^2+v^2) (h i) (m i) (2*z+u+v)) :
    secondDifference B (fun _ => Finset.Icc a b)
      (fun i z => e (α*modifiedCenteredPower k (parameters (h i) (m i)) z)) N =
      reducedSecondSum p A B h m α a b N := by
  rw [secondDifference_interval_phase]
  unfold reducedSecondSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp_rw [hred i hi]
  simpa only [Int.cast_add, add_assoc] using
    normalForm_sum_reindex p A _ _ α (h i) (m i) a (b-u-v) (u+v)

/-- Actual k=8, j=4 polynomial-family bound, with the coefficient tuple
retained until the quadratic parity interval has been produced. -/
theorem family_k8_j4_quadratic_bound {ι : Type*} (B : Finset ι)
    (h m : ι → Fin 4 → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) (hN : 0 < N)
    (hlen : b+1-a ≤ (N:ℤ)) (hm : ∀ i ∈ B, ∀ l, m i l ≠ 0) :
    ‖polynomialFamily 8 B h m α a b‖^4 ≤
      16*((N:ℝ)^3*(B.card:ℝ)^4+(N:ℝ)*(B.card:ℝ)^3*‖reducedSecondSum 16 26880 B h m α a b N‖) := by
  have H := second_interval_family_bound B
    (fun i z => α*modifiedCenteredPower 8 (parameters (h i) (m i)) z) a b N hN hlen
  rw [secondDifference_reduced 8 16 26880 B h m α a b N
    (fun i hi u v z => reduction_k8_j4 (h i) (m i) u v z (hm i hi))] at H
  exact H

/-- Actual k=8, j=5 polynomial-family bound, with the coefficient tuple
retained until the quadratic parity interval has been produced. -/
theorem family_k8_j5_quadratic_bound {ι : Type*} (B : Finset ι)
    (h m : ι → Fin 5 → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ)
    (hlen : b+1-a ≤ (N:ℤ)) (hm : ∀ i ∈ B, ∀ l, m i l ≠ 0) :
    ‖polynomialFamily 8 B h m α a b‖^2 ≤
      (N:ℝ)*(B.card:ℝ)^2+2*(B.card:ℝ)*‖reducedFirstSum 16 53760 B h m α a b N‖ := by
  have H := first_interval_family_bound B
    (fun i z => α*modifiedCenteredPower 8 (parameters (h i) (m i)) z) a b N hlen
  rw [firstDifference_reduced 8 16 53760 B h m α a b N
    (fun i hi u z => reduction_k8_j5 (h i) (m i) u z (hm i hi))] at H
  exact H

/-- Actual k=9, j=5 polynomial-family bound, with the coefficient tuple
retained until the quadratic parity interval has been produced. -/
theorem family_k9_j5_quadratic_bound {ι : Type*} (B : Finset ι)
    (h m : ι → Fin 5 → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ) (hN : 0 < N)
    (hlen : b+1-a ≤ (N:ℤ)) (hm : ∀ i ∈ B, ∀ l, m i l ≠ 0) :
    ‖polynomialFamily 9 B h m α a b‖^4 ≤
      16*((N:ℝ)^3*(B.card:ℝ)^4+(N:ℝ)*(B.card:ℝ)^3*‖reducedSecondSum 18 483840 B h m α a b N‖) := by
  have H := second_interval_family_bound B
    (fun i z => α*modifiedCenteredPower 9 (parameters (h i) (m i)) z) a b N hN hlen
  rw [secondDifference_reduced 9 18 483840 B h m α a b N
    (fun i hi u v z => reduction_k9_j5 (h i) (m i) u v z (hm i hi))] at H
  exact H

/-- Actual k=9, j=6 polynomial-family bound, with the coefficient tuple
retained until the quadratic parity interval has been produced. -/
theorem family_k9_j6_quadratic_bound {ι : Type*} (B : Finset ι)
    (h m : ι → Fin 6 → ℝ) (α : ℝ) (a b : ℤ) (N : ℕ)
    (hlen : b+1-a ≤ (N:ℤ)) (hm : ∀ i ∈ B, ∀ l, m i l ≠ 0) :
    ‖polynomialFamily 9 B h m α a b‖^2 ≤
      (N:ℝ)*(B.card:ℝ)^2+2*(B.card:ℝ)*‖reducedFirstSum 18 967680 B h m α a b N‖ := by
  have H := first_interval_family_bound B
    (fun i z => α*modifiedCenteredPower 9 (parameters (h i) (m i)) z) a b N hlen
  rw [firstDifference_reduced 9 18 967680 B h m α a b N
    (fun i hi u z => reduction_k9_j6 (h i) (m i) u z (hm i hi))] at H
  exact H

/-- The degree-eight j=6 policy is already quadratic and needs no ordinary
shift. Reindexing still gives the even residue class, independently of m. -/
theorem family_k8_j6_quadratic_identity {ι : Type*} (B : Finset ι)
    (h m : ι → Fin 6 → ℝ) (α : ℝ) (a b : ℤ)
    (hm : ∀ i ∈ B, ∀ l, m i l ≠ 0) :
    polynomialFamily 8 B h m α a b =
      ∑ i ∈ B, ∑ ξ ∈ parityInterval a b 0,
        e (α*normalForm 16 107520 (∏ l, h i l) 0 (h i) (m i) (ξ:ℝ)) := by
  unfold polynomialFamily familySum
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [reduction_k8_j6 (h i) (m i) _ (hm i hi)]
  simpa only [Int.cast_zero, add_zero] using
    normalForm_sum_reindex 16 107520 _ 0 α (h i) (m i) a b 0

#print axioms family_k8_j4_quadratic_bound
#print axioms family_k8_j5_quadratic_bound
#print axioms family_k8_j6_quadratic_identity
#print axioms family_k9_j5_quadratic_bound
#print axioms family_k9_j6_quadratic_bound

end Waring.PolynomialSumReduction

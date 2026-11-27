import WaringSiegel.WSL4WeilDistinctSum
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

/-- A coefficient of the nodal polynomial whose roots are geometric monomials. -/
def geometricCoefficient (s : Finset ℕ) (sigma : ℕ) : ℤ[X] :=
  (∏ i∈s,((X : (ℤ[X])[X])-C ((X:ℤ[X])^i))).coeff sigma

/-- The explicit integer polynomial after extracting its forced initial monomial. -/
def geometricCoefficientFactor (s : Finset ℕ) (sigma : ℕ) : ℤ[X] :=
  ∑ t∈s.powersetCard (s.card-sigma),
    (-1 : ℤ[X])^(s.card-sigma)*X^((∑ i∈t,i)-(s.card-sigma)*(s.card-sigma-1)/2)

theorem geometricCoefficient_eq_sum (s : Finset ℕ) (sigma : ℕ) (hsigma : sigma≤s.card) :
    geometricCoefficient s sigma =
      ∑ t∈s.powersetCard (s.card-sigma),(-1 : ℤ[X])^(s.card-sigma)*X^(∑ i∈t,i) := by
  have hp : (∏ i∈s,((X : (ℤ[X])[X])-C ((X:ℤ[X])^i)))=
      ∏ i∈s,((X : (ℤ[X])[X])+C (-((X:ℤ[X])^i))) := by
    simp only [map_neg,sub_eq_add_neg]
  rw [geometricCoefficient,hp,Finset.prod_X_add_C_coeff s _ hsigma]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.prod_neg,Finset.prod_pow_eq_pow_sum]
  rw [(Finset.mem_powersetCard.mp ht).2]

theorem geometricCoefficient_factor (s : Finset ℕ) (sigma : ℕ) (hsigma : sigma≤s.card) :
    geometricCoefficient s sigma =
      X^((s.card-sigma)*(s.card-sigma-1)/2)*geometricCoefficientFactor s sigma := by
  rw [geometricCoefficient_eq_sum s sigma hsigma,geometricCoefficientFactor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard := (Finset.mem_powersetCard.mp ht).2
  have hl := triangle_card_le_nat_sum t
  rw [hcard] at hl
  have he : (∑i∈t,i)=(s.card-sigma)*(s.card-sigma-1)/2+
      ((∑i∈t,i)-(s.card-sigma)*(s.card-sigma-1)/2) := by omega
  conv_lhs => rw [he,pow_add]
  ring

theorem geometricCoefficientFactor_natDegree_le
    (s : Finset ℕ) (n sigma : ℕ) (hs : ∀i∈s,i≤n) :
    (geometricCoefficientFactor s sigma).natDegree≤
      (s.card-sigma)*(n+1-(s.card-sigma)) := by
  apply natDegree_sum_le_of_forall_le
  intro t ht
  have ht' := Finset.mem_powersetCard.mp ht
  have hb := nat_sum_le_triangle_add t n (fun i hi => hs i (ht'.1 hi))
  rw [ht'.2] at hb
  calc
    ((-1 : ℤ[X])^(s.card-sigma)*X^((∑i∈t,i)-
        (s.card-sigma)*(s.card-sigma-1)/2)).natDegree ≤
        ((-1 : ℤ[X])^(s.card-sigma)).natDegree+
          (X^((∑i∈t,i)-(s.card-sigma)*(s.card-sigma-1)/2) : ℤ[X]).natDegree :=
      natDegree_mul_le
    _ = (∑i∈t,i)-(s.card-sigma)*(s.card-sigma-1)/2 := by
      simp only [natDegree_pow,natDegree_neg,natDegree_one,mul_zero,
        natDegree_X,mul_one,zero_add]
    _ ≤ _ := by omega

/-- The exact factor and degree bound used for a row of the geometric Vandermonde inverse. -/
theorem geometricNumerator_factor (n : ℕ) (j : Fin (n+1)) (sigma : ℕ) (hsigma : sigma≤n) :
    ∃ P : ℤ[X],
      (∏ i∈Finset.univ.erase j,((X : (ℤ[X])[X])-C ((X:ℤ[X])^i.val))).coeff sigma =
        X^((n-sigma)*(n-sigma-1)/2)*P ∧
      P.natDegree≤(sigma+1)*(n-sigma) := by
  let s : Finset ℕ := (Finset.range (n+1)).erase j.val
  have hcard : s.card=n := by simp [s,Finset.mem_range.mpr j.isLt]
  have hs : ∀i∈s,i≤n := by
    intro i hi
    have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
    omega
  have hprod : (∏ i∈Finset.univ.erase j,((X : (ℤ[X])[X])-C ((X:ℤ[X])^i.val)))=
      ∏ i∈s,((X : (ℤ[X])[X])-C ((X:ℤ[X])^i)) := by
    refine Finset.prod_nbij Fin.val ?_ ?_ ?_ (fun _ _ => rfl)
    · intro i hi
      exact Finset.mem_erase.mpr ⟨(fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)),
        Finset.mem_range.mpr i.isLt⟩
    · exact Fin.val_injective.injOn
    · intro i hi
      have hir := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
      refine ⟨⟨i,hir⟩,?_,rfl⟩
      exact Finset.mem_erase.mpr ⟨(fun h => (Finset.mem_erase.mp hi).1 (congrArg Fin.val h)),
        Finset.mem_univ _⟩
  refine ⟨geometricCoefficientFactor s sigma,?_,?_⟩
  · rw [hprod]
    simpa only [geometricCoefficient,hcard] using
      geometricCoefficient_factor s sigma (hcard.symm ▸ hsigma)
  · have hb := geometricCoefficientFactor_natDegree_le s n sigma hs
    rw [hcard] at hb
    have he : n+1-(n-sigma)=sigma+1 := by omega
    simpa only [he,Nat.mul_comm] using hb
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometricCoefficient_factor
#print axioms WaringSiegel.WSL4Weil.geometricNumerator_factor

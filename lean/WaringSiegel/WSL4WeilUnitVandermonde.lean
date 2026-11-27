import WaringSiegel.WSL4WeilResidueNodes
import WaringSiegel.WSL4WeilVandermondeProjection
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 2000000

/-- Unit-denominator interpolation inside the actual relative coefficient ring. -/
theorem exists_relative_coefficient_affine_identity
    {B A : Type*} [CommRing B] [CommRing A] [IsDomain A] [IsLocalRing A]
    (p : ℕ) [CharP (ResidueField A) p] (f : B →+* A)
    (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀b : B,((residue A).comp f) b=0 ↔ (p:B)∣b)
    (P : ℕ) (U : Fin (P+1) → B)
    (hU : Function.Injective (fun j => residue A (f (U j))))
    (sigma : Fin (P+1)) :
    ∃ a : Fin (P+1) → A,
      (∀j,a j∈WSL4.relativePrimeCoefficientRing p f) ∧
      ∀x : A,(∑j,a j*(f (U j)*x+1)^P)=(P.choose sigma.val:A)*x^sigma.val := by
  let D : Fin (P+1) → B := fun j => ∏i∈Finset.univ.erase j,(U j-U i)
  let N : Fin (P+1) → B := fun j =>
    (∏i∈Finset.univ.erase j,((X:B[X])-C (U i))).coeff sigma.val
  have hDcop (j : Fin (P+1)) : IsCoprime (D j) (p:B) :=
    residue_distinct_node_denominator_coprime p ((residue A).comp f) hsurj hker P U hU j
  have hDunit (j : Fin (P+1)) : IsUnit (f (D j)) :=
    WSL4.relativePrimeCoefficient_map_isUnit p f (D j) (hDcop j)
  choose v hv using hDunit
  let a : Fin (P+1) → A := fun j => ((v j)⁻¹:Aˣ)*f (N j)
  have ha (j : Fin (P+1)) : a j∈WSL4.relativePrimeCoefficientRing p f :=
    (WSL4.relativePrimeCoefficientRing p f).mul_mem
      (WSL4.relativePrimeCoefficientRing_inverse_mem p f (D j) (hDcop j) (v j) (hv j))
      (WSL4.mem_relativePrimeCoefficientRing_map p f (N j))
  refine ⟨a,ha,?_⟩
  let F := FractionRing A
  let e : A →+* F := algebraMap A F
  let mu : Fin (P+1) → F := fun j => e (f (U j))
  have heinj : Function.Injective e := IsFractionRing.injective A F
  have hmu : Function.Injective mu := by
    intro i j hij
    apply hU
    exact congrArg (residue A) (heinj hij)
  have hrow (j : Fin (P+1)) : e (a j)=inverseVandermondeRow mu sigma j := by
    have hden : (∏i∈Finset.univ.erase j,(mu j-mu i))≠0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hi).1 (hmu h).symm)
    have hd : e (f (D j))=∏i∈Finset.univ.erase j,(mu j-mu i) := by
      simp only [D,map_prod,map_sub,mu]
    have hn : e (f (N j))=(∏i∈Finset.univ.erase j,((X:F[X])-C (mu i))).coeff sigma.val := by
      change ((e.comp f) ((∏i∈Finset.univ.erase j,((X:B[X])-C (U i))).coeff sigma.val))=_
      rw [← coeff_map]
      simp only [Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,RingHom.comp_apply,mu]
    rw [inverseVandermondeRow_formula]
    apply (eq_div_iff hden).mpr
    rw [← hd,← map_mul]
    calc
      e (a j*f (D j)) = e (f (N j)) := by
        congr 1
        dsimp [a]
        rw [← hv j]
        simp [mul_assoc,mul_left_comm,mul_comm]
      _ = _ := hn
  intro x
  apply heinj
  have hh := inverseVandermonde_affine_power_identity mu hmu sigma (e x)
  simpa only [map_sum,map_mul,map_add,map_one,map_pow,map_natCast,hrow,mu] using hh
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_relative_coefficient_affine_identity

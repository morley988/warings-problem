import WaringSiegel.WSL4WeilGeometricClearing
import WaringSiegel.WSL4WeilVandermondeProjection

noncomputable section
open Polynomial
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1500000

theorem map_geometric_numerator
    {R : Type*} [CommRing R] (e : ℤ[X] →+* R) (n : ℕ) (j : Fin (n+1)) (sigma : ℕ) :
    e ((∏ i∈Finset.univ.erase j,((X:(ℤ[X])[X])-C ((X:ℤ[X])^i.val))).coeff sigma)=
      (∏ i∈Finset.univ.erase j,((X:R[X])-C ((e X)^i.val))).coeff sigma := by
  rw [← coeff_map]
  simp only [Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_pow,
    Polynomial.map_X,Polynomial.map_C,map_pow]

theorem geometric_cleared_row_field
    {F : Type*} [Field F] (e : ℤ[X] →+* F) (n : ℕ)
    (hinj : Function.Injective (fun j : Fin (n+1) => (e X)^j.val))
    (j sigma : Fin (n+1)) (u : ℕ) (Q : ℤ[X])
    (hclear : (∏ i∈Finset.univ.erase j,((X:ℤ[X])^j.val-X^i.val))*(X^u*Q)=
      (X^n*WSL4Local.qFactorial n)^sigma.val*
        (∏ i∈Finset.univ.erase j,((X:(ℤ[X])[X])-C ((X:ℤ[X])^i.val))).coeff sigma.val) :
    e (X^u*Q)=e (X^n*WSL4Local.qFactorial n)^sigma.val*
      inverseVandermondeRow (fun i : Fin (n+1) => (e X)^i.val) sigma j := by
  have he := congrArg e hclear
  simp only [map_mul] at he
  rw [map_geometric_numerator e n j sigma.val] at he
  simp only [map_pow,map_prod,map_sub] at he
  have hden : (∏ i∈Finset.univ.erase j,((e X)^j.val-(e X)^i.val))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hi).1 (hinj h).symm)
  rw [inverseVandermondeRow_formula,← mul_div_assoc]
  apply (eq_div_iff hden).mpr
  simpa only [map_mul,map_pow,mul_comm] using he

/-- A universal integral affine-power identity with explicit coefficient degrees.
It is an identity over Z[Y][X], so specialization needs no denominator premise. -/
theorem exists_geometric_integral_power_identity
    (n sigma : ℕ) (hpos : 1≤sigma) (hsigma : sigma≤n) :
    ∃ u : Fin (n+1) → ℕ, ∃ Q : Fin (n+1) → ℤ[X],
      (∀j,u j+j.val*(j.val-1)/2+(n-j.val)*j.val=
        n*sigma+(n-sigma)*(n-sigma-1)/2 ∧
        (Q j).natDegree≤(sigma+1)*(n-sigma)+(sigma-1)*(n*(n+1)/2)+j.val*(n-j.val)) ∧
      (∑ j,C ((X:ℤ[X])^(u j)*Q j)*(C ((X:ℤ[X])^j.val)*(X:(ℤ[X])[X])+1)^n)=
        C ((n.choose sigma:ℤ[X])*(X^n*WSL4Local.qFactorial n)^sigma)*X^sigma := by
  choose u Q hu hdeg hclear using fun j : Fin (n+1) =>
    geometric_inverse_row_integral_polynomial n j sigma hpos hsigma
  refine ⟨u,Q,fun j => ⟨hu j,hdeg j⟩,?_⟩
  let F := FractionRing ℤ[X]
  let e : ℤ[X] →+* F := algebraMap ℤ[X] F
  let mu : Fin (n+1) → F := fun i => (e X)^i.val
  let s : Fin (n+1) := ⟨sigma,by omega⟩
  let L : ℤ[X] := X^n*WSL4Local.qFactorial n
  have heinj : Function.Injective e := IsFractionRing.injective ℤ[X] F
  have hinj : Function.Injective mu := by
    intro i j hij
    have hh : (X:ℤ[X])^i.val=X^j.val := heinj (by simpa only [map_pow] using hij)
    have hd := congrArg Polynomial.natDegree hh
    exact Fin.ext (by simpa only [natDegree_X_pow] using hd)
  have hc (j : Fin (n+1)) : e (X^(u j)*Q j)=(e L)^sigma*inverseVandermondeRow mu s j :=
    geometric_cleared_row_field e n hinj j s (u j) (Q j) (hclear j)
  have hp := inverseVandermonde_polynomial_projection mu hinj s ((X+1)^n)
    (by rw [← C_1,natDegree_pow,natDegree_X_add_C,mul_one])
  simp only [pow_comp,add_comp,X_comp,one_comp,coeff_X_add_one_pow] at hp
  change (∑j,C (inverseVandermondeRow mu s j)*(C (mu j)*X+1)^n)=
    C (n.choose sigma:F)*X^sigma at hp
  have hpoly : (∑j,C (e (X^(u j)*Q j))*(C (mu j)*X+1)^n)=
      C ((n.choose sigma:F)*(e L)^sigma)*X^sigma := by
    calc
      _ = C ((e L)^sigma)*(∑j,C (inverseVandermondeRow mu s j)*(C (mu j)*X+1)^n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hc,map_mul]
        ring
      _ = _ := by rw [hp,← mul_assoc,← C_mul,mul_comm ((e L)^sigma)]
  apply Polynomial.map_injective e heinj
  simpa only [Polynomial.map_sum,Polynomial.map_mul,map_C,Polynomial.map_pow,
    Polynomial.map_add,Polynomial.map_X,Polynomial.map_one,Polynomial.map_natCast,
    map_one,map_mul,map_pow,map_natCast,mu,L] using hpoly
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_geometric_integral_power_identity

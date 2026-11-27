import WaringSiegel.WSL4WeilGeometricNormalized
import WaringSiegel.WSL4MajorRamanujamPrincipalRoots

noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1500000

/-- Literal m-th powers after principal-unit lifting, with the same bounded
coefficient polynomials as the integral inverse Vandermonde identity. -/
theorem exists_geometric_power_coefficient_identity
    {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (p r k : ℕ) (hp : p.Prime) (hkr : k≤r)
    [CharP (ResidueField R) p] (n : ℕ) (hn : IsUnit (n:R))
    (pi : R) (hpi : residue R pi=0) :
    ∃ Q : Fin (p^r+1) → R[X],
      (∀j,(Q j).natDegree≤(p^k+1)*(p^r-p^k)+(p^k-1)*(p^r*(p^r+1)/2)+j.val*(p^r-j.val)) ∧
      (∀j i,(Q j).coeff i∈WSL4Local.rationalPrimeCoefficientRing p R) ∧
      ∀ x : R, ∃ z : Fin (p^r+1) → R,
      (∑j,(Q j).eval (pi^(n*p^r))*(z j)^(n*p^r))=
        (p:R)^(r-k)*(geometricRamanujamScale pi (n*p^r) (p^r))^(p^k)*x^(p^k) := by
  obtain ⟨u,Q,hdegree,hcoeff,hidentity⟩ := exists_geometric_normalized_power_identity
    p r k hp hkr pi (n*p^r)
  refine ⟨Q,fun j => (hdegree j).2,hcoeff,?_⟩
  intro x
  obtain ⟨y,hy⟩ := WSL4.principal_affine_power_family n (p^r) (n*p^r) hn pi x hpi
  refine ⟨fun j => pi^(u j)*y j,?_⟩
  calc
    (∑j,(Q j).eval (pi^(n*p^r))*(pi^(u j)*y j)^(n*p^r)) =
        ∑j,(pi^(u j))^(n*p^r)*(Q j).eval (pi^(n*p^r))*
          (pi^((n*p^r)*j.val+1)*x+1)^(p^r) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow,(hy j).1]
      ring
    _ = _ := hidentity x

/-- Every individual term in the deep truncated power ideal has a finite actual
m-th-power identity. The coefficient polynomials and their degrees are explicit. -/
theorem exists_maximal_power_coefficient_identity
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (p r k : ℕ) (hp : p.Prime) (hkr : k≤r)
    [CharP (ResidueField R) p] (n : ℕ) (hn : 0<n) (hnu : IsUnit (n:R))
    {pi : R} (hpi : Irreducible pi) (w : R)
    (hw : w∈(maximalIdeal R)^((n*p^r)*p^r+1)) :
    ∃ Q : Fin (p^r+1) → R[X], ∃ z : Fin (p^r+1) → R,
      (∀j,(Q j).natDegree≤(p^k+1)*(p^r-p^k)+(p^k-1)*(p^r*(p^r+1)/2)+j.val*(p^r-j.val)) ∧
      (∀j i,(Q j).coeff i∈WSL4Local.rationalPrimeCoefficientRing p R) ∧
      (∑j,(Q j).eval (pi^(n*p^r))*(z j)^(n*p^r))=(p:R)^(r-k)*w^(p^k) := by
  have hm : 0<n*p^r := Nat.mul_pos hn (pow_pos hp.pos _)
  have hpimem : pi∈maximalIdeal R := hpi.not_isUnit
  have hpires : residue R pi=0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hpimem
  obtain ⟨Q,hdegree,hcoeff,hidentity⟩ := exists_geometric_power_coefficient_identity
    p r k hp hkr n hnu pi hpires
  obtain ⟨x,hx⟩ := (mem_maximalIdeal_power_iff_geometricScale_dvd hpi (n*p^r) (p^r) hm w).mp hw
  obtain ⟨z,hz⟩ := hidentity x
  refine ⟨Q,z,hdegree,hcoeff,?_⟩
  rw [hx,mul_pow]
  simpa only [mul_assoc] using hz
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_geometric_power_coefficient_identity
#print axioms WaringSiegel.WSL4Weil.exists_maximal_power_coefficient_identity

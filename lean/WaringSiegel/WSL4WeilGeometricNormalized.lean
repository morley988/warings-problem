import WaringSiegel.WSL4WeilGeometricScale
import WaringSiegel.WSL4MajorRamanujamBinomialInverse

noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1500000

/-- The exact binomial unit is removed inside the rational prime-integral
coefficient subring. Every polynomial keeps the original degree bound. -/
theorem exists_geometric_normalized_power_identity
    {R : Type*} [CommRing R] [IsLocalRing R]
    (p r k : ℕ) (hp : p.Prime) (hkr : k≤r)
    [CharP (ResidueField R) p] (pi : R) (m : ℕ) :
    ∃ u : Fin (p^r+1) → ℕ, ∃ Q : Fin (p^r+1) → R[X],
      (∀j,u j+j.val*(j.val-1)/2+(p^r-j.val)*j.val=
        p^r*p^k+(p^r-p^k)*(p^r-p^k-1)/2 ∧
        (Q j).natDegree≤(p^k+1)*(p^r-p^k)+(p^k-1)*(p^r*(p^r+1)/2)+j.val*(p^r-j.val)) ∧
      (∀j i,(Q j).coeff i∈WSL4Local.rationalPrimeCoefficientRing p R) ∧
      ∀ x : R,
      (∑ j,(pi^(u j))^m*(Q j).eval (pi^m)*
        (pi^(m*j.val+1)*x+1)^(p^r))=
        (p:R)^(r-k)*(geometricRamanujamScale pi m (p^r))^(p^k)*x^(p^k) := by
  have hpos : 1≤p^k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.ne_zero)
  have hle : p^k≤p^r := Nat.pow_le_pow_right hp.one_le hkr
  obtain ⟨u,Q,hdegree,hidentity⟩ := exists_geometric_uniformizer_power_identity
    pi m (p^r) (p^k) hpos hle
  obtain ⟨v,hv,hchoose⟩ := WSL4.prime_power_choose_normalizing_unit (A:=R) p r k hp hkr
  let A : Fin (p^r+1) → R[X] := fun j => C (v:R)*(Q j).map (Int.castRingHom R)
  have hA (j : Fin (p^r+1)) := WSL4.normalized_integer_polynomial_coefficients
    p (v:R) hv (Q j)
  refine ⟨u,A,fun j => ⟨(hdegree j).1,(hA j).2.trans (hdegree j).2⟩,
    fun j i => (hA j).1 i,?_⟩
  intro x
  calc
    (∑j,(pi^(u j))^m*(A j).eval (pi^m)*(pi^(m*j.val+1)*x+1)^(p^r)) =
        (v:R)*(∑j,(pi^(u j))^m*(Q j).eval₂ (Int.castRingHom R) (pi^m)*
          (pi^(m*j.val+1)*x+1)^(p^r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [A,eval_mul,eval_C,eval_map]
      ring
    _ = (p:R)^(r-k)*(geometricRamanujamScale pi m (p^r))^(p^k)*x^(p^k) := by
      rw [hidentity]
      calc
        _ = ((v:R)*((p^r).choose (p^k):R))*
            (geometricRamanujamScale pi m (p^r))^(p^k)*x^(p^k) := by ring
        _ = _ := by rw [hchoose]
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_geometric_normalized_power_identity

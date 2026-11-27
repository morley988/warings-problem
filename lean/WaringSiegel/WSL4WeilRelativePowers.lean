import WaringSiegel.WSL4WeilUnitVandermonde
import WaringSiegel.WSL4MajorRamanujamRelativeUnits
import WaringSiegel.WSL4MajorRamanujamPrincipalRoots

noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 2000000

/-- A deep power-ideal term in the large-residue branch is an actual sum of
P+1 coefficient-weighted m-th powers, with coefficients in the actual monogenic
relative ring. No coefficient-field embedding is required. -/
theorem exists_relative_maximal_power_identity
    {B A : Type*} [CommRing B] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    (p r k : ℕ) (hp : p.Prime) (hkr : k≤r)
    [CharP (ResidueField A) p] (n : ℕ) (hn : IsUnit (n:A))
    (f : B →+* A) (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀b : B,((residue A).comp f) b=0 ↔ (p:B)∣b)
    (hcard : p^r<Nat.card (ResidueField A)) (w : A) (hw : w∈maximalIdeal A) :
    ∃ c z : Fin (p^r+1) → A,
      (∀j,c j∈WSL4.relativePrimeCoefficientRing p f) ∧
      (∑j,c j*(z j)^(n*p^r))=(p:A)^(r-k)*w^(p^k) := by
  obtain ⟨U,hU⟩ := exists_residue_distinct_nodes ((residue A).comp f) hsurj (p^r) hcard
  let sigma : Fin (p^r+1) := ⟨p^k,by
    have := Nat.pow_le_pow_right hp.one_le hkr
    omega⟩
  obtain ⟨a,ha,hidentity⟩ := exists_relative_coefficient_affine_identity
    p f hsurj hker (p^r) U hU sigma
  obtain ⟨v,hv,hchoose⟩ := WSL4.prime_power_choose_normalizing_unit (A:=A) p r k hp hkr
  have hvrel : (v:A)∈WSL4.relativePrimeCoefficientRing p f :=
    WSL4.rationalPrimeCoefficientRing_le_relativePrimeCoefficientRing p f hv
  have hwr : residue A w=0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hw
  have hroot (j : Fin (p^r+1)) : ∃z : A,z^(n*p^r)=(f (U j)*w+1)^(p^r) := by
    obtain ⟨z,hz,-,-⟩ := WSL4.principal_unit_tame_root n hn (f (U j)*w)
      (by rw [map_mul,hwr,mul_zero])
    refine ⟨z,?_⟩
    rw [pow_mul,hz,add_comm (1:A)]
  choose z hz using hroot
  refine ⟨fun j => (v:A)*a j,z,fun j =>
    (WSL4.relativePrimeCoefficientRing p f).mul_mem hvrel (ha j),?_⟩
  calc
    (∑j,((v:A)*a j)*(z j)^(n*p^r)) =
        (v:A)*(∑j,a j*(f (U j)*w+1)^(p^r)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hz]
      ring
    _ = (p:A)^(r-k)*w^(p^k) := by
      rw [hidentity]
      change (v:A)*(((p^r).choose (p^k):A)*w^(p^k))=_
      rw [← mul_assoc,hchoose]
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.exists_relative_maximal_power_identity

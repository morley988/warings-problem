import WaringLinear.QuotientUnitCorrections

/-! # Compression of principal-unit deviations into a fixed coefficient basis -/
namespace WaringLinear
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- Suppose each residue-unit coefficient is an integer linear combination of
a fixed family of kth-power coefficients. Then all scaled deviations can be
represented using one principal-unit correction at each basis coefficient. -/
theorem deviations_on_basis {α β : Type*} [Fintype α] [Fintype β]
    (I : Ideal R) (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ)
    (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I) (v : α → Rˣ) (hv : ∀ j, v j ∈ H)
    (b : β → Rˣ) (z : α → R) (c : α → β → ℤ)
    (hc : ∀ j, z j = ∑ i, (c j i:R)*(b i:R)^k) :
    ∃ w : β → Rˣ, (∀ i, w i ∈ H) ∧
      (∑ j, z j*((v j:R)^k-1)) = ∑ i, (b i:R)^k*((w i:R)^k-1) := by
  classical
  have hrep (i : β) : ∃ w ∈ H, (w:R)^k-1 = ∑ j, c j i • ((v j:R)^k-1) :=
    linear_combination_deviations_one_power Finset.univ I hI H k hH v
      (fun j _ => hv j) (fun j => c j i)
  choose w hw he using hrep
  refine ⟨w,hw,?_⟩
  simp_rw [hc,Finset.sum_mul,he,Finset.mul_sum,zsmul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-- Each correction costs one unit summand once the basis constants have been
subtracted. This is the finite-ring step before the local lifting theorem. -/
theorem realize_deviations_with_basis_units {α β : Type*} [Fintype α] [Fintype β]
    (I : Ideal R) (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ)
    (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I) (v : α → Rˣ) (hv : ∀ j, v j ∈ H)
    (b : β → Rˣ) (z : α → R) (c : α → β → ℤ)
    (hc : ∀ j, z j = ∑ i, (c j i:R)*(b i:R)^k) :
    ∃ y : β → Rˣ, (∑ i, (y i:R)^k) =
      (∑ i, (b i:R)^k) + ∑ j, z j*((v j:R)^k-1) := by
  obtain ⟨w,_,hw⟩ := deviations_on_basis I hI H k hH v hv b z c hc
  refine ⟨fun i => b i*w i,?_⟩
  rw [hw,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by push_cast; ring)

#print axioms deviations_on_basis
#print axioms realize_deviations_with_basis_units
end WaringLinear

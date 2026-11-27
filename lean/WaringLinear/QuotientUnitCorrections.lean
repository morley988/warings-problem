import WaringLinear.SquareZeroUnits
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Additive corrections by actual powers in finite-precision quotients -/
namespace WaringLinear
variable {R : Type*} [CommRing R]

/-- In R/P^b the image of P^r has square zero whenever b≤2r. -/
theorem quotient_layer_squareZero (P : Ideal R) (b r : ℕ) (h : b ≤ 2*r) :
    (P^r).map (Ideal.Quotient.mk (P^b)) * (P^r).map (Ideal.Quotient.mk (P^b)) = ⊥ := by
  rw [← Ideal.map_mul,← pow_add,Ideal.map_eq_bot_iff_le_ker,Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

/-- The actual set of deviations v^k-1, as v varies over H, as an additive subgroup. -/
def kthPowerDeviations (I : Ideal R) (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ)
    (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I) : AddSubgroup R :=
  unitDeviations I hI (H.map (powMonoidHom k)) (by
    rintro u ⟨v,hv,rfl⟩
    exact_mod_cast hH v hv)

/-- Membership identifies the additive correction with a kth power from H. -/
theorem mem_kthPowerDeviations_iff (I : Ideal R) (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ)
    (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I) (z : R) :
    z ∈ kthPowerDeviations I hI H k hH ↔ ∃ v ∈ H, (v:R)^k-1=z := by
  constructor
  · rintro ⟨u,⟨v,hv,rfl⟩,heq⟩
    exact ⟨v,hv,by simpa using heq⟩
  · rintro ⟨v,hv,heq⟩
    exact ⟨v^k,⟨v,hv,rfl⟩,by simpa using heq⟩

/-- An arbitrary finite sum of deviations from the same principal-unit
subgroup already comes from one kth power in that subgroup. -/
theorem sum_deviations_one_power {ι : Type*} (s : Finset ι) (I : Ideal R)
    (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ) (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I)
    (v : ι → Rˣ) (hv : ∀ i ∈ s, v i ∈ H) :
    ∃ w ∈ H, (w:R)^k-1 = ∑ i ∈ s, ((v i:R)^k-1) := by
  apply (mem_kthPowerDeviations_iff I hI H k hH _).mp
  apply AddSubgroup.sum_mem
  intro i hi
  exact (mem_kthPowerDeviations_iff I hI H k hH _).mpr ⟨v i,hv i hi,rfl⟩

/-- Arbitrary integer coefficients are absorbed into one principal-unit correction. -/
theorem linear_combination_deviations_one_power {ι : Type*} (s : Finset ι) (I : Ideal R)
    (hI : I*I=⊥) (H : Subgroup Rˣ) (k : ℕ) (hH : ∀ v ∈ H, (v:R)^k-1 ∈ I)
    (v : ι → Rˣ) (hv : ∀ i ∈ s, v i ∈ H) (c : ι → ℤ) :
    ∃ w ∈ H, (w:R)^k-1 = ∑ i ∈ s, c i • ((v i:R)^k-1) := by
  apply (mem_kthPowerDeviations_iff I hI H k hH _).mp
  apply AddSubgroup.sum_mem
  intro i hi
  apply AddSubgroup.zsmul_mem
  exact (mem_kthPowerDeviations_iff I hI H k hH _).mpr ⟨v i,hv i hi,rfl⟩

#print axioms quotient_layer_squareZero
#print axioms sum_deviations_one_power
#print axioms linear_combination_deviations_one_power
end WaringLinear

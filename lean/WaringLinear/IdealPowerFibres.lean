import WaringLinear.FiniteGram
import WaringSiegel.WSL3MomentLocalPowerGood
import WaringSiegel.WSL2LocalGlobalKernel
import Mathlib.Algebra.Group.Pi.Units

/-! # Small-conductor power fibres over ideals

For ideals coprime to k, the unit kth-power map has at most k choices per
prime ideal, independently of the multiplicities of the prime ideals.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open IsLocalRing UniqueFactorizationMonoid
open scoped NumberField BigOperators Classical
open WaringSiegel WaringSiegel.WSL2 WaringSiegel.WSL3

namespace WaringLinear

def unitRootsCount (A : Type*) [Monoid A] (k : ℕ) : ℕ :=
  Nat.card {u : Aˣ // u^k = 1}

theorem unitRootsCount_congr {A B : Type*} [Monoid A] [Monoid B]
    (e : A ≃* B) (k : ℕ) : unitRootsCount A k = unitRootsCount B k := by
  apply Nat.card_congr
  let f := Units.mapEquiv e
  exact f.toEquiv.subtypeEquiv (fun u => by
    change u^k = 1 ↔ f u ^k = 1
    rw [← map_pow, ← map_one f, f.injective.eq_iff])

theorem unitRootsCount_pi {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, Monoid (A i)] (k : ℕ) :
    unitRootsCount (∀ i, A i) k = ∏ i, unitRootsCount (A i) k := by
  let f : (∀ i, A i)ˣ ≃* ∀ i, (A i)ˣ := MulEquiv.piUnits
  let e : {u : (∀ i, A i)ˣ // u^k = 1} ≃
      {g : ∀ i, (A i)ˣ // ∀ i, g i ^k = 1} := f.toEquiv.subtypeEquiv (fun u => by
    change u^k = 1 ↔ ∀ i, f u i ^k = 1
    rw [← f.injective.eq_iff, map_pow, map_one, funext_iff]
    rfl)
  exact (Nat.card_congr (e.trans (Equiv.subtypePiEquivPi (p := fun i (u : (A i)ˣ) => u^k = 1)))).trans Nat.card_pi

theorem local_unitRootsCount_le {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) (k : ℕ) (hk : 0 < k)
    (hku : IsUnit (k : R)) : unitRootsCount (R ⧸ I) k ≤ k := by
  let π := localResidueReduction I hI
  let f : {u : (R ⧸ I)ˣ // u ^ k = 1} →
      (Polynomial.nthRootsFinset k (1 : ResidueField R)) :=
    fun u => ⟨π u.val, (Polynomial.mem_nthRootsFinset hk 1).mpr (by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, u.property, Units.val_one, map_one])⟩
  have hf : Function.Injective f := by
    intro u v h
    have hr : π u.val = π v.val := congrArg Subtype.val h
    have hru : π u.val ≠ 0 := (u.val.isUnit.map π).ne_zero
    apply Subtype.ext
    apply Units.ext
    apply (power_eq_iff_of_same_nonzero_residue k hk hku I hI hr hru).mp
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, u.property, v.property]
  apply (Nat.card_le_card_of_injective f hf).trans
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

variable {K : Type*} [Field K] [NumberField K]

theorem prime_power_unitRootsCount_le
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (e k : ℕ) (he : e ≠ 0) (hk : 0 < k) (hv : (k : 𝓞 K) ∉ v.asIdeal) :
    unitRootsCount (𝓞 K ⧸ v.asIdeal ^ e) k ≤ k := by
  rw [unitRootsCount_congr (primePowerCompletionEquiv v e).toMulEquiv]
  apply local_unitRootsCount_le _ (Ideal.pow_le_self he) _ hk
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_natCast] using not_congr (completion_residue_natCast_eq_zero_iff v k) |>.mpr hv

theorem ideal_unitRootsCount_factorization (I : Ideal (𝓞 K)) (hI : I ≠ 0) (k : ℕ) :
    unitRootsCount (𝓞 K ⧸ I) k = ∏ P ∈ (normalizedFactors I).toFinset,
      unitRootsCount (𝓞 K ⧸ P^(normalizedFactors I).count P) k := by
  let S := (normalizedFactors I).toFinset
  let e : (𝓞 K ⧸ I) ≃+* ∀ P : S, 𝓞 K ⧸ P.val ^ (normalizedFactors I).count P.val :=
    IsDedekindDomain.quotientEquivPiOfFinsetProdEq I id
      (fun P => (normalizedFactors I).count P)
      (fun P hP => prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
      (fun P _ Q _ h => h) (by
        rw [← Finset.prod_multiset_map_count, Multiset.map_id, prod_normalizedFactors_eq_self hI])
  rw [unitRootsCount_congr e.toMulEquiv, unitRootsCount_pi]
  exact Finset.prod_coe_sort S (fun P => unitRootsCount (𝓞 K ⧸ P^(normalizedFactors I).count P) k)

/-- The dependence on the number of prime ideals of the modulus is explicit.
The hypothesis holds for every modulus supported away from k. -/
theorem ideal_unitRootsCount_le (I : Ideal (𝓞 K)) (hI : I ≠ 0) (k : ℕ) (hk : 0 < k)
    (hgood : ∀ P ∈ (normalizedFactors I).toFinset, (k : 𝓞 K) ∉ P) :
    unitRootsCount (𝓞 K ⧸ I) k ≤ k^(normalizedFactors I).toFinset.card := by
  rw [ideal_unitRootsCount_factorization I hI k, ← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro P hP
  have hp := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  exact prime_power_unitRootsCount_le (normalizedFactorCompletionPrime P hp) _ k
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hP)).ne' hk (hgood P hP)

#print axioms local_unitRootsCount_le
#print axioms ideal_unitRootsCount_le

end WaringLinear

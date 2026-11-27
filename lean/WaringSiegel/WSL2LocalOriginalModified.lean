import WaringSiegel.WSL2LocalAuxiliaryPrime

/-!
# Restricted local densities in original prime-power quotient rings

These are literal tuples modulo the original number-field ideal powers,
with the four coprimality conditions expressed by IsUnit in the quotient.
The canonical completion comparison identifies their normalized counts with
the modified factors occurring in the proved uniform Euler product.
-/

noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical

namespace WaringSiegel

def RestrictedCubicSolutions
    (R : Type*) [CommRing R] (I : Ideal R) (p a : R) :=
  {z : (Fin 4 → R ⧸ I) × (Fin 4 → R ⧸ I) //
    (∑ i, z.2 i ^ 3) + (∑ i, (Ideal.Quotient.mk I p * z.1 i) ^ 3) =
      Ideal.Quotient.mk I a ∧ ∀ i, IsUnit (z.2 i)}

def restrictedCubicSolutionsCongr
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (p a : R) (p' a' : S)
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (hp : e (Ideal.Quotient.mk I p) = Ideal.Quotient.mk J p')
    (ha : e (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J a') :
    RestrictedCubicSolutions R I p a ≃ RestrictedCubicSolutions S J p' a' where
  toFun z := ⟨(fun i => e (z.val.1 i), fun i => e (z.val.2 i)), by
    constructor
    · simpa only [map_add, map_sum, map_pow, map_mul, hp] using
        (congrArg e z.property.1).trans ha
    · exact fun i => (z.property.2 i).map e.toRingHom⟩
  invFun z := ⟨(fun i => e.symm (z.val.1 i), fun i => e.symm (z.val.2 i)), by
    constructor
    · apply e.injective
      simpa only [map_add, map_sum, map_pow, map_mul, e.apply_symm_apply, hp, ha] using
        z.property.1
    · exact fun i => (z.property.2 i).map e.symm.toRingHom⟩
  left_inv z := by apply Subtype.ext; apply Prod.ext <;> funext i <;> exact e.symm_apply_apply _
  right_inv z := by apply Subtype.ext; apply Prod.ext <;> funext i <;> exact e.apply_symm_apply _

def restrictedCubicSolutionsEquivModified
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R) (p a : R) :
    RestrictedCubicSolutions R I p a ≃ ModifiedLocalCubicSolutions R I hI p a where
  toFun z := ⟨z.val, z.property.1, fun i =>
    (localResidueReduction_ne_zero_iff_isUnit I hI _).mpr (z.property.2 i)⟩
  invFun z := ⟨z.val, z.property.1, fun i =>
    (localResidueReduction_ne_zero_iff_isUnit I hI _).mp (z.property.2 i)⟩
  left_inv z := by apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable {K : Type*} [Field K] [NumberField K]

theorem original_restricted_cubic_count_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p ν : 𝓞 K) (n : ℕ) :
    Nat.card (RestrictedCubicSolutions (𝓞 K) (v.asIdeal ^ (n + 1)) p ν) =
      Nat.card (ModifiedLocalCubicSolutions (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K) ^ (n + 1))
        (Ideal.pow_le_self (Nat.succ_ne_zero n))
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) := by
  apply Nat.card_congr
  exact (restrictedCubicSolutionsCongr _ _ _ _ _ _
    (primePowerCompletionEquiv v (n + 1)) rfl rfl).trans
      (restrictedCubicSolutionsEquivModified _ _ _ _)

def normalizedOriginalRestrictedCubicCount
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p ν : 𝓞 K) (n : ℕ) : ℝ :=
  (Nat.card (RestrictedCubicSolutions (𝓞 K) (v.asIdeal ^ (n + 1)) p ν) : ℝ) /
    (Ideal.absNorm v.asIdeal : ℝ) ^ (7 * (n + 1))

theorem normalizedOriginalRestrictedCubicCount_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p ν : 𝓞 K) (n : ℕ) :
    normalizedOriginalRestrictedCubicCount v p ν n =
      normalizedModifiedLocalCubicCount (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) p)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) n := by
  unfold normalizedOriginalRestrictedCubicCount normalizedModifiedLocalCubicCount
  rw [original_restricted_cubic_count_eq_completion, completion_residue_card_eq_absNorm]

/-- At every positive precision, the original restricted count equals the
modified Euler factor, including its unit-density baseline. -/
theorem normalizedOriginalRestrictedCubicCount_eq_factor
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) {p : 𝓞 K} (hp : p ∈ v.asIdeal)
    (ν : 𝓞 K) (n : ℕ) :
    normalizedOriginalRestrictedCubicCount v p ν n = cubicModifiedResidueFactor v ν := by
  rw [normalizedOriginalRestrictedCubicCount_eq_completion]
  exact (cubicModifiedResidueFactor_eq_normalized_count v h6 hp ν n).symm

theorem original_restricted_cubic_count_tendsto
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) {p : 𝓞 K} (hp : p ∈ v.asIdeal) (ν : 𝓞 K) :
    Tendsto (normalizedOriginalRestrictedCubicCount v p ν) atTop
      (𝓝 (cubicModifiedResidueFactor v ν)) := by
  have heq : normalizedOriginalRestrictedCubicCount v p ν =
      fun _ : ℕ => cubicModifiedResidueFactor v ν := by
    funext n
    exact normalizedOriginalRestrictedCubicCount_eq_factor v h6 hp ν n
  rw [heq]
  exact tendsto_const_nhds

theorem original_restricted_cubic_count_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 24576 ≤ Ideal.absNorm v.asIdeal)
    {p : 𝓞 K} (hp : p ∈ v.asIdeal) (ν : 𝓞 K) (n : ℕ) :
    (1 / 2 : ℝ) ≤ normalizedOriginalRestrictedCubicCount v p ν n := by
  rw [normalizedOriginalRestrictedCubicCount_eq_factor v h6 hp]
  exact cubicModifiedResidueFactor_lower v h6 hq ν

end WaringSiegel

#print axioms WaringSiegel.normalizedOriginalRestrictedCubicCount_eq_factor
#print axioms WaringSiegel.original_restricted_cubic_count_lower

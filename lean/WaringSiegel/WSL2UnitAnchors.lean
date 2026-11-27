import WaringSiegel.WSL2UnitCompact
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Actual archimedean anchors for the normalized equation

Roots are constructed in the real and complex coordinates of the mixed
archimedean space. Positive real roots and nonzero complex roots give a
nonsingular first-variable block of the Waring map. The inverse function
theorem then gives genuine open neighborhoods of representable targets.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- Positivity of all real coordinates of an archimedean point. -/
def MixedPositive (b : mixedSpace K) : Prop :=
  ∀ w : {w : InfinitePlace K // IsReal w}, 0 < b.1 w

/-- Positive real roots and arbitrary complex roots give an actual mixed root. -/
theorem exists_mixed_positive_root (k : ℕ) (hk : 0 < k)
    (b : mixedSpace K) (hb : MixedPositive b) :
    ∃ a : mixedSpace K, a ^ k = b ∧ MixedPositive a := by
  let r : {w : InfinitePlace K // IsReal w} → ℝ :=
    fun w => b.1 w ^ (1 / (k : ℝ))
  let c : {w : InfinitePlace K // IsComplex w} → ℂ :=
    fun w => Classical.choose (IsAlgClosed.exists_pow_nat_eq (b.2 w) hk)
  refine ⟨(r, c), ?_, ?_⟩
  · apply Prod.ext
    · funext w
      simpa only [r, one_div] using Real.rpow_inv_natCast_pow (hb w).le hk.ne'
    · funext w
      exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (b.2 w) hk)
  · intro w
    exact Real.rpow_pos_of_pos (hb w) _

/-- A mixed point is a unit precisely when no archimedean coordinate vanishes. -/
theorem mixed_isUnit_iff (a : mixedSpace K) :
    IsUnit a ↔ ∀ w : InfinitePlace K, normAtPlace w a ≠ 0 := by
  constructor
  · intro ha w
    exact (ha.map (normAtPlace w)).ne_zero
  · intro h
    apply isUnit_iff_exists_inv.mpr
    refine ⟨((fun w => (a.1 w)⁻¹), (fun w => (a.2 w)⁻¹)), ?_⟩
    apply Prod.ext
    · funext w
      apply mul_inv_cancel₀
      exact norm_ne_zero_iff.mp (by simpa only [normAtPlace_apply_of_isReal w.property] using h w)
    · funext w
      apply mul_inv_cancel₀
      exact norm_ne_zero_iff.mp (by simpa only [normAtPlace_apply_of_isComplex w.property] using h w)

/-- The normalized equation has an equal-coordinate anchor with positive real
coordinates and a nonzero coordinate at every infinite place. -/
theorem exists_mixed_waring_anchor (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (b : mixedSpace K) (hb : MixedPositive b)
    (hbnz : ∀ w : InfinitePlace K, normAtPlace w b ≠ 0) :
    ∃ a : mixedSpace K, (∑ _i : Fin s, a ^ k) = b ∧ MixedPositive a ∧ IsUnit a ∧
      a ^ k = (s : ℝ)⁻¹ • b := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hb' : MixedPositive ((s : ℝ)⁻¹ • b) := by
    intro w
    exact mul_pos (inv_pos.mpr hsR) (hb w)
  obtain ⟨a, ha, hapos⟩ := exists_mixed_positive_root k hk ((s : ℝ)⁻¹ • b) hb'
  refine ⟨a, ?_, hapos, ?_, ha⟩
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      ha, smul_smul, mul_inv_cancel₀ hsR.ne', one_smul]
  · apply (mixed_isUnit_iff a).mpr
    intro w
    have he : normAtPlace w a ^ k = (s : ℝ)⁻¹ * normAtPlace w b := by
      rw [← map_pow, ha, normAtPlace_smul, abs_of_pos (inv_pos.mpr hsR)]
    intro hz
    rw [hz, zero_pow hk.ne'] at he
    exact (mul_ne_zero (inv_ne_zero hsR.ne') (hbnz w)) he.symm

/-- Each anchor has exactly the coordinate magnitudes dictated by the
normalized target. -/
theorem mixed_anchor_magnitude {k s : ℕ} (hk : 0 < k) (hs : 0 < s)
    {a b : mixedSpace K} (ha : a ^ k = (s : ℝ)⁻¹ • b) (w : InfinitePlace K) :
    normAtPlace w a = ((s : ℝ)⁻¹ * normAtPlace w b) ^ (1 / (k : ℝ)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have he : normAtPlace w a ^ k = (s : ℝ)⁻¹ * normAtPlace w b := by
    rw [← map_pow, ha, normAtPlace_smul, abs_of_pos (inv_pos.mpr hsR)]
  rw [← he, one_div, Real.pow_rpow_inv_natCast (normAtPlace_nonneg _ _) hk.ne']

/-- The first-variable derivative block is a unit of the actual mixed algebra. -/
theorem mixed_pow_derivative_isUnit (k : ℕ) (hk : 0 < k)
    (a : mixedSpace K) (ha : IsUnit a) : IsUnit (k • a ^ (k - 1)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hcast : IsUnit (k : mixedSpace K) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hkR).map (algebraMap ℝ (mixedSpace K))
  simpa only [nsmul_eq_mul] using hcast.mul (ha.pow (k - 1))

/-- The inverse function theorem applies to the literal coordinatewise power
map at every mixed unit. This is local openness, without an analytic premise. -/
theorem mixed_pow_map_nhds (k : ℕ) (hk : 0 < k) (a : mixedSpace K) (ha : IsUnit a) :
    Filter.map (fun x : mixedSpace K => x ^ k) (nhds a) = nhds (a ^ k) := by
  have hderiv := hasStrictFDerivAt_pow (𝕜 := ℝ) (x := a) k
  apply hderiv.map_nhds_eq_of_surj
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨x, hx⟩ := (IsUnit.isUnit_iff_mulLeft_bijective.mp
    (mixed_pow_derivative_isUnit k hk a ha)).surjective y
  exact ⟨x, hx⟩

/-- Fixing the other Waring variables preserves the nonsingular local chart. -/
theorem shifted_mixed_pow_map_nhds (k : ℕ) (hk : 0 < k)
    (a c : mixedSpace K) (ha : IsUnit a) :
    Filter.map (fun x : mixedSpace K => x ^ k + c) (nhds a) = nhds (a ^ k + c) := by
  have hderiv := (hasStrictFDerivAt_pow (𝕜 := ℝ) (x := a) k).add_const c
  apply hderiv.map_nhds_eq_of_surj
  apply LinearMap.range_eq_top.mpr
  intro y
  obtain ⟨x, hx⟩ := (IsUnit.isUnit_iff_mulLeft_bijective.mp
    (mixed_pow_derivative_isUnit k hk a ha)).surjective y
  exact ⟨x, hx⟩

/-- Every sufficiently small open box about the nonsingular anchor covers
an open neighborhood of its target while the other variables remain fixed. -/
theorem shifted_mixed_pow_image_mem_nhds (k : ℕ) (hk : 0 < k)
    (a c : mixedSpace K) (ha : IsUnit a) {U : Set (mixedSpace K)} (hU : U ∈ nhds a) :
    (fun x : mixedSpace K => x ^ k + c) '' U ∈ nhds (a ^ k + c) := by
  rw [← shifted_mixed_pow_map_nhds k hk a c ha]
  exact Filter.image_mem_map hU

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_mixed_waring_anchor
#print axioms WaringSiegel.WSL2.mixed_pow_map_nhds

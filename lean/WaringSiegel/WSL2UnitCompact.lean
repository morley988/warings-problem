import WaringSiegel.WSL2UnitBalancing

/-!
# A fixed compact set of normalized Waring–Siegel targets

For each field and exponent, a totally positive unit kth power sends every
nonzero totally positive algebraic-integer target into one compact subset of
the actual mixed archimedean space after the manuscript's norm scaling.
The set is separated from zero at every embedding and stays in the real
positive cone. No target-dependent compactness constant is assumed.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- The geometric mean of the archimedean magnitudes. -/
def normScale (ν : 𝓞 K) : ℝ := absNorm ν ^ (1 / (Module.finrank ℚ K : ℝ))

/-- The manuscript's root scale P = |Nν|^(1/(dk)). -/
def rootScale (k : ℕ) (ν : 𝓞 K) : ℝ :=
  absNorm ν ^ (1 / ((Module.finrank ℚ K : ℝ) * (k : ℝ)))

theorem normScale_pos {ν : 𝓞 K} (hν : ν ≠ 0) : 0 < normScale ν := by
  apply Real.rpow_pos_of_pos
  rw [← fieldAbsNorm_integer]
  exact fieldAbsNorm_pos (by exact_mod_cast hν)

theorem rootScale_pos {ν : 𝓞 K} (hν : ν ≠ 0) (k : ℕ) : 0 < rootScale k ν := by
  apply Real.rpow_pos_of_pos
  rw [← fieldAbsNorm_integer]
  exact fieldAbsNorm_pos (by exact_mod_cast hν)

theorem rootScale_pow (k : ℕ) (hk : 0 < k) (ν : 𝓞 K) :
    rootScale k ν ^ k = normScale ν := by
  unfold rootScale normScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (absNorm_nonneg ν)]
  congr 1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  field_simp

theorem normScale_pow_degree (ν : 𝓞 K) :
    normScale ν ^ Module.finrank ℚ K = absNorm ν := by
  simpa only [normScale, one_div] using
    (Real.rpow_inv_natCast_pow (x := absNorm ν) (n := Module.finrank ℚ K)
      (absNorm_nonneg ν) (Module.finrank_pos (R := ℚ) (M := K)).ne')

/-- Multiplication by the unit kth power, followed by division by P^k. -/
def normalizedTarget (k : ℕ) (u : (𝓞 K)ˣ) (ν : 𝓞 K) : mixedEmbedding.mixedSpace K :=
  (normScale ν)⁻¹ • mixedEmbedding K (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K)

theorem normalizedTarget_eq_rootScale (k : ℕ) (hk : 0 < k)
    (u : (𝓞 K)ˣ) (ν : 𝓞 K) :
    normalizedTarget k u ν = (rootScale k ν ^ k)⁻¹ •
      mixedEmbedding K (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) := by
  rw [rootScale_pow k hk]
  rfl

theorem mixedNorm_integer (ν : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K (ν : K)) = absNorm ν := by
  rw [mixedEmbedding.norm_eq_norm]
  simpa only [fieldAbsNorm, Rat.cast_abs] using fieldAbsNorm_integer ν

theorem normalizedTarget_norm (k : ℕ) (u : (𝓞 K)ˣ) {ν : 𝓞 K} (hν : ν ≠ 0) :
    mixedEmbedding.norm (normalizedTarget k u ν) = 1 := by
  have hs : 0 < normScale ν := normScale_pos hν
  have hn : absNorm ν ≠ 0 := by
    rw [← fieldAbsNorm_integer]
    exact (fieldAbsNorm_pos (by exact_mod_cast hν)).ne'
  rw [normalizedTarget, mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr hs),
    inv_pow, normScale_pow_degree, mixedNorm_integer, absNorm_unit_pow_mul,
    inv_mul_cancel₀ hn]

/-- A compact norm-one region, uniformly separated from each zero coordinate. -/
def compactTargetSet (K : Type*) [Field K] [NumberField K] (C : ℝ) :
    Set (mixedEmbedding.mixedSpace K) :=
  {b | mixedEmbedding.norm b = 1 ∧
    (∀ w : InfinitePlace K, C⁻¹ ≤ mixedEmbedding.normAtPlace w b ∧
      mixedEmbedding.normAtPlace w b ≤ C) ∧
    ∀ w : {w : InfinitePlace K // IsReal w}, 0 ≤ b.1 w}

theorem compactTargetSet_isClosed (C : ℝ) : IsClosed (compactTargetSet K C) := by
  have hplaces : IsClosed (⋂ w : InfinitePlace K,
      {b : mixedEmbedding.mixedSpace K | C⁻¹ ≤ mixedEmbedding.normAtPlace w b ∧
        mixedEmbedding.normAtPlace w b ≤ C}) := by
    apply isClosed_iInter
    intro w
    exact (isClosed_le continuous_const (mixedEmbedding.continuous_normAtPlace w)).inter
      (isClosed_le (mixedEmbedding.continuous_normAtPlace w) continuous_const)
  have hreal : IsClosed (⋂ w : {w : InfinitePlace K // IsReal w},
      {b : mixedEmbedding.mixedSpace K | 0 ≤ b.1 w}) := by
    apply isClosed_iInter
    intro w
    exact isClosed_le continuous_const ((continuous_apply w).comp continuous_fst)
  have hnorm : IsClosed {b : mixedEmbedding.mixedSpace K | mixedEmbedding.norm b = 1} :=
    isClosed_eq (mixedEmbedding.continuous_norm K) continuous_const
  convert hnorm.inter (hplaces.inter hreal) using 1
  ext b
  simp only [compactTargetSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

theorem compactTargetSet_isBounded (C : ℝ) : Bornology.IsBounded (compactTargetSet K C) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  intro b hb
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => (hb.2.1 w).2

theorem compactTargetSet_isCompact (C : ℝ) : IsCompact (compactTargetSet K C) :=
  Metric.isCompact_of_isClosed_isBounded (compactTargetSet_isClosed C) (compactTargetSet_isBounded C)

theorem compactTargetSet_real_pos {C : ℝ} (hC : 0 < C)
    {b : mixedEmbedding.mixedSpace K} (hb : b ∈ compactTargetSet K C)
    (w : {w : InfinitePlace K // IsReal w}) : 0 < b.1 w := by
  have hlo := (hb.2.1 w).1
  rw [mixedEmbedding.normAtPlace_apply_of_isReal w.property, Real.norm_eq_abs,
    abs_of_nonneg (hb.2.2 w)] at hlo
  exact (inv_pos.mpr hC).trans_le hlo

theorem compactTargetSet_place_ne_zero {C : ℝ} (hC : 0 < C)
    {b : mixedEmbedding.mixedSpace K} (hb : b ∈ compactTargetSet K C)
    (w : InfinitePlace K) : mixedEmbedding.normAtPlace w b ≠ 0 :=
  ((inv_pos.mpr hC).trans_le (hb.2.1 w).1).ne'

/-- The actual normalized targets all lie in one fixed compact positive region. -/
theorem exists_compact_normalized_targets (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 1 ≤ C ∧ IsCompact (compactTargetSet K C) ∧
      ∀ ν : 𝓞 K, ν ≠ 0 → TotallyPositive ν → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧ normalizedTarget k u ν ∈ compactTargetSet K C := by
  obtain ⟨C, hC, hbalance⟩ := exists_positive_unit_balance_integer K k hk
  refine ⟨C, hC, compactTargetSet_isCompact C, ?_⟩
  intro ν hν hp
  obtain ⟨u, hu, hb⟩ := hbalance ν hν
  refine ⟨u, hu, normalizedTarget_norm k u hν, ?_, ?_⟩
  · intro w
    have hs := normScale_pos hν
    have hnorm : mixedEmbedding.normAtPlace w (normalizedTarget k u ν) =
        (normScale ν)⁻¹ * w (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) := by
      rw [normalizedTarget, mixedEmbedding.normAtPlace_smul,
        abs_of_pos (inv_pos.mpr hs), mixedEmbedding.normAtPlace_apply]
    rw [hnorm]
    constructor
    · have hl : C⁻¹ * normScale ν ≤ w (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) := (hb w).1
      have h := mul_le_mul_of_nonneg_left hl (inv_pos.mpr hs).le
      simpa only [mul_left_comm, inv_mul_cancel₀ hs.ne', mul_one] using h
    · have hu' : w (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) ≤ C * normScale ν := (hb w).2
      have h := mul_le_mul_of_nonneg_left hu' (inv_pos.mpr hs).le
      simpa only [mul_left_comm, inv_mul_cancel₀ hs.ne', mul_one] using h
  · intro w
    have hpos := totallyPositive_mul (totallyPositive_pow hu k) hp (embedding_of_isReal w.property)
    change 0 ≤ (normScale ν)⁻¹ *
      (mixedEmbedding K (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K)).1 w
    rw [mixedEmbedding.mixedEmbedding_apply_isReal]
    exact (mul_pos (inv_pos.mpr (normScale_pos hν)) hpos).le

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_compact_normalized_targets

import WaringSiegel.WSL2UnitAnchors
import WaringSiegel.WSL2AnisotropicPacking

/-!
# Positive finite node boxes with the required algebraic norm control

The candidate nodes are actual algebraic integers whose mixed embeddings,
after division by P, lie in a fixed compact positive archimedean box. Their
finiteness and the manuscript's |Nx| ≤ C |Nν|^(1/k) condition are proved.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- A fixed positive archimedean box, separated from every coordinate hyperplane. -/
def rootBox (K : Type*) [Field K] [NumberField K] (ρ R : ℝ) : Set (mixedSpace K) :=
  {x | (∀ w : InfinitePlace K, ρ ≤ normAtPlace w x ∧ normAtPlace w x ≤ R) ∧
    ∀ w : {w : InfinitePlace K // IsReal w}, 0 ≤ x.1 w}

theorem rootBox_isCompact (ρ R : ℝ) : IsCompact (rootBox K ρ R) := by
  have hclosed : IsClosed (rootBox K ρ R) := by
    have hplaces : IsClosed (⋂ w : InfinitePlace K,
        {x : mixedSpace K | ρ ≤ normAtPlace w x ∧ normAtPlace w x ≤ R}) := by
      apply isClosed_iInter
      intro w
      exact (isClosed_le continuous_const (continuous_normAtPlace w)).inter
        (isClosed_le (continuous_normAtPlace w) continuous_const)
    have hreal : IsClosed (⋂ w : {w : InfinitePlace K // IsReal w},
        {x : mixedSpace K | 0 ≤ x.1 w}) := by
      apply isClosed_iInter
      intro w
      exact isClosed_le continuous_const ((continuous_apply w).comp continuous_fst)
    convert hplaces.inter hreal using 1
    ext x
    simp only [rootBox, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  apply Metric.isCompact_of_isClosed_isBounded hclosed
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨R, fun x hx => (mixed_norm_le_iff x R).mpr fun w => (hx.1 w).2⟩

theorem rootBox_positive {ρ R : ℝ} (hρ : 0 < ρ) {x : mixedSpace K}
    (hx : x ∈ rootBox K ρ R) : MixedPositive x := by
  intro w
  have hl := (hx.1 w).1
  rw [normAtPlace_apply_of_isReal w.property, Real.norm_eq_abs, abs_of_nonneg (hx.2 w)] at hl
  exact hρ.trans_le hl

theorem rootBox_isUnit {ρ R : ℝ} (hρ : 0 < ρ) {x : mixedSpace K}
    (hx : x ∈ rootBox K ρ R) : IsUnit x :=
  (mixed_isUnit_iff x).mpr fun w => (hρ.trans_le (hx.1 w).1).ne'

/-- All real embeddings are represented by the real coordinates of the actual mixed embedding. -/
theorem totallyPositive_iff_mixedPositive (x : 𝓞 K) :
    TotallyPositive x ↔ MixedPositive (mixedEmbedding K (x : K)) := by
  constructor
  · intro hx w
    exact hx (embedding_of_isReal w.property)
  · intro hx σ
    let φ : K →+* ℂ := Complex.ofRealHom.comp σ
    have hφ : ComplexEmbedding.IsReal φ := by
      apply ComplexEmbedding.isReal_iff.mpr
      ext z
      simp [φ, ComplexEmbedding.conjugate_coe_eq]
    let w : {w : InfinitePlace K // IsReal w} := ⟨mk φ, isReal_mk_iff.mpr hφ⟩
    have he : embedding_of_isReal w.property = σ := by
      ext z
      apply Complex.ofReal_injective
      rw [embedding_of_isReal_apply]
      change (embedding (mk φ)) z = (σ z : ℂ)
      rw [embedding_mk_eq_of_isReal hφ]
      rfl
    have hh := hx w
    change 0 < embedding_of_isReal w.property (x : K) at hh
    rwa [he] at hh

/-- Actual candidate algebraic integers in the dilated fixed box. -/
def scaledIntegerNodeSet (P ρ R : ℝ) : Set (𝓞 K) :=
  {x | P⁻¹ • mixedEmbedding K (x : K) ∈ rootBox K ρ R}

theorem scaledIntegerNodeSet_place_bound {P ρ R : ℝ} (hP : 0 < P)
    {x : 𝓞 K} (hx : x ∈ scaledIntegerNodeSet P ρ R) (w : InfinitePlace K) :
    w (x : K) ≤ P * R := by
  have hh := (hx.1 w).2
  rw [normAtPlace_smul, abs_of_pos (inv_pos.mpr hP), normAtPlace_apply] at hh
  have hm := mul_le_mul_of_nonneg_left hh hP.le
  rwa [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul] at hm

/-- These node sets are finite because every embedding is bounded; no norm-only
finiteness claim is used. -/
theorem scaledIntegerNodeSet_finite {P ρ R : ℝ} (hP : 0 < P) :
    (scaledIntegerNodeSet (K := K) P ρ R).Finite := by
  let f : 𝓞 K → K := fun x => (x : K)
  have hinj : Function.Injective f := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hfinite := Embeddings.finite_of_norm_le K ℂ (P * R)
  apply (Set.Finite.preimage (Set.injOn_of_injective hinj) hfinite).subset
  intro x hx
  refine ⟨x.property, ?_⟩
  exact (InfinitePlace.le_iff_le (x : K) (P * R)).mp
    (scaledIntegerNodeSet_place_bound hP hx)

theorem scaledIntegerNodeSet_positive {P ρ R : ℝ} (hP : 0 < P) (hρ : 0 < ρ)
    {x : 𝓞 K} (hx : x ∈ scaledIntegerNodeSet P ρ R) : TotallyPositive x := by
  apply (totallyPositive_iff_mixedPositive x).mpr
  intro w
  have hp := rootBox_positive hρ hx w
  change 0 < P⁻¹ * (mixedEmbedding K (x : K)).1 w at hp
  exact pos_of_mul_pos_right hp (inv_pos.mpr hP).le

theorem scaledIntegerNodeSet_norm_bound {P ρ R : ℝ} (hP : 0 < P)
    {x : 𝓞 K} (hx : x ∈ scaledIntegerNodeSet P ρ R) :
    absNorm x ≤ (P * R) ^ Module.finrank ℚ K := by
  have hb : ‖mixedEmbedding K (x : K)‖ ≤ P * R :=
    (mixed_norm_le_iff _ _).mpr fun w => by
      rw [normAtPlace_apply]
      exact scaledIntegerNodeSet_place_bound hP hx w
  rw [← mixedNorm_integer]
  exact (mixed_productNorm_le_norm_pow _).trans (pow_le_pow_left₀ (norm_nonneg _) hb _)

theorem rootScale_pow_degree (k : ℕ) (hk : 0 < k) (ν : 𝓞 K) :
    rootScale k ν ^ Module.finrank ℚ K = absNorm ν ^ (1 / (k : ℝ)) := by
  unfold rootScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (absNorm_nonneg ν)]
  congr 1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  field_simp

/-- At the manuscript's scale P, every candidate root has exactly the required
norm control, with a constant independent of the target. -/
theorem scaledIntegerNodeSet_target_norm_bound (k : ℕ) (hk : 0 < k)
    {ν : 𝓞 K} (hν : ν ≠ 0) {ρ R : ℝ} {x : 𝓞 K}
    (hx : x ∈ scaledIntegerNodeSet (rootScale k ν) ρ R) :
    absNorm x ≤ R ^ Module.finrank ℚ K * absNorm ν ^ (1 / (k : ℝ)) := by
  have h := scaledIntegerNodeSet_norm_bound (rootScale_pos hν k) hx
  simpa only [mul_pow, rootScale_pow_degree k hk, mul_comm] using h

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.scaledIntegerNodeSet_finite
#print axioms WaringSiegel.WSL2.scaledIntegerNodeSet_target_norm_bound

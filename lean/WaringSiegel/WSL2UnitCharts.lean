import WaringSiegel.WSL2UnitNodeBoxes

/-!
# Uniform positive root boxes and finitely many nonsingular archimedean charts

Compact normalized targets admit anchors with common upper and lower
coordinate bounds. One common-radius ball around every anchor stays inside
a fixed compact positive root box. The inverse function theorem and a finite
subcover give finitely many genuine charts covering all normalized targets.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- The anchor magnitudes are uniformly bounded above and below on the
entire fixed compact target region. -/
theorem exists_uniform_anchor_bounds (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ ∀ b ∈ compactTargetSet K B,
      ∃ a : mixedSpace K, (∑ _i : Fin s, a ^ k) = b ∧ MixedPositive a ∧ IsUnit a ∧
        ∀ w : InfinitePlace K, ρ ≤ normAtPlace w a ∧ normAtPlace w a ≤ R := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let ρ : ℝ := ((s : ℝ)⁻¹ * B⁻¹) ^ (1 / (k : ℝ))
  let R : ℝ := ((s : ℝ)⁻¹ * B) ^ (1 / (k : ℝ))
  refine ⟨ρ, R, Real.rpow_pos_of_pos (mul_pos (inv_pos.mpr hsR) (inv_pos.mpr hB)) _,
    Real.rpow_pos_of_pos (mul_pos (inv_pos.mpr hsR) hB) _, ?_⟩
  intro b hb
  obtain ⟨a, hsum, hap, hau, ha⟩ := exists_mixed_waring_anchor k s hk hs b
    (compactTargetSet_real_pos hB hb) (compactTargetSet_place_ne_zero hB hb)
  refine ⟨a, hsum, hap, hau, ?_⟩
  intro w
  rw [mixed_anchor_magnitude hk hs ha w]
  constructor
  · exact Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left (hb.2.1 w).1 (inv_pos.mpr hsR).le) (by positivity)
  · exact Real.rpow_le_rpow (mul_nonneg (inv_pos.mpr hsR).le (normAtPlace_nonneg w b))
      (mul_le_mul_of_nonneg_left (hb.2.1 w).2 (inv_pos.mpr hsR).le) (by positivity)

/-- A common-radius ball about an anchor remains positive and separated
from every coordinate hyperplane. -/
theorem closedBall_anchor_subset_rootBox {ρ R : ℝ} (hρ : 0 < ρ)
    {a : mixedSpace K} (hap : MixedPositive a)
    (ha : ∀ w : InfinitePlace K, ρ ≤ normAtPlace w a ∧ normAtPlace w a ≤ R) :
    Metric.closedBall a (ρ / 2) ⊆ rootBox K (ρ / 2) (R + ρ / 2) := by
  intro x hx
  have hxa : ‖x - a‖ ≤ ρ / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hadiff (w : InfinitePlace K) : normAtPlace w (a - x) ≤ ρ / 2 := by
    exact (normAtPlace_le_mixed_norm (a - x) w).trans (by rwa [norm_sub_rev])
  have hxdiff (w : InfinitePlace K) : normAtPlace w (x - a) ≤ ρ / 2 :=
    (normAtPlace_le_mixed_norm (x - a) w).trans hxa
  constructor
  · intro w
    have hlow := normAtPlace_add_le w (a - x) x
    rw [sub_add_cancel] at hlow
    have hupp := normAtPlace_add_le w (x - a) a
    rw [sub_add_cancel] at hupp
    constructor <;> linarith [(ha w).1, (ha w).2, hadiff w, hxdiff w]
  · intro w
    have halow := (ha w).1
    rw [normAtPlace_apply_of_isReal w.property, Real.norm_eq_abs, abs_of_pos (hap w)] at halow
    have hdiff : |x.1 w - a.1 w| ≤ ρ / 2 := by
      simpa only [normAtPlace_apply_of_isReal w.property] using hxdiff w
    have hdifflo := (abs_le.mp hdiff).1
    linarith

/-- The actual first-variable Waring chart, with all other variables fixed. -/
def mixedWaringChart (k s : ℕ) (a : mixedSpace K) (x : mixedSpace K) : mixedSpace K :=
  x ^ k + (s - 1) • a ^ k

theorem mixedWaringChart_anchor (k s : ℕ) (hs : 0 < s) (a : mixedSpace K) :
    mixedWaringChart k s a a = ∑ _i : Fin s, a ^ k := by
  simp only [mixedWaringChart, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc
    a ^ k + (s - 1) • a ^ k = (1 + (s - 1)) • a ^ k := by rw [add_nsmul, one_nsmul]
    _ = s • a ^ k := by congr 1; omega

/-- Finitely many genuine nonsingular charts cover all compact normalized
targets, and every chart's source ball lies in one fixed compact positive box. -/
theorem exists_finite_uniform_archimedean_charts (k s : ℕ) (hk : 0 < k) (hs : 0 < s)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      ∃ A : Finset (mixedSpace K),
        (∀ a ∈ A, MixedPositive a ∧ IsUnit a ∧
          Metric.closedBall a ρ ⊆ rootBox K ρ R) ∧
        ∀ b ∈ compactTargetSet K B, ∃ a ∈ A,
          b ∈ interior (mixedWaringChart k s a '' Metric.ball a ρ) := by
  obtain ⟨ρ₀, R₀, hρ₀, hR₀, hanchors⟩ := exists_uniform_anchor_bounds (K := K) k s hk hs B hB
  let I := compactTargetSet K B
  let a : I → mixedSpace K := fun b => Classical.choose (hanchors b b.property)
  have ha (b : I) : (∑ _i : Fin s, a b ^ k) = b ∧ MixedPositive (a b) ∧ IsUnit (a b) ∧
      ∀ w : InfinitePlace K, ρ₀ ≤ normAtPlace w (a b) ∧ normAtPlace w (a b) ≤ R₀ :=
    Classical.choose_spec (hanchors b b.property)
  let V : I → Set (mixedSpace K) := fun b =>
    interior (mixedWaringChart k s (a b) '' Metric.ball (a b) (ρ₀ / 2))
  have hV (b : I) : (b : mixedSpace K) ∈ V b := by
    apply mem_interior_iff_mem_nhds.mpr
    have h := shifted_mixed_pow_image_mem_nhds k hk (a b) ((s - 1) • (a b)^k)
      (ha b).2.2.1 (Metric.ball_mem_nhds (a b) (by positivity : 0 < ρ₀ / 2))
    have he : a b ^ k + (s - 1) • a b ^ k = (b : mixedSpace K) :=
      (mixedWaringChart_anchor k s hs (a b)).trans (ha b).1
    rwa [he] at h
  obtain ⟨T, hT⟩ := (compactTargetSet_isCompact (K := K) B).elim_finite_subcover V
    (fun _ => isOpen_interior) (by
      intro b hb
      exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hV ⟨b, hb⟩⟩)
  refine ⟨ρ₀ / 2, R₀ + ρ₀ / 2, by positivity, by positivity,
    rootBox_isCompact _ _, T.image a, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(ha b).2.1, (ha b).2.2.1,
      closedBall_anchor_subset_rootBox hρ₀ (ha b).2.1 (ha b).2.2.2⟩
  · intro b hb
    obtain ⟨j, hjT, hj⟩ := Set.mem_iUnion₂.mp (hT hb)
    exact ⟨a j, Finset.mem_image.mpr ⟨j, hjT, rfl⟩, hj⟩

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_finite_uniform_archimedean_charts

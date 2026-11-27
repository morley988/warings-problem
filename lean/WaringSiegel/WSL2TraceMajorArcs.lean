import WaringSiegel.WSL2ProductArcs
import WaringSiegel.WSL2TraceHaar

/-!
# WSL2: product major arcs on the actual trace quotient

The lifted separation estimate descends to V/D⁻¹. Centers are compared as
actual quotient classes, so lattice translates of one rational center are
not mistakenly treated as different arcs.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

instance archimedeanTraceTorus_t2Space : T2Space (ArchimedeanTraceTorus K) :=
  (archimedeanTraceTorusHomeomorph (K := K)).symm.t2Space

def traceRationalPoint (γ : K) : ArchimedeanTraceTorus K :=
  Submodule.Quotient.mk (mixedEmbedding K γ)

theorem traceRationalPoint_eq_iff (γ δ : K) :
    traceRationalPoint γ = traceRationalPoint δ ↔ γ - δ ∈ inverseDifferent K := by
  change Submodule.Quotient.mk (mixedEmbedding K γ) =
    (Submodule.Quotient.mk (mixedEmbedding K δ) : ArchimedeanTraceTorus K) ↔ _
  rw [Submodule.Quotient.eq, ← map_sub, mem_archInverseDifferentLattice]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' := (mixedEmbedding K).injective he
    rwa [he'] at ha
  · intro h
    exact ⟨γ - δ, h, rfl⟩

def traceMajorArc (H L : ℝ) (γ : K) : Set (ArchimedeanTraceTorus K) :=
  Submodule.Quotient.mk '' productMajorArc (inverseDifferent K) H L γ

/-- Lattice-equivalent rational centers define the same projected arc. -/
theorem traceMajorArc_add_inverseDifferent (H L : ℝ) (γ a : K)
    (ha : a ∈ inverseDifferent K) : traceMajorArc H L (γ + a) = traceMajorArc H L γ := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x - mixedEmbedding K a, ?_, ?_⟩
    · change (Ideal.absNorm (conductorIdeal (inverseDifferent K) γ) : ℝ) *
        productArcWeight H ((x - mixedEmbedding K a) - mixedEmbedding K γ) ≤ L
      have he : (x - mixedEmbedding K a) - mixedEmbedding K γ =
          x - mixedEmbedding K (γ+a) := by rw [map_add]; abel
      rw [he]
      simpa only [productMajorArc, Set.mem_setOf_eq,
        conductorIdeal_add_lattice _ _ _ ha] using hx
    · apply (Submodule.Quotient.eq _).mpr
      have hmem : mixedEmbedding K a ∈ archInverseDifferentLattice (K := K) :=
        (mem_archInverseDifferentLattice _).mpr ⟨a, ha, rfl⟩
      simpa only [sub_sub_cancel_left] using (archInverseDifferentLattice (K := K)).neg_mem hmem
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x + mixedEmbedding K a, ?_, ?_⟩
    · change (Ideal.absNorm (conductorIdeal (inverseDifferent K) (γ+a)) : ℝ) *
        productArcWeight H ((x + mixedEmbedding K a) - mixedEmbedding K (γ+a)) ≤ L
      rw [conductorIdeal_add_lattice _ _ _ ha, map_add]
      have he : (x + mixedEmbedding K a) - (mixedEmbedding K γ + mixedEmbedding K a) =
          x - mixedEmbedding K γ := by abel
      rw [he]
      exact hx
    · apply (Submodule.Quotient.eq _).mpr
      have hmem : mixedEmbedding K a ∈ archInverseDifferentLattice (K := K) :=
        (mem_archInverseDifferentLattice _).mpr ⟨a, ha, rfl⟩
      simpa only [add_sub_cancel_left] using hmem

/-- The actual projected major arcs are disjoint for distinct trace-torus
centers under the exact conductor separation cutoff. -/
theorem traceMajorArcs_disjoint (H L : ℝ) (hH : 0 < H) (hL : 0 ≤ L)
    (hsmall : (2 : ℝ)^finrank ℚ K * L^2 <
      (FractionalIdeal.absNorm (inverseDifferent K) : ℝ) * H^finrank ℚ K)
    (γ δ : K) (hne : traceRationalPoint γ ≠ traceRationalPoint δ) :
    Disjoint (traceMajorArc H L γ) (traceMajorArc H L δ) := by
  rw [Set.disjoint_left]
  intro q hγ hδ
  obtain ⟨x, hx, hxq⟩ := hγ
  obtain ⟨y, hy, hyq⟩ := hδ
  have hxy : x - y ∈ archInverseDifferentLattice (K := K) :=
    (Submodule.Quotient.eq _).mp (hxq.trans hyq.symm)
  obtain ⟨a, ha, hea⟩ := (mem_archInverseDifferentLattice _).mp hxy
  have hne' : γ ≠ δ+a := by
    intro h
    apply hne
    apply (traceRationalPoint_eq_iff γ δ).mpr
    rw [h, add_sub_cancel_left]
    exact ha
  have hδ' : x ∈ productMajorArc (inverseDifferent K) H L (δ+a) := by
    change (Ideal.absNorm (conductorIdeal (inverseDifferent K) (δ+a)) : ℝ) *
      productArcWeight H (x - mixedEmbedding K (δ+a)) ≤ L
    rw [conductorIdeal_add_lattice _ _ _ ha, map_add, hea]
    have he : x - (mixedEmbedding K δ + (x-y)) = y - mixedEmbedding K δ := by abel
    rw [he]
    exact hy
  exact Set.disjoint_left.mp
    (productMajorArcs_disjoint _ inverseDifferent_ne_zero H L hH hL hsmall γ (δ+a) hne') hx hδ'

theorem productArcWeight_continuous (H : ℝ) : Continuous (productArcWeight (K := K) H) := by
  unfold productArcWeight
  apply continuous_finset_prod
  intro w hw
  exact (continuous_const.max (continuous_const.mul (continuous_normAtPlace w))).pow (mult w)

theorem place_le_productArcWeight (H : ℝ) (β : mixedSpace K) (w : InfinitePlace K) :
    H * normAtPlace w β ≤ productArcWeight H β := by
  calc
    _ ≤ max 1 (H * normAtPlace w β) := le_max_right _ _
    _ = ∏ v : InfinitePlace K, if v = w then max 1 (H * normAtPlace v β) else 1 := by simp
    _ ≤ productArcWeight H β := by
      apply Finset.prod_le_prod
      · intro v hv
        split_ifs
        · exact le_trans zero_le_one (le_max_left _ _)
        · exact zero_le_one
      · intro v hv
        split_ifs
        · exact le_self_pow₀ (le_max_left _ _) mult_ne_zero
        · exact one_le_pow₀ (le_max_left _ _)

theorem productMajorArc_isClosed (I : FractionalIdeal (𝓞 K)⁰ K)
    (H L : ℝ) (γ : K) : IsClosed (productMajorArc I H L γ) := by
  unfold productMajorArc
  exact isClosed_le
    (continuous_const.mul ((productArcWeight_continuous H).comp (continuous_id.sub continuous_const)))
    continuous_const

theorem productMajorArc_isCompact (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (H L : ℝ) (hH : 0 < H) (γ : K) : IsCompact (productMajorArc I H L γ) := by
  let Q : ℝ := Ideal.absNorm (conductorIdeal I γ)
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast conductorIdeal_absNorm_pos I hI γ
  have hbound : productMajorArc I H L γ ⊆
      Metric.closedBall (mixedEmbedding K γ) (L / Q / H) := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_eq_norm, mixed_norm_le_iff]
    intro w
    apply (le_div_iff₀ hH).mpr
    calc
      _ = H * normAtPlace w (θ - mixedEmbedding K γ) := mul_comm _ _
      _ ≤ productArcWeight H (θ - mixedEmbedding K γ) := place_le_productArcWeight _ _ _
      _ ≤ L / Q := (le_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hθ)
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨productMajorArc_isClosed I H L γ, Metric.isBounded_closedBall.subset hbound⟩

theorem traceMajorArc_isCompact (H L : ℝ) (hH : 0 < H) (γ : K) :
    IsCompact (traceMajorArc H L γ) :=
  (productMajorArc_isCompact _ inverseDifferent_ne_zero H L hH γ).image continuous_quotient_mk'

theorem traceMajorArc_measurableSet (H L : ℝ) (hH : 0 < H) (γ : K) :
    MeasurableSet (traceMajorArc H L γ) :=
  (traceMajorArc_isCompact H L hH γ).isClosed.measurableSet

end WaringSiegel

import WaringSiegel.WSL2UnitDensity

/-!
# One uniform target radius for the positive archimedean density

Compactness makes both the lower constant and the neighborhood radius
uniform over all normalized targets. The measure statement and its genuine
Radon–Nikodym density counterpart are both recorded explicitly.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- A fixed local measure domination on a compact set holds on balls of
one fixed positive radius around every point of that set. -/
theorem compact_uniform_ball_measure_lower {E : Type*} [MetricSpace E]
    [MeasurableSpace E] (μ ν : Measure E) (c : ENNReal)
    {S : Set E} (hS : IsCompact S)
    (hloc : ∀ b ∈ S, ∃ V : Set E, IsOpen V ∧ b ∈ V ∧ c • μ.restrict V ≤ ν) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ S, c • μ.restrict (Metric.ball b δ) ≤ ν := by
  by_cases hne : S.Nonempty
  · have hballs (b : S) : ∃ r : ℝ, 0 < r ∧ c • μ.restrict (Metric.ball b r) ≤ ν := by
      obtain ⟨V, hV, hb, hdom⟩ := hloc b b.property
      obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hb)
      exact ⟨r, hr, (measure_smul_mono c (Measure.restrict_mono hrV le_rfl)).trans hdom⟩
    choose r hr hdom using hballs
    obtain ⟨T, hT⟩ := hS.elim_finite_subcover
      (fun b : S => Metric.ball (b : E) (r b / 2)) (fun _ => Metric.isOpen_ball) (by
        intro b hb
        exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, Metric.mem_ball_self (half_pos (hr ⟨b, hb⟩))⟩)
    obtain ⟨b₀, hb₀⟩ := hne
    obtain ⟨j₀, hj₀, -⟩ := Set.mem_iUnion₂.mp (hT hb₀)
    have hTne : T.Nonempty := ⟨j₀, hj₀⟩
    let δ := T.inf' hTne (fun j => r j / 2)
    refine ⟨δ, (Finset.lt_inf'_iff _).mpr (fun j _ => half_pos (hr j)), ?_⟩
    intro b hb
    obtain ⟨j, hj, hbj⟩ := Set.mem_iUnion₂.mp (hT hb)
    have hδ : δ ≤ r j / 2 := Finset.inf'_le _ hj
    have hsub : Metric.ball b δ ⊆ Metric.ball (j : E) (r j) := by
      intro x hx
      have hxb := Metric.mem_ball.mp hx
      have hba := Metric.mem_ball.mp hbj
      apply Metric.mem_ball.mpr
      have ht := dist_triangle x b (j : E)
      linarith
    exact (measure_smul_mono c (Measure.restrict_mono hsub le_rfl)).trans (hdom j)
  · exact ⟨1, zero_lt_one, fun b hb => False.elim (hne ⟨b, hb⟩)⟩

/-- One actual compact positive root box, one positive volume constant,
and one positive target radius work for every normalized target. -/
theorem exists_uniform_archimedean_ball_volume_lower (k s : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ b ∈ compactTargetSet K B,
          c • volume.restrict (Metric.ball b δ) ≤ archimedeanWaringMeasure k s ρ R := by
  obtain ⟨ρ, R, hρ, hR, hcompact, c, hc, hcfin, hlocal⟩ :=
    exists_uniform_archimedean_volume_lower (K := K) k s hk B hB
  obtain ⟨δ, hδ, hballs⟩ := compact_uniform_ball_measure_lower volume _ c
    (compactTargetSet_isCompact (K := K) B) hlocal
  exact ⟨ρ, R, hρ, hR, hcompact, c, hc, hcfin, δ, hδ, hballs⟩

/-- The genuine density is uniformly bounded below a.e. on balls of a
fixed positive radius about every compact normalized target. -/
theorem exists_uniform_archimedean_ball_density_lower (k s : ℕ) (hk : 0 < k)
    (B : ℝ) (hB : 0 < B) :
    ∃ ρ R : ℝ, 0 < ρ ∧ 0 < R ∧ IsCompact (rootBox K ρ R) ∧
      ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ b ∈ compactTargetSet K B,
        ∀ᵐ x ∂volume.restrict (Metric.ball b δ),
          c ≤ (archimedeanWaringDensity k s ρ R x).toReal := by
  obtain ⟨ρ, R, hρ, hR, hcompact, c, hc, hcfin, δ, hδ, hballs⟩ :=
    exists_uniform_archimedean_ball_volume_lower (K := K) k s hk B hB
  refine ⟨ρ, R, hρ, hR, hcompact, c.toReal, δ,
    ENNReal.toReal_pos hc.ne' hcfin.ne, hδ, ?_⟩
  intro b hb
  have hdom := hballs b hb
  rw [← archimedeanWaringDensity_measure k s hk ρ R hρ] at hdom
  have hae := ae_density_lower_of_measure_domination volume
    (archimedeanWaringDensity (K := K) k s ρ R)
    (archimedeanWaringDensity_measurable k s ρ R) c Metric.isOpen_ball.measurableSet hdom
  filter_upwards [hae, ae_restrict_of_ae (archimedeanWaringDensity_finite_ae (K := K) k s ρ R)]
    with x hx hxfin
  exact ENNReal.toReal_mono hxfin.ne hx

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_uniform_archimedean_ball_volume_lower
#print axioms WaringSiegel.WSL2.exists_uniform_archimedean_ball_density_lower

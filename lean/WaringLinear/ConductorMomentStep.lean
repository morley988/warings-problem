import WaringLinear.IntegratedStage
import WaringLinear.StageArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # A conductor stage for actual continuous Fourier magnitudes -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace WaringLinear
variable {T : Type*} [AddCommGroup T] [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace T] [BorelSpace T] [MeasurableAdd T]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [AddCommGroup T] [MeasurableAdd T] in
private theorem compact_power_integrable (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → ℝ) (hf : Continuous f) (a : ℝ) (ha : 0≤a) :
    Integrable (fun x => (f x)^a) μ :=
  (hf.rpow_const (fun _ => Or.inr ha)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [AddCommGroup T] [TopologicalSpace T] [CompactSpace T] [BorelSpace T] [MeasurableAdd T] in
private theorem integral_preserved {μ : Measure T} (t : T → T)
    (ht : MeasurePreserving t μ μ) (f : T → ℝ) (hf : Integrable f μ) :
    (∫ x,f (t x) ∂μ)=∫ x,f x ∂μ := by
  rw [←integral_map ht.measurable.aemeasurable
    (by simpa only [ht.map_eq] using hf.aestronglyMeasurable),ht.map_eq]

/-- The new excess A is any common upper bound for the under-threshold
and the large-fibre exponents. The data are normalized Haar maps, actual
continuous complex sums, a finite marking identity, a cutoff on the
squared large-fibre samples and unchanged-order divisor child moments.
The conclusion is the real-order integral bound itself. -/
theorem conductor_fourier_moment_step
    (μ : Measure T) [IsFiniteMeasure μ] [μ.IsAddRightInvariant]
    (π : ι → T →+ T) (ψ : κ → T →+ T)
    (hπ : ∀ i,MeasurePreserving (π i) μ μ) (hψ : ∀ j,MeasurePreserving (ψ j) μ μ)
    (cπ : ∀ i,Continuous (π i)) (cψ : ∀ j,Continuous (ψ j))
    [∀ i,Fintype (π i).ker]
    (F : T → ℂ) (V H : ι → T → ℂ) (J : κ → T → ℂ)
    (cF : Continuous F) (cV : ∀ i,Continuous (V i))
    (cH : ∀ i,Continuous (H i)) (cJ : ∀ j,Continuous (J j))
    (m : ι → ℝ) (d : κ → ℝ) (X p k h z θ D E A : ℝ)
    (L P B C D₀ Z : ℝ)
    (hX : 1≤X) (hp : 1≤p) (hh : 0<h) (hhp : h<p+2)
    (hD : 0≤D) (hL : 0≤L) (hP : 0≤P) (hB : 0≤B) (hC : 0≤C) (hD₀ : 0≤D₀)
    (hm : ∀ i,0<m i) (hd : ∀ j,0<d j) (hmass : (∑i,(m i)⁻¹)≤1)
    (hsize : ∀ i,X^θ≤m i)
    (hcard : ∀ i,(Fintype.card (π i).ker:ℝ)=(m i)^k)
    (hparent : ∀ x,F x=∑ i,V i (π i x))
    (hbad : ∀ x, (∃ i,2*‖H i x‖<‖F x‖) → ∃ j,‖F x‖≤D₀*‖J j (ψ j x)‖)
    (hfibre : ∀ i x, (∑ a : (π i).ker,
      {u : T | X^(1-z)≤2*‖H i u‖}.indicator (fun u => ‖H i u‖^2) (x+a.1))≤B*X^2)
    (hlow : (∫x,‖F x‖^h ∂μ)≤L*X^(h-k+E))
    (hshort : ∀ i,(∫x,‖V i x‖^p ∂μ)≤C*(X/m i)^(p-k+D))
    (hexcept : ∀ j,(∫x,‖J j x‖^(p+2) ∂μ)≤P*(X/d j)^(p+2-k+A))
    (hZ : (∑j,((d j)^(p+2-k+A))⁻¹)≤Z)
    (hAh : E-(p+2-h)*z≤A) (hAD : (1-θ)*D≤A) :
    (∫x,‖F x‖^(p+2) ∂μ) ≤ (L+4*B*C+D₀^(p+2)*(P*Z))*X^(p+2-k+A) := by
  classical
  let G : Set T := {x | X^(1-z)≤‖F x‖ ∧ ∀ i,‖F x‖≤2*‖H i x‖}
  let W (i : ι) (x : T) := m i*‖V i x‖
  let K (j : κ) (x : T) := ‖J j (ψ j x)‖
  have hXp : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hp' : 0≤p := by linarith
  have hr : 0≤p+2 := by linarith
  have hG : MeasurableSet G := by
    have he : G={x | X^(1-z)≤‖F x‖} ∩ ⋂ i,{x | ‖F x‖≤2*‖H i x‖} := by
      ext x
      simp only [G,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_iInter]
    rw [he]
    exact (measurableSet_le measurable_const cF.norm.measurable).inter
      (MeasurableSet.iInter (fun i => measurableSet_le cF.norm.measurable
        (continuous_const.mul (cH i).norm).measurable))
  have cW (i : ι) : Continuous (W i) := continuous_const.mul (cV i).norm
  have hW (i : ι) (x : T) : 0≤W i x := mul_nonneg (hm i).le (norm_nonneg _)
  have iF := compact_power_integrable μ _ cF.norm _ hr
  have iFW := iF.indicator hG
  have iLow := compact_power_integrable μ _ cF.norm h hh.le
  have iW (i : ι) := compact_power_integrable μ _ (cW i) p hp'
  have iJ (j : κ) := compact_power_integrable μ _ (cJ j).norm (p+2) hr
  have iK (j : κ) := compact_power_integrable μ _ ((cJ j).comp (cψ j)).norm (p+2) hr
  have iHW (i : ι) : Integrable (fun x => G.indicator (fun u => ‖H i u‖^2) x*(W i (π i x))^p) μ := by
    have hwhole := ((((cH i).norm.pow 2).mul (((cW i).comp (cπ i)).rpow_const (fun _ => Or.inr hp'))).integrable_of_hasCompactSupport
      (μ := μ) (HasCompactSupport.of_compactSpace _)).indicator hG
    apply hwhole.congr
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x∈G <;> simp [hx]
  have hpar (x : T) (_ : x∈G) : ‖F x‖≤∑ i,(m i)⁻¹*W i (π i x) := by
    calc
      _ ≤ ∑ i,‖V i (π i x)‖ := by rw [hparent]; exact norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp [W,(hm i).ne']
  have hs (x : T) (hx : x∉G) :
      ‖F x‖≤X^(1-z) ∨ ∃ j,‖F x‖≤D₀*K j x := by
    by_cases hl : ‖F x‖≤X^(1-z)
    · exact Or.inl hl
    · right
      apply hbad x
      by_contra! h
      exact hx ⟨(lt_of_not_ge hl).le,h⟩
  have hi (i : ι) (x : T) : (∑ a : (π i).ker,
      G.indicator (fun u => ‖H i u‖^2) (x+a.1))≤B*X^2 := by
    apply (Finset.sum_le_sum (fun a _ => ?_)).trans (hfibre i x)
    by_cases hmem : x+a.1∈G
    · have ht : X^(1-z)≤2*‖H i (x+a.1)‖ := hmem.1.trans (hmem.2 i)
      simp [hmem,ht]
    · rw [Set.indicator_of_notMem hmem]
      exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have raw := integrate_fourier_stage μ G π hπ (fun i => (m i)⁻¹) (fun _ => B*X^2)
    (fun x => ‖F x‖) W (fun i x => ‖H i x‖) K X p h z D₀ hXp hp hh hhp hD₀
    (fun i => (inv_pos.mpr (hm i)).le) hmass (fun x => norm_nonneg _) hW
    (fun j x => norm_nonneg _) hpar (fun x hx => hx.2) hs iF iFW iLow iW iK iHW hi
  have hlow' := low_stage_power _ X p k h z E L hXp hlow
  simp only [hcard] at raw
  have HH (i : ι) : (∫ x,(W i x)^p ∂μ)≤(m i)^p*C*(X/m i)^(p-k+D) := by
    simp only [W,Real.mul_rpow (hm i).le (norm_nonneg _),integral_const_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hshort i) (Real.rpow_nonneg (hm i).le p)
  have hgood' := good_stage_power m _ X p k D θ B C hXp hD hB hC hm hsize hmass HH
  have HJ (j : κ) : (∫ x,(K j x)^(p+2) ∂μ)≤P*(X/d j)^(p+2-k+A) := by
    change (∫ x,‖J j (ψ j x)‖^(p+2) ∂μ)≤_
    rw [integral_preserved _ (hψ j) _ (iJ j)]
    exact hexcept j
  have hbad' := exceptional_stage_power d _ X (p+2-k+A) Z P hXp hP hd hZ HJ
  apply combine_stage_powers _ X p k h z E D θ (4*B*C) L (D₀^(p+2)*(P*Z)) A
    hX (by positivity) hL hAD hAh
  have hh := mul_le_mul_of_nonneg_left hbad' (Real.rpow_nonneg hD₀ (p+2))
  linarith only [raw,hlow',hgood',hh]

#print axioms conductor_fourier_moment_step
end WaringLinear

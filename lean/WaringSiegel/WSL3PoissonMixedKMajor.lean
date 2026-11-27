import WaringSiegel.WSL3PoissonMixedKMinor
import WaringSiegel.WSL3PoissonMixedHolder

/-!
# The actual K_major(d) reduction, preserving Haar under multiplication

The major fourth moment is retained as its literal integral. No numerical
major-fourth estimate is assumed or asserted here. All Hölder, small-sum
Hua, restriction and multiplier steps are proved.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceCubicSum_eighth_moment {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum 3 w hc P (by linarith) q‖^8 ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(5+ε) := by
  obtain ⟨C,hC,hb⟩ := traceTorus_low_hua_moments (K:=K) 3 3
    (by norm_num) (by norm_num) (by norm_num) hε
  obtain ⟨W,hW⟩ := hw.continuous.bounded_above_of_compact_support hc
  let V := |W|+1
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨C*V^8,by positivity,fun P hP => ?_⟩
  have hP0 : 0 < P := by linarith
  let S := compactIntegerSupport w hc P hP0.ne'
  have hweights : ∀ x : S, ‖w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K))‖ ≤ V :=
    fun x => (hW _).trans ((le_abs_self W).trans (by dsimp [V]; linarith))
  have hbox : ∀ x : S, ∀ v : InfinitePlace K, v ((x:𝓞 K):K) ≤ P := by
    intro x v
    rw [← normAtPlace_apply]
    exact (normAtPlace_le_mixed_norm _ v).trans
      (compactIntegerSupport_norm_bound hc hsupport P hP0 x.property)
  have hh := hb P hP (fun x:S => (x:𝓞 K)) Subtype.val_injective hbox
    (fun x => w (P⁻¹ • mixedEmbedding K ((x:𝓞 K):K))) V hV.le hweights
  norm_num only [show (2^3:ℕ)=8 from rfl,show (2^3-3:ℕ)=5 from rfl,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

theorem compactTraceCubicSum_mul_eighth_moment {w : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hsupport : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P), ∀ a : 𝓞 K, a ≠ 0 →
      (∫ q, ‖compactTraceWeylSum 3 w hc P (by linarith) (traceTorusMul a q)‖^8 ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(5+ε) := by
  obtain ⟨C,hC,hb⟩ := compactTraceCubicSum_eighth_moment hw hc hsupport hε
  refine ⟨C,hC,fun P hP a ha => ?_⟩
  rw [compactTraceWeylSum,traceWeylSum_mul_integral_norm_pow a ha]
  exact hb P hP

/-- Actual set-integral transport under any nonzero integer multiplier. -/
theorem traceHaar_setIntegral_mul (d : 𝓞 K) (hd : d ≠ 0)
    (S : Set (ArchimedeanTraceTorus K)) (hS : MeasurableSet S)
    (f : ArchimedeanTraceTorus K → ℝ) (hf : Continuous f) :
    (∫ q in (traceTorusMul d) ⁻¹' S, f (traceTorusMul d q) ∂traceHaar) =
      ∫ q in S, f q ∂traceHaar := by
  have hm := (traceTorusMul_continuous d).measurable
  have h := integral_map (μ:=traceHaar) hm.aemeasurable
    (hf.measurable.indicator hS).aestronglyMeasurable
  rw [traceTorusMul_map_Haar d hd] at h
  calc
    _ = ∫ q, S.indicator f (traceTorusMul d q) ∂traceHaar := by
      rw [← integral_indicator (hS.preimage hm)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        by_cases hq : traceTorusMul d q ∈ S <;> simp [Set.indicator,hq])
    _ = ∫ q, S.indicator f q ∂traceHaar := h.symm
    _ = _ := integral_indicator hS

def nonzeroCubicMajorFourth (u : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (H : ℝ) (hH : H ≠ 0) : ℝ :=
  ∫ q in nonzeroCubicMajorArcs H, ‖compactTraceNonzeroCubicSum u huc H hH q‖^4 ∂traceHaar

theorem nonzeroCubicMajorFourth_nonneg (u : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (H : ℝ) (hH : H ≠ 0) : 0 ≤ nonzeroCubicMajorFourth u huc H hH :=
  integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)

def mixedKMajorIntegral (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) : ℝ :=
  ∫ q in (traceTorusMul d) ⁻¹' nonzeroCubicMajorArcs H,
    ‖compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q)‖ *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar

theorem mixedKMajorIntegral_nonneg (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) :
    0 ≤ mixedKMajorIntegral u v huc hvc H R hH hR d :=
  integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 4))

/-- Exact actual major-fourth reduction, with no conductor or norm(d) cost. -/
theorem mixedKMajorIntegral_fourth_bound (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : 0 < H) (hR : R ≠ 0) (d : 𝓞 K) (hd : d ≠ 0) :
    mixedKMajorIntegral u v huc hvc H R hH.ne' hR d ^4 ≤
      nonzeroCubicMajorFourth u huc H hH.ne' *
        (∫ q, ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^8 ∂traceHaar) *
        (∫ q, ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar)^2 := by
  let S := (traceTorusMul d) ⁻¹' nonzeroCubicMajorArcs (K:=K) H
  let f : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceNonzeroCubicSum u huc H hH.ne' (traceTorusMul d q)‖
  let g : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖
  have hcf : Continuous f :=
    ((compactTraceNonzeroCubicSum_continuous _ _ _ _).comp (traceTorusMul_continuous d)).norm
  have hcg : Continuous g :=
    ((compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous 4)).norm
  have hf0 : ∀ q, 0 ≤ f q := fun _ => norm_nonneg _
  have hg0 : ∀ q, 0 ≤ g q := fun _ => norm_nonneg _
  have h := compact_integral_holder_424 (μ:=traceHaar.restrict S) hcf hcg hf0 hg0
  have hS0 : MeasurableSet (nonzeroCubicMajorArcs (K:=K) H) :=
    traceMajorArcUnion_measurableSet _ _ (by positivity)
  have he : (∫ q in S, f q^4 ∂traceHaar) = nonzeroCubicMajorFourth u huc H hH.ne' :=
    traceHaar_setIntegral_mul d hd _ hS0 _ ((compactTraceNonzeroCubicSum_continuous _ _ _ _).norm.pow 4)
  rw [he] at h
  have h8 : (∫ q in S, g q^8 ∂traceHaar) ≤ ∫ q, g q^8 ∂traceHaar :=
    setIntegral_le_integral ((hcg.pow 8).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall (fun _ => pow_nonneg (hg0 _) _))
  have h4 : (∫ q in S, g q^4 ∂traceHaar) ≤ ∫ q, g q^4 ∂traceHaar :=
    setIntegral_le_integral ((hcg.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall (fun _ => pow_nonneg (hg0 _) _))
  apply h.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left h8 (nonzeroCubicMajorFourth_nonneg _ _ _ _)
  · exact pow_le_pow_left₀ (integral_nonneg (fun _ => pow_nonneg (hg0 _) _)) h4 2
  · exact sq_nonneg _
  · exact mul_nonneg (nonzeroCubicMajorFourth_nonneg _ _ _ _)
      (integral_nonneg (fun _ => pow_nonneg (hg0 _) _))

end WaringSiegel.WSL3Poisson

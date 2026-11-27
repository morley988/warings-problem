import WaringSiegel.WSL3PoissonMixedKWhole

/-! # Literal support counts and the diagonal contribution to J -/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_norm_one (x : 𝓞 K) (q : ArchimedeanTraceTorus K) :
    ‖traceTorusCharacter x q‖ = 1 := by
  exact norm_latticeCharacter_eq_one _ _

theorem compactIntegerSupport_card_volume_bound {w : mixedSpace K → ℂ}
    (hc : HasCompactSupport w) (hs : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (P : ℝ) (hP : 1 ≤ P) :
    ((compactIntegerSupport w hc P (by linarith)).card:ℝ) ≤
      2*3^finrank ℚ K * P^finrank ℚ K := by
  apply integer_box_card_bound _ P hP
  intro x hx v
  rw [← normAtPlace_apply]
  exact (normAtPlace_le_mixed_norm _ v).trans (compactIntegerSupport_norm_bound hc hs P (by linarith) hx)

theorem compactTraceNonzeroCubicSum_norm_le_mass (u : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (H : ℝ) (hH : H ≠ 0) (q : ArchimedeanTraceTorus K) :
    ‖compactTraceNonzeroCubicSum u huc H hH q‖ ≤
      ∑ h ∈ (compactIntegerSupport u huc H hH).erase 0,
        ‖u (H⁻¹ • mixedEmbedding K (h:K))‖ := by
  unfold compactTraceNonzeroCubicSum
  apply (norm_sum_le _ _).trans
  simp only [norm_mul,traceTorusCharacter_norm_one,mul_one,le_refl]

theorem compactTraceNonzeroCubicSum_volume_bound {u : mixedSpace K → ℂ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hus : ∀ x, u x ≠ 0 → ‖x‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ) (hH : 1 ≤ H), ∀ q : ArchimedeanTraceTorus K,
      ‖compactTraceNonzeroCubicSum u huc H (by linarith) q‖ ≤ C*H^finrank ℚ K := by
  obtain ⟨W,hW⟩ := hu.bounded_above_of_compact_support huc
  let V := |W|+1
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V*(2*3^finrank ℚ K),by positivity,fun H hH q => ?_⟩
  have hH0 : 0 < H := by linarith
  let S := compactIntegerSupport u huc H hH0.ne'
  have hweight (x : mixedSpace K) : ‖u x‖ ≤ V :=
    (hW x).trans ((le_abs_self W).trans (by dsimp [V]; linarith))
  have hsub : ((S.erase 0).card:ℝ) ≤ (S.card:ℝ) := by
    exact_mod_cast (Finset.card_erase_le (a:=(0:𝓞 K)) (s:=S))
  have hc : ((S.erase 0).card:ℝ) ≤ 2*3^finrank ℚ K*H^finrank ℚ K :=
    hsub.trans (compactIntegerSupport_card_volume_bound huc hus H hH)
  calc
    _ ≤ ∑ h ∈ S.erase 0, ‖u (H⁻¹ • mixedEmbedding K (h:K))‖ :=
      compactTraceNonzeroCubicSum_norm_le_mass _ _ _ _ _
    _ ≤ ∑ _h ∈ S.erase 0, V := Finset.sum_le_sum (fun _ _ => hweight _)
    _ = V*((S.erase 0).card:ℝ) := by simp [mul_comm]
    _ ≤ V*(2*3^finrank ℚ K*H^finrank ℚ K) := mul_le_mul_of_nonneg_left hc hV.le
    _ = _ := by ring

/-- The diagonal-pair bound uses the actual fourth moment, uniformly in
all multipliers. It also holds for the zero sixth-power difference. -/
theorem mixedKIntegral_trivial_volume_bound {u v : mixedSpace K → ℂ}
    (hu : Continuous u) (huc : HasCompactSupport u) (hus : ∀ x, u x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H R : ℝ) (hH : 1 ≤ H) (hR : 1 ≤ R), ∀ d : 𝓞 K,
      mixedKIntegral u v huc hvc H R (by linarith) (by linarith) d ≤
        C*(H^finrank ℚ K)*(R^finrank ℚ K : ℝ)^(2+ε) := by
  obtain ⟨Ce,hCe,he⟩ := compactTraceNonzeroCubicSum_volume_bound hu huc hus
  obtain ⟨Cg,hCg,hg⟩ := compactTraceCubicSum_mul_fourth_moment hv hvc hvs hε
  refine ⟨Ce*Cg,mul_pos hCe hCg,fun H R hH hR d => ?_⟩
  have hH0 : 0 < H := by linarith
  have hR0 : 0 < R := by linarith
  let E : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖compactTraceNonzeroCubicSum u huc H hH0.ne' (traceTorusMul d q)‖
  let g : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖compactTraceWeylSum 3 v hvc R hR0.ne' (traceTorusMul 4 q)‖^4
  have hcE : Continuous E := ((compactTraceNonzeroCubicSum_continuous _ _ _ _).comp
    (traceTorusMul_continuous d)).norm
  have hcg : Continuous g := ((compactTraceWeylSum_continuous _ _ _ _ _).comp
    (traceTorusMul_continuous 4)).norm.pow 4
  have hi : Integrable g traceHaar := hcg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ q, E q*g q ∂traceHaar := rfl
    _ ≤ ∫ q, (Ce*H^finrank ℚ K)*g q ∂traceHaar := integral_mono
      ((hcE.mul hcg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hi.const_mul _) (fun q => mul_le_mul_of_nonneg_right (he H hH _) (pow_nonneg (norm_nonneg _) _))
    _ = (Ce*H^finrank ℚ K)*∫ q, g q ∂traceHaar := integral_const_mul _ _
    _ ≤ (Ce*H^finrank ℚ K)*(Cg*(R^finrank ℚ K : ℝ)^(2+ε)) :=
      mul_le_mul_of_nonneg_left (hg R hR 4 (by norm_num)) (by positivity)
    _ = _ := by ring

end WaringSiegel.WSL3Poisson

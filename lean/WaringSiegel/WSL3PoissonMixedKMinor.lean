import WaringSiegel.WSL3PoissonMixedNonzero

/-!
# The actual K_minor(d) term of the cubic mixed moment

The h=0 term is removed literally. Multiplication by d occurs inside the
actual trace-torus map. The constant is uniform in every algebraic-integer
d, and in particular contains no factor involving its norm.
-/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def nonzeroCubicMajorArcs (H : ℝ) : Set (ArchimedeanTraceTorus K) :=
  traceMajorArcUnion (H^2*(4*H)) ((6:ℝ)^finrank ℚ K*H^finrank ℚ K)

def mixedKMinorArcs (H : ℝ) (d : 𝓞 K) : Set (ArchimedeanTraceTorus K) :=
  (traceTorusMul d) ⁻¹' (nonzeroCubicMajorArcs (K:=K) H)ᶜ

theorem mixedKMinorArcs_measurable (H : ℝ) (hH : 0 < H) (d : 𝓞 K) :
    MeasurableSet (mixedKMinorArcs (K:=K) H d) :=
  (traceMajorArcUnion_measurableSet _ _ (by positivity)).compl.preimage (traceTorusMul_continuous d).measurable

def mixedKMinorIntegral (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) : ℝ :=
  ∫ q in mixedKMinorArcs H d,
    ‖compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q)‖ *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar

theorem mixedKMinorIntegral_nonneg (u v : mixedSpace K → ℂ) (huc : HasCompactSupport u)
    (hvc : HasCompactSupport v) (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) :
    0 ≤ mixedKMinorIntegral u v huc hvc H R hH hR d := by
  apply integral_nonneg
  intro q
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 4)

/-- K_minor(d) << T^(3/4+epsilon) Z^(2+delta), for the actual sums and sets. -/
theorem mixedKMinorIntegral_bound {u v : mixedSpace K → ℂ}
    (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hus : ∀ x, u x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H R : ℝ) (hH : 1 ≤ H) (hR : 1 ≤ R), ∀ d : 𝓞 K,
      mixedKMinorIntegral u v huc hvc H R (by linarith) (by linarith) d ≤
        C*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)*(R^finrank ℚ K : ℝ)^(2+δ) := by
  obtain ⟨Ce,hCe,he⟩ := compactTraceNonzeroCubicSum_minor hu huc hus hε
  obtain ⟨Cu,hCu,hv4⟩ := compactTraceCubicSum_mul_fourth_moment hv hvc hvs hδ
  refine ⟨Ce*Cu,mul_pos hCe hCu,fun H R hH hR d => ?_⟩
  have hH0 : 0 < H := by linarith
  have hR0 : 0 < R := by linarith
  let E : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceNonzeroCubicSum u huc H hH0.ne' (traceTorusMul d q)‖
  let g : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceWeylSum 3 v hvc R hR0.ne' (traceTorusMul 4 q)‖^4
  let D := Ce*(H^finrank ℚ K : ℝ)^((3:ℝ)/4+ε)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcE : Continuous E :=
    ((compactTraceNonzeroCubicSum_continuous u huc H hH0.ne').comp (traceTorusMul_continuous d)).norm
  have hcg : Continuous g :=
    ((compactTraceWeylSum_continuous 3 v hvc R hR0.ne').comp (traceTorusMul_continuous 4)).norm.pow 4
  have hg : Integrable g traceHaar :=
    hcg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEg : Integrable (fun q => E q*g q) traceHaar :=
    (hcE.mul hcg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDg : Integrable (fun q => D*g q) traceHaar := hg.const_mul D
  have hg0 : ∀ q, 0 ≤ g q := fun q => pow_nonneg (norm_nonneg _) 4
  have hEf : ∀ q ∈ mixedKMinorArcs (K:=K) H d, E q ≤ D :=
    fun q hqm => he H hH (traceTorusMul d q) hqm
  have hfourth : (∫ q, g q ∂traceHaar) ≤ Cu*(R^finrank ℚ K : ℝ)^(2+δ) :=
    hv4 R hR 4 (by norm_num)
  calc
    _ = ∫ q in mixedKMinorArcs H d, E q*g q ∂traceHaar := rfl
    _ ≤ ∫ q in mixedKMinorArcs H d, D*g q ∂traceHaar :=
      setIntegral_mono_on hEg.integrableOn hDg.integrableOn (mixedKMinorArcs_measurable H hH0 d)
        (fun q hqm => mul_le_mul_of_nonneg_right (hEf q hqm) (hg0 q))
    _ = D * ∫ q in mixedKMinorArcs H d, g q ∂traceHaar := integral_const_mul _ _
    _ ≤ D * ∫ q, g q ∂traceHaar :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)) hD
    _ ≤ D * (Cu*(R^finrank ℚ K : ℝ)^(2+δ)) := mul_le_mul_of_nonneg_left hfourth hD
    _ = _ := by dsimp [D]; ring

end WaringSiegel.WSL3Poisson

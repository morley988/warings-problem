import WaringSiegel.WSL3PoissonMixedTorus

/-!
# The actual complementary integral I in the cubic mixed sixth moment

The integrand is the genuine quadratic average times the fourth power of the
small cubic trace sum. The major complement is the literal trace-torus set,
with all measurability, integrability, phase multipliers and moment inputs
proved. With X=P^d,T=H^d,Z=R^d this is I << T X^(1+epsilon) Z^(2+epsilon).
-/
noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def mixedComplementArcs (P H : ℝ) : Set (ArchimedeanTraceTorus K) :=
  (traceMajorArcUnion (P^2*(2*H)) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K))ᶜ

theorem mixedComplementArcs_measurable (P H : ℝ) (hP : 0 < P) (hH : 0 < H) :
    MeasurableSet (mixedComplementArcs (K:=K) P H) :=
  (traceMajorArcUnion_measurableSet _ _ (by positivity)).compl

def mixedComplementIntegral (w v : mixedSpace K → ℂ) (hwc : HasCompactSupport w)
    (hvc : HasCompactSupport v) (P H R : ℝ) (hP : P ≠ 0) (hR : R ≠ 0) (U : Finset (𝓞 K)) : ℝ :=
  ∫ q in mixedComplementArcs P H,
    compactTraceQuadraticAverage w hwc P hP U q *
      ‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 ∂traceHaar

theorem mixedComplementIntegral_nonneg (w v : mixedSpace K → ℂ) (hwc : HasCompactSupport w)
    (hvc : HasCompactSupport v) (P H R : ℝ) (hP : P ≠ 0) (hR : R ≠ 0) (U : Finset (𝓞 K)) :
    0 ≤ mixedComplementIntegral w v hwc hvc P H R hP hR U := by
  apply integral_nonneg
  intro q
  exact mul_nonneg (compactTraceQuadraticAverage_nonneg _ _ _ _ _ _)
    (pow_nonneg (norm_nonneg _) 4)

/-- Closed estimate for the actual complementary I integral. -/
theorem mixedComplementIntegral_bound {w v : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H R : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R),
      1 ≤ H → H ≤ P → P ≤ H^2 → ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      mixedComplementIntegral w v hwc hvc P H R (by linarith) (by linarith) U ≤
        C*P^finrank ℚ K*H^finrank ℚ K*P^ε*(R^finrank ℚ K : ℝ)^(2+δ) := by
  obtain ⟨Cq,hCq,hq⟩ := compactTraceQuadraticAverage_minor_bound hw hwc hws hε
  obtain ⟨Cu,hCu,hu⟩ := compactTraceCubicSum_mul_fourth_moment hv hvc hvs hδ
  refine ⟨Cq*Cu,mul_pos hCq hCu,fun P H R hP hR hH hHP hPH U hU0 hU => ?_⟩
  have hP0 : 0 < P := by linarith
  have hH0 : 0 < H := by linarith
  have hR0 : 0 < R := by linarith
  let A := compactTraceQuadraticAverage w hwc P hP0.ne' U
  let g : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceWeylSum 3 v hvc R hR0.ne' (traceTorusMul 4 q)‖^4
  let D := Cq*P^finrank ℚ K*H^finrank ℚ K*P^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcA : Continuous A := compactTraceQuadraticAverage_continuous _ _ _ _ _
  have hcg : Continuous g :=
    ((compactTraceWeylSum_continuous 3 v hvc R hR0.ne').comp (traceTorusMul_continuous 4)).norm.pow 4
  have hg : Integrable g traceHaar :=
    hcg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAg : Integrable (fun q => A q*g q) traceHaar :=
    (hcA.mul hcg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDg : Integrable (fun q => D*g q) traceHaar := hg.const_mul D
  have hg0 : ∀ q, 0 ≤ g q := fun q => pow_nonneg (norm_nonneg _) 4
  have hAf : ∀ q ∈ mixedComplementArcs (K:=K) P H, A q ≤ D :=
    fun q hqm => hq P H hP hH hHP hPH q hqm U hU0 hU
  have hfourth : (∫ q, g q ∂traceHaar) ≤ Cu*(R^finrank ℚ K : ℝ)^(2+δ) :=
    hu R hR 4 (by norm_num)
  calc
    _ = ∫ q in mixedComplementArcs P H, A q*g q ∂traceHaar := rfl
    _ ≤ ∫ q in mixedComplementArcs P H, D*g q ∂traceHaar :=
      setIntegral_mono_on hAg.integrableOn hDg.integrableOn
        (mixedComplementArcs_measurable P H hP0 hH0)
        (fun q hqm => mul_le_mul_of_nonneg_right (hAf q hqm) (hg0 q))
    _ = D * ∫ q in mixedComplementArcs P H, g q ∂traceHaar := integral_const_mul _ _
    _ ≤ D * ∫ q, g q ∂traceHaar :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)) hD
    _ ≤ D * (Cu*(R^finrank ℚ K : ℝ)^(2+δ)) := mul_le_mul_of_nonneg_left hfourth hD
    _ = _ := by dsimp [D]; ring

/-- The manuscript's volume-variable form, I << T X^(1+epsilon) Z^(2+epsilon). -/
theorem mixedComplementIntegral_volume_bound {w v : mixedSpace K → ℂ}
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w)
    (hws : ∀ x, w x ≠ 0 → ‖x‖ ≤ 1)
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hvs : ∀ x, v x ≠ 0 → ‖x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H R : ℝ) (hP : 1 ≤ P) (hR : 1 ≤ R),
      1 ≤ H → H ≤ P → P ≤ H^2 → ∀ U : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) → (∀ h ∈ U, ‖mixedEmbedding K (h:K)‖ ≤ H) →
      mixedComplementIntegral w v hwc hvc P H R (by linarith) (by linarith) U ≤
        C*H^finrank ℚ K*(P^finrank ℚ K : ℝ)^(1+ε)*(R^finrank ℚ K : ℝ)^(2+ε) := by
  have hd : (0:ℝ) < finrank ℚ K := by exact_mod_cast (finrank_pos (R:=ℚ) (M:=K))
  obtain ⟨C,hC,hb⟩ := mixedComplementIntegral_bound hw hwc hws hv hvc hvs (mul_pos hd hε) hε
  refine ⟨C,hC,fun P H R hP hR hH hHP hPH U hU0 hU => ?_⟩
  have hP0 : 0 < P := by linarith
  have hp : P^((finrank ℚ K : ℝ)*ε) = (P^finrank ℚ K : ℝ)^ε := by
    rw [Real.rpow_mul hP0.le,Real.rpow_natCast]
  have hx : (P^finrank ℚ K : ℝ)^(1+ε) = P^finrank ℚ K*(P^finrank ℚ K : ℝ)^ε := by
    rw [Real.rpow_add (pow_pos hP0 _),Real.rpow_one]
  exact (hb P H R hP hR hH hHP hPH U hU0 hU).trans_eq (by rw [hp,hx]; ring)

end WaringSiegel.WSL3Poisson

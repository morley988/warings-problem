import WaringSiegel.WSL3PoissonMixedSupport
import WaringSiegel.WSL3PoissonTranslatedWeights
import WaringSiegel.WSL3MomentCompletion

/-!
# Literal smooth cubic and quadratic Weyl differencing over the trace lattice

All coefficients are arbitrary elements of the archimedean algebra. Exact
compact supports remove the overlap restrictions without adding boundary
terms. The resulting amplitudes are the actual translated product weights.
-/
noncomputable section
set_option maxHeartbeats 1200000
open Function NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def traceCubicNodePhase (θ α β : mixedSpace K) (x : 𝓞 K) : ℂ :=
  archimedeanTraceCharacter 1
    (θ*(mixedEmbedding K (x:K))^3+α*(mixedEmbedding K (x:K))^2+β*mixedEmbedding K (x:K))

def traceQuadraticNodePhase (θ α : mixedSpace K) (x : 𝓞 K) : ℂ :=
  archimedeanTraceCharacter 1
    (θ*(mixedEmbedding K (x:K))^2+α*mixedEmbedding K (x:K))

def compactCubicSum (w : mixedSpace K → ℂ) (P : ℝ) (θ α β : mixedSpace K) : ℂ :=
  ∑' x : 𝓞 K, w (P⁻¹ • mixedEmbedding K (x:K)) * traceCubicNodePhase θ α β x

def compactQuadraticSum (w : mixedSpace K → ℂ) (P : ℝ) (θ α : mixedSpace K) : ℂ :=
  ∑' x : 𝓞 K, w (P⁻¹ • mixedEmbedding K (x:K)) * traceQuadraticNodePhase θ α x

theorem trace_phase_correlation (w : 𝓞 K → ℂ) (f : 𝓞 K → mixedSpace K) (h x : 𝓞 K) :
    shiftedWeight (fun x => w x * archimedeanTraceCharacter 1 (f x)) h x =
      shiftedWeight w h x * archimedeanTraceCharacter 1 (f (x+h)-f x) := by
  simp only [shiftedWeight, WSL3.archimedeanTraceCharacter_sub, map_mul]
  ring

theorem trace_phase_double_correlation (w : 𝓞 K → ℂ) (f : 𝓞 K → mixedSpace K) (h j x : 𝓞 K) :
    doubleShiftedWeight (fun x => w x * archimedeanTraceCharacter 1 (f x)) h j x =
      doubleShiftedWeight w h j x *
        archimedeanTraceCharacter 1 (f (x+j+h)-f (x+j)-(f (x+h)-f x)) := by
  unfold doubleShiftedWeight
  rw [show shiftedWeight (fun x => w x * archimedeanTraceCharacter 1 (f x)) h =
      (fun x => shiftedWeight w h x * archimedeanTraceCharacter 1 (f (x+h)-f x)) from
        funext (fun x => trace_phase_correlation w f h x)]
  exact trace_phase_correlation _ _ j x

theorem traceCharacter_one_mul (a x : mixedSpace K) :
    archimedeanTraceCharacter 1 (a*x) = archimedeanTraceCharacter a x := by
  simp only [archimedeanTraceCharacter, one_mul]

theorem norm_trace_linear_add_constant (S : Finset (𝓞 K)) (w : 𝓞 K → ℂ)
    (a c : mixedSpace K) :
    ‖∑ x ∈ S, w x * archimedeanTraceCharacter 1 (a*mixedEmbedding K (x:K)+c)‖ =
      ‖∑ x ∈ S, w x * archimedeanTraceCharacter a (mixedEmbedding K (x:K))‖ := by
  simp only [archimedeanTraceCharacter_add, traceCharacter_one_mul, ← mul_assoc]
  rw [← Finset.sum_mul, norm_mul, archimedeanTraceCharacter_norm, mul_one]

theorem traceCubic_double_correlation_norm (S : Finset (𝓞 K)) (w : 𝓞 K → ℂ)
    (θ α β : mixedSpace K) (h j : 𝓞 K) :
    ‖∑ x ∈ S, doubleShiftedWeight (fun x => w x * traceCubicNodePhase θ α β x) h j x‖ =
      ‖∑ x ∈ S, doubleShiftedWeight w h j x *
        archimedeanTraceCharacter (6*θ*mixedEmbedding K (h:K)*mixedEmbedding K (j:K))
          (mixedEmbedding K (x:K))‖ := by
  simp only [traceCubicNodePhase, trace_phase_double_correlation, map_add]
  have heq (x : 𝓞 K) :
      θ*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K)+mixedEmbedding K (h:K))^3+
          α*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K)+mixedEmbedding K (h:K))^2+
          β*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K)+mixedEmbedding K (h:K))-
      (θ*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K))^3+
          α*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K))^2+
          β*(mixedEmbedding K (x:K)+mixedEmbedding K (j:K)))-
      (θ*(mixedEmbedding K (x:K)+mixedEmbedding K (h:K))^3+
          α*(mixedEmbedding K (x:K)+mixedEmbedding K (h:K))^2+
          β*(mixedEmbedding K (x:K)+mixedEmbedding K (h:K))-
        (θ*(mixedEmbedding K (x:K))^3+α*(mixedEmbedding K (x:K))^2+β*mixedEmbedding K (x:K))) =
      (6*θ*mixedEmbedding K (h:K)*mixedEmbedding K (j:K))*mixedEmbedding K (x:K)+
        (3*θ*mixedEmbedding K (h:K)*mixedEmbedding K (j:K)*(mixedEmbedding K (h:K)+mixedEmbedding K (j:K))+
          2*α*mixedEmbedding K (h:K)*mixedEmbedding K (j:K)) := by ring
  simp_rw [heq]
  exact norm_trace_linear_add_constant _ _ _ _

theorem traceQuadratic_correlation_norm (S : Finset (𝓞 K)) (w : 𝓞 K → ℂ)
    (θ α : mixedSpace K) (h : 𝓞 K) :
    ‖∑ x ∈ S, shiftedWeight (fun x => w x * traceQuadraticNodePhase θ α x) h x‖ =
      ‖∑ x ∈ S, shiftedWeight w h x *
        archimedeanTraceCharacter (2*θ*mixedEmbedding K (h:K)) (mixedEmbedding K (x:K))‖ := by
  simp only [traceQuadraticNodePhase, trace_phase_correlation, map_add]
  have heq (x : 𝓞 K) :
      θ*(mixedEmbedding K (x:K)+mixedEmbedding K (h:K))^2+
          α*(mixedEmbedding K (x:K)+mixedEmbedding K (h:K))-
        (θ*(mixedEmbedding K (x:K))^2+α*mixedEmbedding K (x:K)) =
      (2*θ*mixedEmbedding K (h:K))*mixedEmbedding K (x:K)+
        (θ*(mixedEmbedding K (h:K))^2+α*mixedEmbedding K (h:K)) := by ring
  simp_rw [heq]
  exact norm_trace_linear_add_constant _ _ _ _

theorem shiftedWeight_scaled (w : mixedSpace K → ℂ) (P : ℝ) (h x : 𝓞 K) :
    shiftedWeight (fun x : 𝓞 K => w (P⁻¹ • mixedEmbedding K (x:K))) h x =
      translatedProductWeight w
        (P⁻¹ • mixedEmbedding K (h:K), P⁻¹ • mixedEmbedding K (x:K)) := by
  simp only [shiftedWeight, translatedProductWeight, map_add, smul_add]

theorem doubleShiftedWeight_scaled (w : mixedSpace K → ℂ) (P : ℝ) (h j x : 𝓞 K) :
    doubleShiftedWeight (fun x : 𝓞 K => w (P⁻¹ • mixedEmbedding K (x:K))) h j x =
      doubleTranslatedProductWeight w
        ((P⁻¹ • mixedEmbedding K (h:K),P⁻¹ • mixedEmbedding K (j:K)), P⁻¹ • mixedEmbedding K (x:K)) := by
  simp only [doubleShiftedWeight, shiftedWeight, doubleTranslatedProductWeight,
    map_add, smul_add]

/-- Actual cubic differencing, with arbitrary archimedean lower coefficients. -/
theorem compactCubicSum_fourth_le_linear (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ α β : mixedSpace K) (H : Finset (𝓞 K))
    (hH : ∀ x ∈ compactIntegerSupport w hc P hP, ∀ y ∈ compactIntegerSupport w hc P hP,
      x-y ∈ H) :
    ‖compactCubicSum w P θ α β‖^4 ≤ (H.card:ℝ) * ∑ h ∈ H, ∑ j ∈ H,
      ‖compactLinearSum (fun x => doubleTranslatedProductWeight w
        ((P⁻¹ • mixedEmbedding K (h:K),P⁻¹ • mixedEmbedding K (j:K)),x)) P
          (6*θ*mixedEmbedding K (h:K)*mixedEmbedding K (j:K))‖ := by
  let S := compactIntegerSupport w hc P hP
  let W : 𝓞 K → ℂ := fun x => w (P⁻¹ • mixedEmbedding K (x:K))
  have hW : ∀ x, W x ≠ 0 → x ∈ S := fun x hx => (mem_compactIntegerSupport w hc P hP x).mpr hx
  have hsum : compactCubicSum w P θ α β = ∑ x ∈ S, W x * traceCubicNodePhase θ α β x := by
    apply tsum_eq_sum
    intro x hx
    have hz : W x = 0 := by by_contra hn; exact hx (hW x hn)
    exact mul_eq_zero_of_left hz _
  rw [hsum]
  have hb := finite_sum_fourth_le_double_correlations S H hH
    (fun x => W x * traceCubicNodePhase θ α β x)
  simp_rw [traceCubic_double_correlation_norm, sum_doubleShiftedWeight_eq_tsum hW] at hb
  simpa only [W, doubleShiftedWeight_scaled, compactLinearSum] using hb

/-- Actual quadratic differencing; its linear coefficient is exactly `2θh`. -/
theorem compactQuadraticSum_sq_le_linear (w : mixedSpace K → ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P ≠ 0) (θ α : mixedSpace K) (H : Finset (𝓞 K))
    (hH : ∀ x ∈ compactIntegerSupport w hc P hP, ∀ y ∈ compactIntegerSupport w hc P hP,
      x-y ∈ H) :
    ‖compactQuadraticSum w P θ α‖^2 ≤ ∑ h ∈ H,
      ‖compactLinearSum (fun x => translatedProductWeight w (P⁻¹ • mixedEmbedding K (h:K),x)) P
        (2*θ*mixedEmbedding K (h:K))‖ := by
  let S := compactIntegerSupport w hc P hP
  let W : 𝓞 K → ℂ := fun x => w (P⁻¹ • mixedEmbedding K (x:K))
  have hW : ∀ x, W x ≠ 0 → x ∈ S := fun x hx => (mem_compactIntegerSupport w hc P hP x).mpr hx
  have hsum : compactQuadraticSum w P θ α = ∑ x ∈ S, W x * traceQuadraticNodePhase θ α x := by
    apply tsum_eq_sum
    intro x hx
    have hz : W x = 0 := by by_contra hn; exact hx (hW x hn)
    exact mul_eq_zero_of_left hz _
  rw [hsum]
  have hb := finite_sum_norm_sq_le_correlations S H hH (fun x => W x * traceQuadraticNodePhase θ α x)
  simp_rw [traceQuadratic_correlation_norm, sum_shiftedWeight_eq_tsum hW] at hb
  simpa only [W, shiftedWeight_scaled, compactLinearSum] using hb

end WaringSiegel.WSL3Poisson

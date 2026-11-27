import WaringLinear.SeveralFactors
import WaringLinear.TraceMoment

/-! # A loss-free restricted moment from a defect paid by several ordinary factors -/
noncomputable section
open MeasureTheory
open scoped NumberField
open WaringSiegel WaringSiegel.WSL2
namespace WaringLinear
variable {T : Type*} [MeasurableSpace T]

theorem loss_free_several_factors (μ : Measure T) (M : Set T) (hM : MeasurableSet M)
    (F f : T → ℝ) (hF0 : ∀ x, 0 ≤ F x) (hf0 : ∀ x, 0 ≤ f x)
    (m d a k : ℕ) (P C B A D ρ E : ℝ) (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : E ≤ ((a:ℝ)+1)*ρ)
    (hBox : ∀ x ∈ Mᶜ, F x ≤ C*P) (hMinor : ∀ x ∈ Mᶜ, f x ≤ B*P^(1-ρ))
    (hI : Integrable (fun x => F x^(m+d+a+1)) μ)
    (hJ : Integrable (fun x => f x^(m+d+a+1)) μ)
    (hr : Integrable (fun x => F x^m) μ)
    (hOne : Integrable (fun x => f x*F x^(m+d+a)) μ)
    (hMany : Integrable (fun x => f x^(a+1)*F x^(m+d)) μ)
    (hSupport : (∫ x, F x^(m+d+a+1) ∂μ) ≤ ∫ x, f x*F x^(m+d+a) ∂μ)
    (hMajor : (∫ x in M, f x^(m+d+a+1) ∂μ) ≤ A*P^((m:ℝ)+d+a+1-k))
    (hRestricted : (∫ x, F x^m ∂μ) ≤ D*P^((m:ℝ)-k+E)) :
    (∫ x, F x^(m+d+a+1) ∂μ) ≤
      2*((2:ℝ)^(m+d+a+1)*A + B^(a+1)*C^d*D)*P^((m:ℝ)+d+a+1-k) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hMinor0 : 0 ≤ B*P^(1-ρ) := by positivity
  have hsub : (∫ x in Mᶜ, F x^m ∂μ) ≤ D*P^((m:ℝ)-k+E) :=
    (setIntegral_le_integral hr (Filter.Eventually.of_forall
      (fun x => pow_nonneg (hF0 x) m))).trans hRestricted
  have hpow : (P^(1-ρ))^(a+1) * P^d * P^((m:ℝ)-k+E) ≤ P^((m:ℝ)+d+a+1-k) := by
    rw [← Real.rpow_natCast (P^(1-ρ)) (a+1), ← Real.rpow_mul hPpos.le,
      ← Real.rpow_natCast P d, ← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
    apply Real.rpow_le_rpow_of_exponent_le hP
    push_cast
    linarith
  have hSupport' := many_mixed_of_one_mixed μ F f hF0 hf0 (m+d) a hI hOne hMany hSupport
  have hleft := absorb_several_mixed μ M hM F f hF0 hf0 m d a (C*P)
    (B*P^(1-ρ)) hMinor0 hBox hMinor hI hJ hr hMany hSupport'
  have hscaled : (B*P^(1-ρ))^(a+1)*(C*P)^d*(D*P^((m:ℝ)-k+E)) ≤
      B^(a+1)*C^d*D*P^((m:ℝ)+d+a+1-k) := by
    rw [mul_pow,mul_pow]
    calc
      _ = (B^(a+1)*C^d*D)*((P^(1-ρ))^(a+1)*P^d*P^((m:ℝ)-k+E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hMajor (by positivity : 0 ≤ (2:ℝ)^(m+d+a+1))
  have h2 := (mul_le_mul_of_nonneg_left hsub
    (by positivity : 0 ≤ (B*P^(1-ρ))^(a+1)*(C*P)^d)).trans hscaled
  nlinarith only [hleft,h1,h2]

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-- Actual Fourier sums of algebraic kth powers with positive nested weights on the
normalized trace torus. The only analytic hypotheses are the minor pointwise
estimate, the full ordinary major moment and the earlier restricted moment. -/
theorem trace_loss_free_several_factors (k : ℕ) (n : ι → 𝓞 K) (v w : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hvw : ∀ i, v i ≤ w i)
    (s m d a : ℕ) (horder : m+d+a=2*s+1)
    (M : Set (ArchimedeanTraceTorus K)) (hM : MeasurableSet M)
    (P C B A D ρ E : ℝ) (hP : 1 ≤ P) (hC : 0 ≤ C) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hE : E ≤ ((a:ℝ)+1)*ρ)
    (hBox : ∀ q ∈ Mᶜ, ‖traceWeylSum k n (fun x => (v x : ℂ)) q‖ ≤ C*P)
    (hMinor : ∀ q ∈ Mᶜ, ‖traceWeylSum k n (fun x => (w x : ℂ)) q‖ ≤ B*P^(1-ρ))
    (hMajor : (∫ q in M, ‖traceWeylSum k n (fun x => (w x : ℂ)) q‖^(m+d+a+1) ∂traceHaar) ≤
      A*P^((m:ℝ)+d+a+1-k))
    (hRestricted : (∫ q, ‖traceWeylSum k n (fun x => (v x : ℂ)) q‖^m ∂traceHaar) ≤
      D*P^((m:ℝ)-k+E)) :
    (∫ q, ‖traceWeylSum k n (fun x => (v x : ℂ)) q‖^(m+d+a+1) ∂traceHaar) ≤
      2*((2:ℝ)^(m+d+a+1)*A + B^(a+1)*C^d*D)*P^((m:ℝ)+d+a+1-k) := by
  let F := traceWeylSum k n (fun x => (v x : ℂ))
  let f := traceWeylSum k n (fun x => (w x : ℂ))
  have hc (weight : ι → ℂ) : Continuous (traceWeylSum k n weight) :=
    (continuous_frequencySum (fun x => integerCoordinates K (n x^k)) weight).comp
      (archimedeanTraceTorusContinuousAddEquiv (K := K)).continuous
  have hF := (hc (fun x => (v x : ℂ))).norm
  have hf := (hc (fun x => (w x : ℂ))).norm
  have hSupport := trace_even_moment_le_one_mixed k n v w hv hvw s
  rw [show 2*(s+1) = m+d+a+1 by omega, ← horder] at hSupport
  exact loss_free_several_factors traceHaar M hM (fun q => ‖F q‖) (fun q => ‖f q‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) m d a k P C B A D ρ E hP hC hB hD hE
    hBox hMinor
    ((hF.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hf.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hf.mul (hF.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hf.pow _).mul (hF.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hSupport hMajor hRestricted

#print axioms loss_free_several_factors
#print axioms trace_loss_free_several_factors
end WaringLinear

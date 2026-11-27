import WaringSiegel.WSL3MomentLocalizedCritical
import WaringSiegel.WSL3MomentCompactHua
import WaringSiegel.WSL3MomentHolder

/-! # Actual minor-arc interpolation with the two proved Hua families -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_localized_critical_bound_k
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k : ℕ) (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^(k*(k+1)) ∂traceHaar) ≤
        C * (P^finrank ℚ K)^((k^2:ℕ)-1+ε : ℝ) := by
  have hR : 1 ≤ k-2 := by omega
  have h2 : k-2+2=k := by omega
  have h3 : k-2+3=k+1 := by omega
  simpa only [h2,h3] using compactTraceWeylSum_localized_critical_bound f hc (k-2) hR hε

/-- A proved whole-torus moment and the proved localized critical moment
interpolate on the actual minor set. The low-moment premise is discharged by
the two final Hua-family specializations below. -/
theorem compactTraceWeylSum_minor_interpolated_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k : ℕ) (hk : 3 ≤ k) (m : ℕ) (lam : ℝ)
    (hwhole : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum k f hc P (by linarith) q‖^m ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(lam+ε))
    (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (horder : (p:ℝ) = (m:ℝ)*t + (k*(k+1):ℕ)*(1-t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(lam*t+((k^2:ℕ)-1)*(1-t)+ε : ℝ) := by
  obtain ⟨A,hA,hlo⟩ := hwhole ε hε
  obtain ⟨B,hB,hhi⟩ := compactTraceWeylSum_localized_critical_bound_k f hc k hk hε
  let C := A+B
  have hC : 0 < C := add_pos hA hB
  refine ⟨C,hC,?_⟩
  intro P hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let F : ArchimedeanTraceTorus K → ℝ := fun q => ‖compactTraceWeylSum k f hc P hP0.ne' q‖
  let M := vinogradovMinorArcs (K := K) k P
  have hF : Continuous F := (compactTraceWeylSum_continuous _ _ _ _ _).norm
  have hi (n : ℕ) : Integrable (fun q => F q^n) traceHaar :=
    (hF.pow n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow : (∫ q in M, F q^m ∂traceHaar) ≤ C*(P^finrank ℚ K : ℝ)^(lam+ε) := by
    calc
      _ ≤ ∫ q, F q^m ∂traceHaar := setIntegral_le_integral (hi m)
        (Filter.Eventually.of_forall (fun q => pow_nonneg (norm_nonneg _) _))
      _ ≤ A*(P^finrank ℚ K : ℝ)^(lam+ε) := hlo P hP
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (by positivity) _)
  have hhigh : (∫ q in M, F q^(k*(k+1)) ∂traceHaar) ≤
      C*(P^finrank ℚ K : ℝ)^((k^2:ℕ)-1+ε : ℝ) := by
    exact (hhi P hP).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; linarith) (Real.rpow_nonneg (by positivity) _))
  have h := integral_pow_interpolation (μ := traceHaar.restrict M) (fun q => norm_nonneg _)
    (hi p).integrableOn (hi m).integrableOn (hi (k*(k+1))).integrableOn ht0 ht1 horder
  exact h.trans (interpolated_power_bound
    (integral_nonneg (fun q => pow_nonneg (norm_nonneg _) _))
    (integral_nonneg (fun q => pow_nonneg (norm_nonneg _) _))
    hC (by positivity) ht0 ht1 hlow hhigh)

theorem compactTraceWeylSum_generalized_hua_splice
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k)
    (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (horder : (p:ℝ) = (r*(r+1):ℕ)*t + (k*(k+1):ℕ)*(1-t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((r^2:ℕ)*t+((k^2:ℕ)-1)*(1-t)+ε : ℝ) :=
  compactTraceWeylSum_minor_interpolated_bound f hc k hk (r*(r+1)) (r^2:ℕ)
    (fun ε hε => compactTraceWeylSum_generalized_hua_moment_bound f hc k r hr hrk hε)
    p t ht0 ht1 horder hε

theorem compactTraceWeylSum_classical_hua_splice
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j : ℕ) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (horder : (p:ℝ) = (2^j:ℕ)*t + (k*(k+1):ℕ)*(1-t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((2^j-j:ℕ)*t+((k^2:ℕ)-1)*(1-t)+ε : ℝ) :=
  compactTraceWeylSum_minor_interpolated_bound f hc k hk (2^j) (2^j-j:ℕ)
    (fun ε hε => compactTraceWeylSum_classical_hua_moment_bound f hc k j hj hjk hε)
    p t ht0 ht1 horder hε

#print axioms compactTraceWeylSum_generalized_hua_splice
#print axioms compactTraceWeylSum_classical_hua_splice
end WaringSiegel.WSL3

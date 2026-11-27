import WaringSiegel.WSL3MomentSplicing

/-! # Positive outer-minor savings from both actual Hua interpolations -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_generalized_hua_minor_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k)
    (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (horder : (p:ℝ) = (r*(r+1):ℕ)*t + (k*(k+1):ℕ)*(1-t))
    (hgain : 0 < 1-((k:ℝ)-r+1)*t) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  let δ : ℝ := 1-((k:ℝ)-r+1)*t
  have hδ : 0 < δ := hgain
  obtain ⟨C,hC,hb⟩ := compactTraceWeylSum_generalized_hua_splice f hc k r hk hr hrk
    p t ht0 ht1 horder (show 0 < δ/2 by positivity)
  refine ⟨C,δ/2,hC,by positivity,?_⟩
  intro P hP
  have he : (r^2:ℕ)*t+((k^2:ℕ)-1)*(1-t)+δ/2 = (p:ℝ)-k-δ/2 := by
    dsimp [δ]
    push_cast at horder ⊢
    nlinarith [horder]
  simpa only [he] using hb P hP

theorem compactTraceWeylSum_classical_hua_minor_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j : ℕ) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : j ≤ k)
    (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (horder : (p:ℝ) = (2^j:ℕ)*t + (k*(k+1):ℕ)*(1-t))
    (hgain : 0 < 1-((k:ℝ)+1-j)*t) :
    ∃ C η : ℝ, 0 < C ∧ 0 < η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  let δ : ℝ := 1-((k:ℝ)+1-j)*t
  have hδ : 0 < δ := hgain
  obtain ⟨C,hC,hb⟩ := compactTraceWeylSum_classical_hua_splice f hc k j hk hj hjk
    p t ht0 ht1 horder (show 0 < δ/2 by positivity)
  refine ⟨C,δ/2,hC,by positivity,?_⟩
  intro P hP
  have hjpow : j ≤ 2^j := j.lt_two_pow_self.le
  have he : (2^j-j:ℕ)*t+((k^2:ℕ)-1)*(1-t)+δ/2 = (p:ℝ)-k-δ/2 := by
    dsimp [δ]
    rw [Nat.cast_sub hjpow]
    push_cast at horder ⊢
    nlinarith [horder]
  simpa only [he] using hb P hP

#print axioms compactTraceWeylSum_generalized_hua_minor_saving
#print axioms compactTraceWeylSum_classical_hua_minor_saving
end WaringSiegel.WSL3

import WaringSiegel.WSL4MajorFlexibleSplicing

/-! # A strict interpolation gap survives a genuinely smaller major cutoff -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_shrinking_interpolation_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k : ℕ) (hk : 3≤k) (m : ℕ) (lam : ℝ)
    (hwhole : ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q, ‖compactTraceWeylSum k f hc P (by linarith) q‖^m ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(lam+ε))
    (p : ℕ) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1)
    (horder : (p:ℝ)=(m:ℝ)*t+(k*(k+1):ℕ)*(1-t))
    (hgap : 0<(p:ℝ)-k-(lam*t+((k^2:ℕ)-1)*(1-t))) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  let δ : ℝ := (p:ℝ)-k-(lam*t+((k^2:ℕ)-1)*(1-t))
  have hδ : 0<δ := hgap
  let β : ℝ := min (δ/8) (1/4)
  have hβ : 0<β := lt_min (by positivity) (by norm_num)
  have hβδ : β≤δ/8 := min_le_left _ _
  have hβ1 : β≤1/4 := min_le_right _ _
  let a : ℝ := 1-β
  have ha0 : 0<a := by dsimp [a]; linarith
  have ha1 : a<1 := by dsimp [a]; linarith
  obtain ⟨C,hC,hbound⟩ := compactTraceWeylSum_shrinking_interpolated_bound f hc k hk a ha0.le ha1.le
    m lam hwhole p t ht0 ht1 horder (show 0<δ/4 by positivity)
  refine ⟨a,C,δ/4,ha0,ha1,hC,by positivity,?_⟩
  intro P hP
  have he : lam*t+((k^2:ℕ)+1-2*a)*(1-t)+δ/4≤(p:ℝ)-k-δ/4 := by
    have hprod := mul_nonneg hβ.le ht0
    dsimp [a]
    dsimp [δ] at hβδ ⊢
    nlinarith
  exact (hbound P hP).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hP) he) hC.le)

theorem compactTraceWeylSum_generalized_hua_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r : ℕ) (hk : 3≤k) (hr : 1≤r) (hrk : r≤k)
    (p : ℕ) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1)
    (horder : (p:ℝ)=(r*(r+1):ℕ)*t+(k*(k+1):ℕ)*(1-t))
    (hgain : 0<1-((k:ℝ)-r+1)*t) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  apply compactTraceWeylSum_shrinking_interpolation_saving f hc k hk (r*(r+1)) (r^2:ℕ)
    (fun ε hε => compactTraceWeylSum_generalized_hua_moment_bound f hc k r hr hrk hε)
    p t ht0 ht1 horder
  have he : (p:ℝ)-k-((r^2:ℕ)*t+((k^2:ℕ)-1)*(1-t))=1-((k:ℝ)-r+1)*t := by
    push_cast at horder ⊢
    nlinarith [horder]
  rw [he]
  exact hgain

theorem compactTraceWeylSum_classical_hua_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j : ℕ) (hk : 3≤k) (hj : 1≤j) (hjk : j≤k)
    (p : ℕ) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1)
    (horder : (p:ℝ)=(2^j:ℕ)*t+(k*(k+1):ℕ)*(1-t))
    (hgain : 0<1-((k:ℝ)+1-j)*t) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  apply compactTraceWeylSum_shrinking_interpolation_saving f hc k hk (2^j) (2^j-j:ℕ)
    (fun ε hε => compactTraceWeylSum_classical_hua_moment_bound f hc k j hj hjk hε)
    p t ht0 ht1 horder
  have hjpow : j≤2^j := j.lt_two_pow_self.le
  have he : (p:ℝ)-k-((2^j-j:ℕ)*t+((k^2:ℕ)-1)*(1-t))=1-((k:ℝ)+1-j)*t := by
    rw [Nat.cast_sub hjpow]
    push_cast at horder ⊢
    nlinarith [horder]
  rw [he]
  exact hgain

#print axioms compactTraceWeylSum_generalized_hua_shrinking_saving
#print axioms compactTraceWeylSum_classical_hua_shrinking_saving
end WaringSiegel.WSL4

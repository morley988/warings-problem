import WaringSiegel.WSL3MomentSplicing
import WaringSiegel.WSL3MomentCompactTrivial

/-! # Actual minor-arc saving above the critical moment -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_supercritical_minor_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hTp : k*(k+1)≤p) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  obtain ⟨B,hB,htrivial⟩ := compactTraceWeylSum_trivial_bound f hc
  obtain ⟨A,hA,hcritical⟩ := compactTraceWeylSum_localized_critical_bound_k f hc k hk
    (by norm_num : (0:ℝ)<1/2)
  let T := k*(k+1)
  let N := p-T
  have hn : N+T=p := Nat.sub_add_cancel hTp
  refine ⟨B^N*A,1/2,by positivity,by norm_num,?_⟩
  intro P hP
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let X : ℝ := P^finrank ℚ K
  have hX : 0<X := pow_pos hP0 _
  let F : ArchimedeanTraceTorus K → ℝ := fun q => ‖compactTraceWeylSum k f hc P hP0.ne' q‖
  have hF : Continuous F := (compactTraceWeylSum_continuous _ _ _ _ _).norm
  have hi (n : ℕ) : Integrable (fun q => F q^n) traceHaar :=
    (hF.pow n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb (q : ArchimedeanTraceTorus K) : F q≤B*X := htrivial P hP k q
  have hpoint (q : ArchimedeanTraceTorus K) : F q^p≤(B*X)^N*F q^T := by
    calc
      _ = F q^(N+T) := by rw [hn]
      _ = F q^N*F q^T := pow_add _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hb q) N) (pow_nonneg (norm_nonneg _) T)
  have hbound : (∫ q in vinogradovMinorArcs (K := K) k P, F q^p ∂traceHaar) ≤
      (B*X)^N * (A*X^((k^2:ℕ)-1+1/2 : ℝ)) := by
    calc
      _ ≤ ∫ q in vinogradovMinorArcs (K := K) k P, (B*X)^N*F q^T ∂traceHaar :=
        setIntegral_mono_on (hi p).integrableOn ((hi T).const_mul _).integrableOn
          (vinogradovMinorArcs_measurable _ _ hP0) (fun q _ => hpoint q)
      _ = (B*X)^N * ∫ q in vinogradovMinorArcs (K := K) k P, F q^T ∂traceHaar := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcritical P hP) (by positivity)
  have he : (N:ℝ)+((k^2:ℕ)-1+1/2 : ℝ)=(p:ℝ)-k-1/2 := by
    have hnR : (N:ℝ)+(k:ℝ)*(k+1)=p := by exact_mod_cast hn
    push_cast
    nlinarith [hnR]
  apply hbound.trans_eq
  calc
    (B*X)^N*(A*X^((k^2:ℕ)-1+1/2 : ℝ)) =
        (B^N*A)*(X^(N:ℝ)*X^((k^2:ℕ)-1+1/2 : ℝ)) := by
      rw [mul_pow,Real.rpow_natCast]
      ring
    _ = _ := by rw [← Real.rpow_add hX, he]

#print axioms compactTraceWeylSum_supercritical_minor_saving
end WaringSiegel.WSL3

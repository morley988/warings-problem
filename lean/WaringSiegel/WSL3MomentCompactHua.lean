import WaringSiegel.WSL3MomentGeneralizedTrace
import WaringSiegel.WSL3MomentTrace
import WaringSiegel.WSL3MomentTranslationSupport
import WaringSiegel.WSL3PoissonMixedTorus

/-! # Both full Hua families for the actual fixed compact smooth trace sums -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
universe u
variable {K : Type u} [Field K] [NumberField K]

theorem compact_moment_of_boxed_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k m : ℕ) (lam : ℝ)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ {α : Type u} [Fintype α] (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : InfinitePlace K, v (nodes x:K) ≤ P) →
      ∀ (w : α → ℂ) (W : ℝ), 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ q, ‖traceWeylSum k nodes w q‖^m ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(lam+ε)*W^m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum k f hc P (by linarith) q‖^m ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^(lam+ε) := by
  obtain ⟨A, hA, hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  obtain ⟨C, hC, hbound⟩ := hb ε hε
  let W : ℝ := 1 + SchwartzMap.seminorm ℝ 0 0 f
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨C*(A^finrank ℚ K : ℝ)^(lam+ε)*W^m, by positivity, ?_⟩
  intro P hP
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let S := compactIntegerSupport f hc P hP0.ne'
  have hS : ∀ x : S, ∀ v : InfinitePlace K, v (x.val:K) ≤ A*P := by
    intro x v
    exact hsupport P hP0 x.val ((mem_compactIntegerSupport _ _ _ _ _).mp x.property) v
  have hw : ∀ x : S, ‖f (P⁻¹ • mixedEmbedding K (x.val:K))‖ ≤ W := by
    intro x
    exact (SchwartzMap.norm_le_seminorm ℝ f _).trans (by dsimp [W]; linarith)
  have h := hbound (A*P) (one_le_mul_of_one_le_of_one_le hA hP)
    (fun x : S => x.val) Subtype.val_injective hS
    (fun x : S => f (P⁻¹ • mixedEmbedding K (x.val:K))) W hW.le hw
  apply h.trans_eq
  rw [mul_pow, Real.mul_rpow (by positivity) (by positivity)]
  ring

theorem compactTraceWeylSum_generalized_hua_moment_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum k f hc P (by linarith) q‖^(r*(r+1)) ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((r^2:ℕ)+ε : ℝ) :=
  compact_moment_of_boxed_bound f hc k (r*(r+1)) (r^2:ℕ)
    (fun ε hε => traceTorus_generalized_hua_moment_bound k r hr hrk hε) hε

theorem compactTraceWeylSum_classical_hua_moment_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q, ‖compactTraceWeylSum k f hc P (by linarith) q‖^(2^j) ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((2^j-j:ℕ)+ε : ℝ) :=
  compact_moment_of_boxed_bound f hc k (2^j) (2^j-j:ℕ)
    (fun ε hε => traceTorus_hua_moment_bound k j hj hjk hε) hε

#print axioms compactTraceWeylSum_generalized_hua_moment_bound
#print axioms compactTraceWeylSum_classical_hua_moment_bound
end WaringSiegel.WSL3

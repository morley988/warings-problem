import WaringSiegel.WSL3MomentTranslationSupport
import WaringSiegel.WSL3PoissonMixedTorus

/-! # The literal compact trace sum is bounded by its box volume -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_trivial_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P), ∀ k : ℕ, ∀ q : ArchimedeanTraceTorus K,
      ‖compactTraceWeylSum k f hc P (by linarith) q‖ ≤ C*P^finrank ℚ K := by
  obtain ⟨A,hA,hsupport⟩ := compact_support_place_bound (f : mixedSpace K → ℂ) hc
  let W : ℝ := 1 + SchwartzMap.seminorm ℝ 0 0 f
  have hW : 0<W := by dsimp [W]; positivity
  refine ⟨2*(3:ℝ)^finrank ℚ K*A^finrank ℚ K*W, by positivity, ?_⟩
  intro P hP k q
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let S := compactIntegerSupport f hc P hP0.ne'
  have hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K)≤A*P := by
    intro x hx v
    exact hsupport P hP0 x ((mem_compactIntegerSupport _ _ _ _ _).mp hx) v
  have hcard := integer_box_card_bound S (A*P) (one_le_mul_of_one_le_of_one_le hA hP) hS
  have hw (x : S) : ‖f (P⁻¹ • mixedEmbedding K (x.val:K))‖≤W :=
    (SchwartzMap.norm_le_seminorm ℝ f _).trans (by dsimp [W]; linarith)
  calc
    _ ≤ ∑ x : S, ‖f (P⁻¹ • mixedEmbedding K (x.val:K))‖ := by
      unfold compactTraceWeylSum traceWeylSum
      apply (norm_sum_le _ _).trans_eq
      simp only [norm_mul,traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]
      rfl
    _ ≤ (S.card:ℝ)*W := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hw x)
    _ ≤ (2*(3:ℝ)^finrank ℚ K*(A*P)^finrank ℚ K)*W :=
      mul_le_mul_of_nonneg_right hcard hW.le
    _ = _ := by rw [mul_pow]; ring

#print axioms compactTraceWeylSum_trivial_bound
end WaringSiegel.WSL3

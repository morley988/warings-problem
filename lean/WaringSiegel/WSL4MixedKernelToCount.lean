import WaringSiegel.WSL4MixedSixthFourier

/-! # The actual cubic kernel average is bounded by the literal congruent count -/
noncomputable section
open MeasureTheory NumberField
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem trace_coprime_mixed_sixth_le_congruent_count {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} [Fintype α] [Fintype β]
      (a : 𝓞 K) (ha : a ≠ 0)
      [Fintype (PrincipalResidueRing a)] [Fintype (traceTorusMul a).ker]
      (x : α → 𝓞 K) (y : β → 𝓞 K),
      (∫ q, ‖traceCoprimeWeylSum a 3 x (fun _ => 1) q‖^2 *
        ‖traceWeylSum 3 y (fun _ => 1) (traceTorusMul a q)‖^4 ∂traceHaar) ≤
        C*((Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℝ))^ε *
          mixedResidueCongruentCount a x y := by
  obtain ⟨C,hC,hbound⟩ := trace_cubic_mixed_moment_epsilon_reduction (K:=K) hε
  refine ⟨C,hC,?_⟩
  intro α β _ _ a ha _ _ x y
  exact (hbound a ha x (fun _ => 1) y (fun _ => 1)).trans
    (mul_le_mul_of_nonneg_left (trace_residue_second_fourth_integral_le_count a x y)
      (show 0≤C*((Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℝ))^ε by positivity))

#print axioms trace_coprime_mixed_sixth_le_congruent_count
end WaringSiegel.WSL4Local

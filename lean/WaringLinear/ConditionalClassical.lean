import WaringLinear.ConditionalGlobal
import WaringSharp.AllOrders
import WaringLinear.RationalTransfer

/-! # A conditional linear bound for the classical positive Waring predicate -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringEnvelope WaringDualEnvelope
namespace WaringLinear

theorem sharp_waring_of_analytic_inputs (W : ℝ → TraceSumFamily ℚ) (k : ℕ) (hk : 21≤k)
    (seed : SelectedSeeds (cutoffAdmissible W k) k)
    (finiteStep : k<180000^2 → ShorteningStep DualStage (cutoffAdmissible W k) k)
    (largeStep : 180000^2≤k → ShorteningStep WaringSharpTail.Branch (cutoffAdmissible W k) k)
    (arcs : ∀ r a : ℕ, Even r → Even a → 0<a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
        Nonempty (OrdinaryArcBounds (W η) k r a) ∧ UniformCore (W η) k r a) :
    ∃ s : ℕ, ((s+1:ℕ):ℝ)/k<6873/1000 ∧ Waring.WaringBound k s := by
  obtain ⟨s,hs,hG⟩ := sharp_waring_siegel_of_analytic_inputs W k hk seed finiteStep largeStep arcs
  exact ⟨s,hs,classical_of_rational_field k s (by omega) hG⟩

/-- The small-degree input is the explicit historical table. At large degrees,
the hypotheses concern only the moments and arcs of actual Weyl sums. -/
theorem all_degrees_waring_of_analytic_inputs
    (small : ∀ k : Fin 21, 1≤k.val → Waring.WaringBound k.val (WaringEnvelope.smallBounds[k.val]!))
    (analytic : ∀ k : ℕ, 21≤k → ∃ W : ℝ → TraceSumFamily ℚ,
      SelectedSeeds (cutoffAdmissible W k) k ∧
      (k<180000^2 → ShorteningStep DualStage (cutoffAdmissible W k) k) ∧
      (180000^2≤k → ShorteningStep WaringSharpTail.Branch (cutoffAdmissible W k) k) ∧
      ∀ r a : ℕ, Even r → Even a → 0<a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
        ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
          Nonempty (OrdinaryArcBounds (W η) k r a) ∧ UniformCore (W η) k r a)
    (k : ℕ) (hk : 1≤k) : ∃ s : ℕ, 1000*s≤6873*k ∧ Waring.WaringBound k s := by
  by_cases h : k<21
  · let i : Fin 21 := ⟨k,h⟩
    exact ⟨_, WaringSharp.small_degree_prices i hk,small i hk⟩
  · have hl : 21≤k := by omega
    obtain ⟨W,seed,f,t,arcs⟩ := analytic k hl
    obtain ⟨s,hp,rep⟩ := sharp_waring_of_analytic_inputs W k hl seed f t arcs
    have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have h' := (div_lt_iff₀ hk').mp hp
    push_cast at h'
    exact ⟨s, by exact_mod_cast (show 1000*(s:ℝ)≤6873*k by linarith only [h']), rep⟩

#print axioms sharp_waring_of_analytic_inputs
#print axioms all_degrees_waring_of_analytic_inputs
end WaringLinear

import WaringDualEnvelope.AllDegrees
import WaringDualEnvelope.SemanticMenu
import WaringEnvelope.Price

/-! # The 6.874 real all-degree conductor envelope -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope

/-- The full family of real conductors at every retained height and a terminal
price below 6.874, with degree-aware choices and the radical loss of each word. -/
theorem full_real_envelope_6874 (k : ℕ) (hk : 21≤k) :
    ∃ (c : WaringDualEnvelope.Config) (s : State) (R : ℝ),
      c.first≤k ∧ (c.last=0 ∨ k≤c.last) ∧
      MathematicalMenu DualStage k c.heightTop s.height s.modulus R ∧
      terminalCondition c.toConfig s k ∧ actualPrice c.toConfig s c.heightTop k R < (6874:ℝ)/1000 := by
  obtain ⟨c,hl,hr,hcert⟩ := all_large_degrees_6874 k hk
  obtain ⟨s,R,hmenu,hR,hf⟩ := hcert.mathematicalMenu hl
  have hc := hcert.1
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hK : 0<c.first := by omega
  obtain ⟨hprice,hterminal⟩ := actualPrice_of_checks c.toConfig s c.heightTop (6874*D/1000)
    k R hK hl hr hR hc.1.2 hc.2 hf
  refine ⟨c,s,R,hl,hr,hmenu,hterminal,?_⟩
  convert hprice using 1
  norm_num [D]

#print axioms full_real_envelope_6874
end WaringDualEnvelope

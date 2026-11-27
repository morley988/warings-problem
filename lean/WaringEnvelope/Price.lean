import WaringEnvelope.TerminalDefect
import WaringEnvelope.InfinitePrice
import WaringEnvelope.SemanticMenu

/-! # A uniform real-valued cost for a continuously admissible conductor menu -/
noncomputable section
namespace WaringEnvelope
set_option maxRecDepth 8192

def actualPrice (c : Config) (s : State) (z₀ k : ℕ) (R : ℝ) : ℝ :=
  if c.last=0 then
    2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R+
    (2:ℝ)*V/(F*U)*Real.log ((s.height:ℝ)*14*F^2/T)+(4:ℝ)*V/(F*U)+
    (16:ℝ)*V/U*(Real.log (((64:ℝ)*V/(14*U))*(Real.log k+81/10))/Real.sqrt k)+
    16/Real.sqrt k+6/k
  else
    2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length s.modulus+
      ((fee c).1:ℝ)/(fee c).2+6/k

def terminalCondition (c : Config) (s : State) (k : ℕ) : Prop :=
  if c.last=0 then s.modulus=F*B ∧ T≤s.height*14*F^2 ∧ c.first=c.root^2
  else 2*((s.height:ℝ)/T)/length s.modulus <
    (((fee c).1:ℝ)/(fee c).2)/((k:ℝ)*(Real.log k+81/10))

theorem actualPrice_of_checks (c : Config) (s : State) (z₀ bound k : ℕ) (R : ℝ)
    (hc : 0<c.first) (hk : c.first≤k) (hband : c.last=0 ∨ k≤c.last)
    (hR : R≤(s.cost:ℝ)/D) (hbase : validLog (T-z₀) z₀ c.baseLog=true)
    (hend : validLog (if c.last=0 then c.first else c.last) 1 c.endLog=true)
    (hf : (if c.last=0 then infiniteFinal c s bound else finiteFinal c s bound)=true) :
    actualPrice c s z₀ k R < (bound:ℝ)/D ∧ terminalCondition c s k := by
  by_cases h0 : c.last=0
  · simp only [h0,if_true] at hf hend
    simp only [actualPrice,terminalCondition,h0,if_true]
    refine ⟨infiniteFinal_real_price c s z₀ bound k R hk hR hbase hend hf,?_⟩
    simp only [infiniteFinal,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hf
    exact ⟨hf.2.2.2.1,hf.2.2.2.2.1,hf.2.1⟩
  · simp only [h0,if_false] at hf hend
    simp only [actualPrice,terminalCondition,h0,if_false]
    refine ⟨finiteFinal_real_price c s z₀ bound k R hc hk hR hbase hf,?_⟩
    exact finiteFinal_real_defect c s bound k (by omega) (hband.resolve_left h0) hend hf

/-- Every k≥21 has a continuously admissible family, with all defects and
rounding terms included in an actual real price strictly below 6.919. -/
theorem full_real_envelope_6919 (k : ℕ) (hk : 21≤k) :
    ∃ (c : Config) (s : State) (R : ℝ), c.first≤k ∧ (c.last=0 ∨ k≤c.last) ∧
      MathematicalMenu StageConclusion k top s.height s.modulus R ∧ terminalCondition c s k ∧
      actualPrice c s top k R < (6919:ℝ)/1000 := by
  obtain ⟨c,hl,hr,hcert⟩ := all_large_degrees_6919 k hk
  obtain ⟨s,R,hmenu,hR,hf⟩ := hcert.realProfile
  obtain ⟨hc,_⟩ := config_indices_pos c hcert.1
  obtain ⟨hcfg,_⟩ := hcert
  have hab := hmenu.mathematicalMenu hl hcfg
  simp only [configOK,Bool.and_eq_true,decide_eq_true_eq] at hcfg
  obtain ⟨hprice,hterminal⟩ := actualPrice_of_checks c s top (6919*D/1000) k R hc hl hr hR
    hcfg.1.2 hcfg.2 hf
  refine ⟨c,s,R,hl,hr,hab,hterminal,?_⟩
  convert hprice using 1
  norm_num [D]

#print axioms full_real_envelope_6919
end WaringEnvelope

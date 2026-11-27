import WaringEnvelope.TerminalCosts

/-! # The terminal defect at the actual degree in a finite band -/
noncomputable section
namespace WaringEnvelope

theorem finiteFinal_real_defect (c : Config) (s : State) (bound k : ℕ) (hK : 1≤k)
    (hk : k≤c.last) (hlog : validLog c.last 1 c.endLog=true)
    (hf : finiteFinal c s bound=true) :
    2*((s.height:ℝ)/T)/length s.modulus <
      (((fee c).1:ℝ)/(fee c).2) / ((k:ℝ)*(Real.log k+81/10)) := by
  obtain ⟨a,b,hab⟩ : ∃ a b, fee c=(a,b) := ⟨_,_,Prod.mk.eta.symm⟩
  have hab' := hab
  unfold fee at hab'
  simp only [finiteFinal,hab',Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at hf
  obtain ⟨⟨⟨⟨_,hm⟩,hb⟩,hdef⟩,_⟩ := hf
  rw [hab]
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hmp : (0:ℝ)<s.modulus := by exact_mod_cast hm
  have hbp : (0:ℝ)<b := by exact_mod_cast hb
  have hB : (0:ℝ)<B := by norm_num [B]
  have hD : (0:ℝ)<D := by norm_num [D]
  have hT : (0:ℝ)<T := by norm_num [T]
  have hU : (0:ℝ)<U := by norm_num [U]
  have hV : (0:ℝ)<V := by norm_num [V]
  have hkj : (k:ℝ)≤c.last := by exact_mod_cast hk
  have hlg : 0≤Real.log k := Real.log_nonneg (by exact_mod_cast hK)
  have hmax : Real.log k ≤ (c.endLog:ℝ)/D := by
    apply (Real.log_le_log hkp hkj).trans
    simpa using validLog_sound c.last 1 c.endLog hlog
  have hraw : (2:ℝ)*s.height*B*V*b*c.last*(10*c.endLog+81*D) < a*10*D*T*U*s.modulus :=
    by exact_mod_cast hdef
  have hterm : 2*((s.height:ℝ)/T)/length s.modulus *
      ((c.last:ℝ)*((c.endLog:ℝ)/D+81/10)) < (a:ℝ)/b := by
    unfold length
    field_simp
    linarith only [hraw]
  have hn : 0≤2*((s.height:ℝ)/T)/length s.modulus := by unfold length; positivity
  have hpr := mul_le_mul hkj (add_le_add_right hmax (81/10))
    (by linarith : 0≤Real.log k+81/10) (Nat.cast_nonneg c.last)
  exact (lt_div_iff₀ (mul_pos hkp (by linarith))).2 ((mul_le_mul_of_nonneg_left hpr hn).trans_lt hterm)

#print axioms finiteFinal_real_defect
end WaringEnvelope

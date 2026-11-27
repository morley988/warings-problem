import WaringEnvelope.FiniteShortening
import WaringDualEnvelope.FiniteOrders
import WaringDualEnvelope.SeedHeights

/-! # Exact hypotheses for the finite conductor update -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope

def SelectedSeeds (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ z, T≤20*z → 3*z≤T → P (evenOrder (k*seedOrder z)) (seedDefect z)

theorem Path.terminal_modulus_lt {c : WaringDualEnvelope.Config} {s : State}
    (h : WaringDualEnvelope.Path c start s) (hK : 0<c.first) : s.modulus<B*c.first := by
  cases h with
  | refl => exact Nat.mul_pos (by decide) hK
  | extend _ row => exact (dualRow_properties _ _ _ _ row).2.2.1

theorem finite_shortening_order_with_fee (c : WaringDualEnvelope.Config) (bound k : ℕ) (P : ℕ → ℝ → Prop)
    (hk : 21≤k) (hk₀ : c.first≤k) (hk₁ : k≤c.last) (hfin : c.last≠0) (hsz : SizeFacts c)
    (hc : WaringDualEnvelope.Certified c bound) (h₃ : 3*c.heightTop≤T)
    (seed : SelectedSeeds P k)
    (step : ShorteningStep DualStage P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ k*((fee c.toConfig).1:ℝ)/(fee c.toConfig).2≤(a:ℝ) ∧
      P r x ∧ 0≤x ∧ (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a:ℕ):ℝ)/k<(bound:ℝ)/D := by
  obtain ⟨cfg,s,path,hfinal⟩ := hc
  have hcfg := cfg
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at hcfg
  have hm := path.terminal_modulus_lt (by omega : 0<c.first)
  have hmk := hm.trans_le (Nat.mul_le_mul_left B hk₀)
  rcases path.mathematicalMenu hk₀ cfg with h|⟨R,menu,hR⟩
  · simp [h,hfin,finiteFinal,start] at hfinal
  have hf : finiteFinal c.toConfig s bound=true := by simpa [hfin] using hfinal
  obtain ⟨hs₀,hs₁,hn,hd,hratio,_⟩ := hsz
  have htop : 0<c.heightTop := by
    have hT : 0<T := by decide
    omega
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at cfg
  have hK : 0<c.first := by omega
  have hlog := cfg.2
  simp only [hfin,if_false] at hlog
  have stop := finiteFinal_real_defect c.toConfig s bound k (by omega) hk₁ hlog hf
  have charge := finiteFinal_real_price c.toConfig s c.heightTop bound k R hK hk₀ hR cfg.1.2 hf
  obtain ⟨p⟩ := menu.indexed htop
  have hn' : (0:ℝ)<(fee c.toConfig).1 := by exact_mod_cast hn
  have hd' : (0:ℝ)<(fee c.toConfig).2 := by exact_mod_cast hd
  have hs := p.guarded_finite_order_with_fee P hk hs₀ h₃ hmk _ (div_pos hn' hd')
    ((div_le_one hd').2 (by exact_mod_cast hratio)) stop (seed _ hs₀ h₃) step
  obtain ⟨r,a,x,er,ea,ha,hP,hx,hgap,hprice⟩ := hs
  exact ⟨r,a,x,er,ea,by simpa only [mul_div_assoc] using ha,hP,hx,hgap,hprice.trans charge⟩

theorem finite_shortening_order (c : WaringDualEnvelope.Config) (bound k : ℕ) (P : ℕ → ℝ → Prop)
    (hk : 21≤k) (hk₀ : c.first≤k) (hk₁ : k≤c.last) (hfin : c.last≠0) (hsz : SizeFacts c)
    (hc : WaringDualEnvelope.Certified c bound) (h₃ : 3*c.heightTop≤T)
    (seed : SelectedSeeds P k)
    (step : ShorteningStep DualStage P k) : MomentOrder P k ((bound:ℝ)/D) := by
  obtain ⟨r,a,x,er,ea,_,hP,hx,hgap,hprice⟩ := finite_shortening_order_with_fee c bound k P
    hk hk₀ hk₁ hfin hsz hc h₃ seed step
  exact ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩

#print axioms finite_shortening_order_with_fee
#print axioms finite_shortening_order
end WaringDualEnvelope

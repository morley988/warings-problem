import WaringDualEnvelope.SelectedConfig
import WaringDualEnvelope.Price
import WaringEnvelope.FiniteOrder

/-! # Certified even moment orders for all finite bands -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope

def SeedMoments (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ z, T≤20*z → 2*z≤T → P (evenOrder (k*seedOrder z)) (seedDefect z)

def MomentOrder (P : ℕ → ℝ → Prop) (k : ℕ) (price : ℝ) : Prop :=
  ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
    (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧ ((r+a:ℕ):ℝ)/k<price

theorem finite_certified_order (c : WaringDualEnvelope.Config) (bound k : ℕ) (P : ℕ → ℝ → Prop)
    (hk : 21≤k) (hk₀ : c.first≤k) (hk₁ : k≤c.last) (hfin : c.last≠0) (hsz : SizeFacts c)
    (hc : WaringDualEnvelope.Certified c bound) (seed : SeedMoments P k)
    (step : StageUpdate DualStage P k) : MomentOrder P k ((bound:ℝ)/D) := by
  obtain ⟨s,R,menu,hR,hfinal⟩ := hc.mathematicalMenu hk₀
  have hf : finiteFinal c.toConfig s bound=true := by simpa [hfin] using hfinal
  obtain ⟨hs₀,hs₁,hn,hd,hratio,_⟩ := hsz
  have htop : 0<c.heightTop := by
    have hT : 0<T := by decide
    omega
  have cfg := hc.1
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at cfg
  have hK : 0<c.first := by omega
  have hlog := cfg.2
  simp only [hfin,if_false] at hlog
  have stop := finiteFinal_real_defect c.toConfig s bound k (by omega) hk₁ hlog hf
  have charge := finiteFinal_real_price c.toConfig s c.heightTop bound k R hK hk₀ hR cfg.1.2 hf
  obtain ⟨p⟩ := menu.indexed htop
  have hn' : (0:ℝ)<(fee c.toConfig).1 := by exact_mod_cast hn
  have hd' : (0:ℝ)<(fee c.toConfig).2 := by exact_mod_cast hd
  have hs := p.finite_order P hk hs₀ hs₁ _ (div_pos hn' hd')
    ((div_le_one hd').2 (by exact_mod_cast hratio)) stop (seed _ hs₀ hs₁) step
  obtain ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩ := hs
  exact ⟨r,a,x,er,ea,hP,hx,hgap,hprice.trans charge⟩

theorem finite_moment_orders_6874 (k : ℕ) (hk : 21≤k) (hcap : k<10^12)
    (P : ℕ → ℝ → Prop) (seed : SeedMoments P k) (step : StageUpdate DualStage P k) :
    MomentOrder P k (6874/1000) := by
  obtain ⟨c,hl,hr,hsz,hc⟩ := selected_6874 k hk
  have hfin : c.last≠0 := by
    intro h
    have zero := hsz.2.2.2.2.2 h
    omega
  have h := finite_certified_order c (6874*D/1000) k P hk hl (hr.resolve_left hfin) hfin hsz hc seed step
  convert h using 1
  norm_num [D]

#print axioms finite_certified_order
#print axioms finite_moment_orders_6874
end WaringDualEnvelope

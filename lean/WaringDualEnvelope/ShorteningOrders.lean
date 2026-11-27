import WaringDualEnvelope.FiniteShortening
import WaringDualEnvelope.RealStages

/-! # Integer moment orders through the unbounded degree band -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope Set MeasureTheory
set_option maxRecDepth 8192

theorem infinite_shortening_order (c : WaringDualEnvelope.Config) (bound k : ℕ) (P : ℕ → ℝ → Prop)
    (hk : c.first≤k) (h0 : c.last=0) (sz : SizeFacts c)
    (cert : WaringDualEnvelope.Certified c bound) (h₃ : 3*c.heightTop≤T) (seed : SelectedSeeds P k)
    (step : ShorteningStep DualStage P k) : MomentOrder P k ((bound:ℝ)/D) := by
  obtain ⟨cfg,s,path,hfinal⟩ := cert
  have hf : infiniteFinal c.toConfig s bound=true := by simpa [h0] using hfinal
  have checks := hf
  simp only [infiniteFinal,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checks
  have hfirst : c.first=c.root^2 := checks.2.1
  have hlarge : 10^8≤c.first := checks.2.2.1
  have hm : s.modulus=F*B := checks.2.2.2.1
  have hZ : T≤s.height*14*F^2 := checks.2.2.2.2.1
  have hmpos : 0<s.modulus := by rw [hm];decide
  have hK : 21≤c.first := by omega
  have hr : 0<c.root := by
    by_contra! h
    have e : c.root=0 := by omega
    simp [e] at hfirst
    omega
  rcases path.mathematicalMenu hk cfg with h|⟨R,menu,hR⟩
  · simp [h,start] at hmpos
  obtain ⟨hlo,hhi,_,_,_,_⟩ := sz
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at cfg
  have htop : 0<c.heightTop := by omega
  have hmk := (path.terminal_modulus_lt (by omega : 0<c.first)).trans_le (Nat.mul_le_mul_left B hk)
  have price := infiniteFinal_real_price c.toConfig s c.heightTop bound k R hk hR cfg.1.2
    (by simpa [h0] using cfg.2) hf
  obtain ⟨p⟩ := menu.indexed htop
  let v : ℝ := (U:ℝ)/V
  let cap := Real.sqrt (k:ℝ)/8
  let fee := 16/Real.sqrt (k:ℝ)
  have hk' : (10^8:ℝ)≤(k:ℝ) := by exact_mod_cast hlarge.trans hk
  have hkp : (0:ℝ)<k := by linarith
  have hk1 : 1≤(k:ℝ) := by linarith
  have hlog := Real.log_nonneg hk1
  have hroot : 0<Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hkp
  have hF : (0:ℝ)<F := by norm_num [F]
  have hv : 0<v := by norm_num [v,U,V]
  have hv1 : v≤1 := by norm_num [v,U,V]
  have hcap : (F:ℝ)≤cap := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).2
    apply (Real.le_sqrt (by positivity) hkp.le).2
    calc
      ((F:ℝ)*8)^2 ≤ 10^8 := by norm_num [F]
      _ ≤ (k:ℝ) := hk'
  have hfee : 0<fee := div_pos (by norm_num) hroot
  have hfee1 : fee≤1 := by
    apply (div_le_one hroot).2
    exact (Real.le_sqrt (by norm_num) hkp.le).2 (by linarith)
  have hden : 0<(k:ℝ)*(Real.log k+81/10) := mul_pos hkp (by linarith)
  have hsdef : clippedStop k=fee/((k:ℝ)*(Real.log k+81/10)) := by
    unfold clippedStop fee
    rw [div_div]
    congr 1
    ring
  have ht : 0<clippedStop k := by rw [hsdef]; exact div_pos hfee hden
  have ⟨hz,_,hstart,_,hseed⟩ := seed_range c.heightTop hlo hhi
  have hle : clippedStop k≤seedDefect c.heightTop := by
    apply le_trans _ (hz.trans hstart)
    rw [hsdef];apply (div_le_iff₀ hden).2
    nlinarith only [hk',hfee1,mul_nonneg hkp.le hlog]
  have hlast : p.lengthAt p.N=v*F := by
    unfold IndexedStages.lengthAt length
    rw [p.lastModulus,hm];push_cast
    norm_num [v,U,V,B,F]
  have hheight : 1/(14*(F:ℝ)^2)≤p.heightAt p.N := by
    have hT : (0:ℝ)<T := by norm_num [T]
    unfold IndexedStages.heightAt
    rw [p.lastHeight]
    apply (div_le_div_iff₀ (by positivity) hT).2
    rw [one_mul,←mul_assoc]
    exact_mod_cast hZ
  have integr := p.extended_degree_integral v F k (seedDefect c.heightTop) hv hv1 hF hk1
    hcap hlast hheight (p.starting_knee hlo hhi)
  obtain ⟨r,a,x,er,ea,hP,hx,hxt,ha,hord⟩ := even_moment_order_of_integral (Guarded P k) k (by omega)
    (p.extendedDrift v F cap) (seedDefect c.heightTop) (clippedStop k) (seedOrder c.heightTop) fee
    ht.le hle hseed hfee.le (p.continuous_extendedDrift v F cap hF).continuousOn
    (fun t h => p.positive_extendedDrift v F cap t (ht.trans_le h.1))
    ((p.monotone_extendedDrift v F cap hv hF hcap).monotoneOn _) (guarded_seed hlo h₃ (seed _ hlo h₃)) (fun r x hP hx => by
      rcases p.extendedDrift_attained v F cap x hF hcap with ⟨i,hi,he⟩|⟨M,hM,he⟩
      · rw [he];exact p.guarded_row hi hhi hmk step hP hx
      · rw [he]
        obtain ⟨hrk,er,hrP⟩ := hP
        have hM1 : 1<M := (by norm_num [F] : (1:ℝ)<F).trans_le hM.1
        have hMk : M<(k:ℝ) := by
          apply lt_of_le_of_lt hM.2
          apply (div_lt_iff₀ (by norm_num : (0:ℝ)<8)).2
          have hl : Real.sqrt (k:ℝ)≤k := (Real.sqrt_le_iff).2 ⟨hkp.le,by nlinarith only [sq_nonneg ((k:ℝ)-1),hk1]⟩
          linarith only [hl,hkp]
        have hMp : 0<M := zero_lt_one.trans hM1
        refine ⟨by omega,er.add (by decide : Even 2),?_⟩
        exact step r x _ M hrk er hrP hx (by positivity) hM1 hMk
          (extended_real_conductors h0 hK hr hk path hf M hM))
  rw [hsdef] at hxt
  refine ⟨r,a,x,er,ea,hP.2.2,hx,ordinary_minor_gap k a (by omega) x fee hfee hxt ha,?_⟩
  apply lt_trans _ price
  have hs₀ : p.heightAt 0=normalizedHeight c.heightTop := by unfold IndexedStages.heightAt normalizedHeight;rw [p.first]
  have hsN : p.heightAt p.N=(s.height:ℝ)/T := by unfold IndexedStages.heightAt;rw [p.lastHeight]
  have hcoef2 : 2/(v*F)=(2:ℝ)*V/(F*U) := by norm_num [v,F,U,V]
  have hcoef4 : 4/(v*F)=(4:ℝ)*V/(F*U) := by norm_num [v,F,U,V]
  have hcoef16 : 16/v=(16:ℝ)*V/U := by norm_num [v,U,V]
  have hcoef64 : 64/(14*v)=(64:ℝ)*V/(14*U) := by norm_num [v,U,V]
  rw [hs₀,hsN,hcoef2,hcoef4,hcoef16,hcoef64,
    show 14*(F:ℝ)^2*((s.height:ℝ)/T)=s.height*14*(F:ℝ)^2/T by ring] at integr
  dsimp only [fee,cap] at hord
  linarith only [hord,integr,seed_price_identity c.heightTop htop hhi]

theorem all_shortening_orders_6874 (k : ℕ) (hk : 21≤k) (P : ℕ → ℝ → Prop)
    (seed : SelectedSeeds P k) (step : ShorteningStep DualStage P k) : MomentOrder P k (6874/1000) := by
  obtain ⟨c,hl,hr,h₃,sz,hc⟩ := selected_heights_6874 k hk
  by_cases h0 : c.last=0
  · have h := infinite_shortening_order c (6874*D/1000) k P hl h0 sz hc h₃ seed step
    convert h using 1
    norm_num [D]
  · have h := finite_shortening_order c (6874*D/1000) k P hk hl (hr.resolve_left h0) h0 sz hc h₃ seed step
    convert h using 1
    norm_num [D]

#print axioms infinite_shortening_order
#print axioms all_shortening_orders_6874
end WaringDualEnvelope

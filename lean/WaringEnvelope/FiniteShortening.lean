import WaringEnvelope.ShorteningRanges

/-! # Finite certified schedules with the stated shortening ranges -/
noncomputable section
namespace WaringEnvelope.IndexedStages
open Set MeasureTheory
variable {C k z₀ z m R} (p : IndexedStages C k z₀ z m R)
include p in
theorem guarded_finite_order_with_fee (P : ℕ → ℝ → Prop) (hk : 21≤k)
    (hlo : T≤20*z₀) (h₃ : 3*z₀≤T) (hmod : m<B*k) (fee : ℝ) (hf : 0<fee) (hf₁ : fee≤1)
    (hstop : 2*((z:ℝ)/T)/length m<fee/((k:ℝ)*(Real.log k+81/10)))
    (hseed : P (evenOrder (k*seedOrder z₀)) (seedDefect z₀))
    (hstep : ShorteningStep C P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ k*fee≤(a:ℝ) ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a:ℕ):ℝ)/k < 2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length m+fee+6/k := by
  have hhi : 2*z₀≤T := by omega
  let target := fee/((k:ℝ)*(Real.log k+81/10))
  have hk' : (21:ℝ)≤k := by exact_mod_cast hk
  have hlog := Real.log_nonneg (show 1≤(k:ℝ) by linarith)
  have hden : 0<(k:ℝ)*(Real.log k+81/10) := mul_pos (by linarith) (by linarith)
  have ht : 0<target := div_pos hf hden
  have ⟨hl,_,h₀,_,hv⟩ := seed_range z₀ hlo hhi
  have hd : target≤seedDefect z₀ := by
    apply le_trans _ (hl.trans h₀)
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (show 0≤(k:ℝ) by linarith) hlog]
  have hstar : 2*p.heightAt p.N/p.lengthAt p.N≤target := by
    unfold heightAt lengthAt
    rw [p.lastHeight,p.lastModulus]
    exact hstop.le
  have price := p.drift_integral_bound (seedDefect z₀) target ht (p.starting_knee hlo hhi) hstar
  obtain ⟨r,a,x,er,ea,hP,hx,hxt,ha,hs⟩ := even_moment_order_of_integral (Guarded P k) k (by omega) p.drift
    (seedDefect z₀) target (seedOrder z₀) fee ht.le hd hv hf.le
    p.continuous_drift.continuousOn (fun t h => p.positive_drift _ (ht.trans_le h.1))
    (p.monotone_drift.monotoneOn _) (guarded_seed hlo h₃ hseed) (fun r x hp hx => by
      obtain ⟨i,hi,he⟩ := p.exists_active x
      rw [he]
      exact p.guarded_row hi hhi hmod hstep hp hx)
  refine ⟨r,a,x,er,ea,ha,hP.2.2,hx,ordinary_minor_gap k a (by omega) x fee hf hxt ha,?_⟩
  have h₀' : p.heightAt 0=normalizedHeight z₀ := by unfold heightAt normalizedHeight;rw [p.first]
  have hN : p.lengthAt p.N=length m := by unfold lengthAt; rw [p.lastModulus]
  rw [h₀',hN] at price
  have hz : 0<z₀ := p.first ▸ p.posHeight 0 (by omega)
  linarith [seed_price_identity z₀ hz hhi]

include p in
theorem guarded_finite_order (P : ℕ → ℝ → Prop) (hk : 21≤k)
    (hlo : T≤20*z₀) (h₃ : 3*z₀≤T) (hmod : m<B*k) (fee : ℝ) (hf : 0<fee) (hf₁ : fee≤1)
    (hstop : 2*((z:ℝ)/T)/length m<fee/((k:ℝ)*(Real.log k+81/10)))
    (hseed : P (evenOrder (k*seedOrder z₀)) (seedDefect z₀))
    (hstep : ShorteningStep C P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a:ℕ):ℝ)/k < 2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length m+fee+6/k := by
  obtain ⟨r,a,x,er,ea,_,hP,hx,hgap,hprice⟩ := p.guarded_finite_order_with_fee
    P hk hlo h₃ hmod fee hf hf₁ hstop hseed hstep
  exact ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩

#print axioms guarded_finite_order_with_fee
#print axioms guarded_finite_order
end WaringEnvelope.IndexedStages

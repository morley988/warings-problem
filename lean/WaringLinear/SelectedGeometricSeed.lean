import WaringLinear.GeometricLinearOrders
import WaringDualEnvelope.FiniteShortening
import WaringSharp.ShorteningOrders

/-! # The geometric smooth seed at the actual scheduled heights -/
noncomputable section
open WaringEnvelope WaringDualEnvelope Waring Waring.SmoothMoments

namespace WaringDualEnvelope
theorem finite_shortening_at_selected_seed (c : WaringDualEnvelope.Config) (bound k : ℕ) (P : ℕ → ℝ → Prop)
    (hk : 21≤k) (hk₀ : c.first≤k) (hk₁ : k≤c.last) (hfin : c.last≠0) (hsz : SizeFacts c)
    (hc : WaringDualEnvelope.Certified c bound) (h₃ : 3*c.heightTop≤T)
    (seed : P (evenOrder (k*seedOrder c.heightTop)) (seedDefect c.heightTop))
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
    ((div_le_one hd').2 (by exact_mod_cast hratio)) stop seed step
  obtain ⟨r,a,x,er,ea,ha,hP,hx,hgap,hprice⟩ := hs
  exact ⟨r,a,x,er,ea,by simpa only [mul_div_assoc] using ha,hP,hx,hgap,hprice.trans charge⟩

end WaringDualEnvelope

namespace WaringSharp
theorem selected_heights_geometric (k : ℕ) (hl : 21≤k) (hu : k<180000^2) :
    ∃ c : WaringDualEnvelope.Config, c.first≤k ∧ k≤c.last ∧ c.last≠0 ∧
    1997*T≤20000*c.heightTop ∧ 3*c.heightTop≤T ∧ SizeFacts c ∧ WaringDualEnvelope.Certified c (6873*D/1000-ceilDiv D c.first) := by
  by_cases h0 : k≤33
  · exact ⟨Band00.cfg, by change 21≤_;omega, h0, by decide, by decide, by decide, by decide +kernel, Band00.checked⟩
  by_cases h1 : k≤54
  · exact ⟨Band01.cfg, by change 34≤_;omega, h1, by decide, by decide, by decide, by decide +kernel, Band01.checked⟩
  by_cases h2 : k≤88
  · exact ⟨Band02.cfg, by change 55≤_;omega, h2, by decide, by decide, by decide, by decide +kernel, Band02.checked⟩
  by_cases h3 : k≤142
  · exact ⟨Band03.cfg, by change 89≤_;omega, h3, by decide, by decide, by decide, by decide +kernel, Band03.checked⟩
  by_cases h4 : k≤228
  · exact ⟨Band04.cfg, by change 143≤_;omega, h4, by decide, by decide, by decide, by decide +kernel, Band04.checked⟩
  by_cases h5 : k≤366
  · exact ⟨Band05.cfg, by change 229≤_;omega, h5, by decide, by decide, by decide, by decide +kernel, Band05.checked⟩
  by_cases h6 : k≤587
  · exact ⟨Band06.cfg, by change 367≤_;omega, h6, by decide, by decide, by decide, by decide +kernel, Band06.checked⟩
  by_cases h7 : k≤940
  · exact ⟨Band07.cfg, by change 588≤_;omega, h7, by decide, by decide, by decide, by decide +kernel, Band07.checked⟩
  by_cases h8 : k≤1505
  · exact ⟨Band08.cfg, by change 941≤_;omega, h8, by decide, by decide, by decide, by decide +kernel, Band08.checked⟩
  by_cases h9 : k≤2409
  · exact ⟨Band09.cfg, by change 1506≤_;omega, h9, by decide, by decide, by decide, by decide +kernel, Band09.checked⟩
  by_cases h10 : k≤3856
  · exact ⟨Band10.cfg, by change 2410≤_;omega, h10, by decide, by decide, by decide, by decide +kernel, Band10.checked⟩
  by_cases h11 : k≤6171
  · exact ⟨Band11.cfg, by change 3857≤_;omega, h11, by decide, by decide, by decide, by decide +kernel, Band11.checked⟩
  by_cases h12 : k≤9875
  · exact ⟨Band12.cfg, by change 6172≤_;omega, h12, by decide, by decide, by decide, by decide +kernel, Band12.checked⟩
  by_cases h13 : k≤15801
  · exact ⟨Band13.cfg, by change 9876≤_;omega, h13, by decide, by decide, by decide, by decide +kernel, Band13.checked⟩
  by_cases h14 : k≤25283
  · exact ⟨Band14.cfg, by change 15802≤_;omega, h14, by decide, by decide, by decide, by decide +kernel, Band14.checked⟩
  by_cases h15 : k≤40454
  · exact ⟨Band15.cfg, by change 25284≤_;omega, h15, by decide, by decide, by decide, by decide +kernel, Band15.checked⟩
  by_cases h16 : k≤64728
  · exact ⟨Band16.cfg, by change 40455≤_;omega, h16, by decide, by decide, by decide, by decide +kernel, Band16.checked⟩
  by_cases h17 : k≤103566
  · exact ⟨Band17.cfg, by change 64729≤_;omega, h17, by decide, by decide, by decide, by decide +kernel, Band17.checked⟩
  by_cases h18 : k≤165707
  · exact ⟨Band18.cfg, by change 103567≤_;omega, h18, by decide, by decide, by decide, by decide +kernel, Band18.checked⟩
  by_cases h19 : k≤265132
  · exact ⟨Band19.cfg, by change 165708≤_;omega, h19, by decide, by decide, by decide, by decide +kernel, Band19.checked⟩
  by_cases h20 : k≤424212
  · exact ⟨Band20.cfg, by change 265133≤_;omega, h20, by decide, by decide, by decide, by decide +kernel, Band20.checked⟩
  by_cases h21 : k≤678740
  · exact ⟨Band21.cfg, by change 424213≤_;omega, h21, by decide, by decide, by decide, by decide +kernel, Band21.checked⟩
  by_cases h22 : k≤1085985
  · exact ⟨Band22.cfg, by change 678741≤_;omega, h22, by decide, by decide, by decide, by decide +kernel, Band22.checked⟩
  by_cases h23 : k≤1737577
  · exact ⟨Band23.cfg, by change 1085986≤_;omega, h23, by decide, by decide, by decide, by decide +kernel, Band23.checked⟩
  by_cases h24 : k≤2780124
  · exact ⟨Band24.cfg, by change 1737578≤_;omega, h24, by decide, by decide, by decide, by decide +kernel, Band24.checked⟩
  by_cases h25 : k≤4448200
  · exact ⟨Band25.cfg, by change 2780125≤_;omega, h25, by decide, by decide, by decide, by decide +kernel, Band25.checked⟩
  by_cases h26 : k≤7117121
  · exact ⟨Band26.cfg, by change 4448201≤_;omega, h26, by decide, by decide, by decide, by decide +kernel, Band26.checked⟩
  by_cases h27 : k≤11387395
  · exact ⟨Band27.cfg, by change 7117122≤_;omega, h27, by decide, by decide, by decide, by decide +kernel, Band27.checked⟩
  by_cases h28 : k≤18219833
  · exact ⟨Band28.cfg, by change 11387396≤_;omega, h28, by decide, by decide, by decide, by decide +kernel, Band28.checked⟩
  by_cases h29 : k≤29151734
  · exact ⟨Band29.cfg, by change 18219834≤_;omega, h29, by decide, by decide, by decide, by decide +kernel, Band29.checked⟩
  by_cases h30 : k≤46642776
  · exact ⟨Band30.cfg, by change 29151735≤_;omega, h30, by decide, by decide, by decide, by decide +kernel, Band30.checked⟩
  by_cases h31 : k≤74628443
  · exact ⟨Band31.cfg, by change 46642777≤_;omega, h31, by decide, by decide, by decide, by decide +kernel, Band31.checked⟩
  by_cases h32 : k≤119405510
  · exact ⟨Band32.cfg, by change 74628444≤_;omega, h32, by decide, by decide, by decide, by decide +kernel, Band32.checked⟩
  by_cases h33 : k≤191048817
  · exact ⟨Band33.cfg, by change 119405511≤_;omega, h33, by decide, by decide, by decide, by decide +kernel, Band33.checked⟩
  by_cases h34 : k≤305678108
  · exact ⟨Band34.cfg, by change 191048818≤_;omega, h34, by decide, by decide, by decide, by decide +kernel, Band34.checked⟩
  by_cases h35 : k≤489084974
  · exact ⟨Band35.cfg, by change 305678109≤_;omega, h35, by decide, by decide, by decide, by decide +kernel, Band35.checked⟩
  by_cases h36 : k≤782535960
  · exact ⟨Band36.cfg, by change 489084975≤_;omega, h36, by decide, by decide, by decide, by decide +kernel, Band36.checked⟩
  by_cases h37 : k≤1252057537
  · exact ⟨Band37.cfg, by change 782535961≤_;omega, h37, by decide, by decide, by decide, by decide +kernel, Band37.checked⟩
  by_cases h38 : k≤2003292060
  · exact ⟨Band38.cfg, by change 1252057538≤_;omega, h38, by decide, by decide, by decide, by decide +kernel, Band38.checked⟩
  by_cases h39 : k≤3205267297
  · exact ⟨Band39.cfg, by change 2003292061≤_;omega, h39, by decide, by decide, by decide, by decide +kernel, Band39.checked⟩
  by_cases h40 : k≤5128427676
  · exact ⟨Band40.cfg, by change 3205267298≤_;omega, h40, by decide, by decide, by decide, by decide +kernel, Band40.checked⟩
  by_cases h41 : k≤8205484283
  · exact ⟨Band41.cfg, by change 5128427677≤_;omega, h41, by decide, by decide, by decide, by decide +kernel, Band41.checked⟩
  by_cases h42 : k≤13128774854
  · exact ⟨Band42.cfg, by change 8205484284≤_;omega, h42, by decide, by decide, by decide, by decide +kernel, Band42.checked⟩
  by_cases h43 : k≤21006039768
  · exact ⟨Band43.cfg, by change 13128774855≤_;omega, h43, by decide, by decide, by decide, by decide +kernel, Band43.checked⟩
  by_cases h44 : k≤33609663630
  · exact ⟨Band44.cfg, by change 21006039769≤_;omega, h44, by decide, by decide, by decide, by decide +kernel, Band44.checked⟩
  omega
end WaringSharp

namespace WaringLinear

theorem scheduled_geometric_allowance (z : ℕ) (hz : 1997*T≤20000*z) (hhi : 3*z≤T) :
    -(2:ℝ)*Real.log (seedDefect z) ≤ seedOrder z+131/100 := by
  have hlo : T≤20*z := by omega
  obtain ⟨hz',_,_,hD,_⟩ := seed_range z hlo (by omega)
  have H : (1997:ℝ)/20000≤normalizedHeight z := by
    unfold normalizedHeight
    have hT : (0:ℝ)<T := by norm_num [T]
    apply (le_div_iff₀ hT).2
    have h : (1997:ℝ)*T≤20000*z := by exact_mod_cast hz
    linarith only [h]
  have hz₁ : 0<1-normalizedHeight z := by linarith
  have hlow : (1997:ℝ)/18003≤seedDefect z := (le_div_iff₀ hz₁).2 (by linarith only [H])
  have hd : 0<seedDefect z := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0:ℝ)<1997/18003) hd)
  rw [Real.log_div (by norm_num) hd.ne',Real.log_div (by norm_num) (by norm_num)] at hlog
  have hfrac : (1997:ℝ)/18003/(seedDefect z)≤1+1997/18003-seedDefect z := by
    apply (div_le_iff₀ hd).2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hD)]
  have hnum := validLog_sound 18003 1997 (2199*D/1000) (by decide +kernel)
  norm_num [D] at hnum
  rw [Real.log_div (by norm_num) (by norm_num)] at hnum
  unfold seedOrder
  linarith only [hlog,hfrac,hnum]

/-- At degree k the extra cost is two times the ceiling of 0.655k plus four. -/
def selectedShift (k : ℕ) := 2*⌈(131:ℝ)/200*k⌉₊+4

theorem selected_shifted_subset_seed (k z : ℕ) (hk : 2≤k) (hz : 1997*T≤20000*z) (hhi : 3*z≤T) :
    SubsetMoment k (evenOrder (k*seedOrder z)+selectedShift k) (seedDefect z) := by
  have hlo : T≤20*z := by omega
  obtain ⟨hw,_,h₀,_,hv⟩ := seed_range z hlo (by omega)
  have hd : 0<seedDefect z := by linarith only [hw,h₀]
  have hs := geometric_smooth_seed k (seedDefect z) hk hd
  have h := mul_le_mul_of_nonneg_left (scheduled_geometric_allowance z hz hhi) (Nat.cast_nonneg (α:=ℝ) k)
  have hc := Nat.le_ceil ((131:ℝ)/200*k)
  have hn := Nat.ceil_le_ceil (show -(k:ℝ)*Real.log (seedDefect z)≤
      k*seedOrder z/2+(⌈(131:ℝ)/200*k⌉₊:ℝ) by linarith only [h,hc])
  rw [Nat.ceil_add_natCast (by positivity : 0≤(k:ℝ)*seedOrder z/2)] at hn
  have hu : 2*(⌈-(k:ℝ)*Real.log (seedDefect z)⌉₊+2)≤evenOrder (k*seedOrder z)+selectedShift k := by
    unfold evenOrder selectedShift
    omega
  apply subset_moment_of_smooth _ (admissibleExcess_order_growth hs hu)
  unfold evenOrder selectedShift
  exact ⟨⌈(k:ℝ)*seedOrder z/2⌉₊+⌈(131:ℝ)/200*k⌉₊+2,by omega⟩

private theorem selected_shift_step {k : ℕ} {P : ℕ → ℝ → Prop} {C : ℕ → ℝ → ℝ → ℝ → Prop}
    (step : ShorteningStep C P k) : ShorteningStep C (fun r x => P (r+selectedShift k) x) k := by
  intro r x z M hk er hP hx hz hm hmk hconduct
  have he : Even (selectedShift k) := ⟨⌈(131:ℝ)/200*k⌉₊+2,by unfold selectedShift;omega⟩
  have hh := step (r+selectedShift k) x z M (by omega) (er.add he) hP hx hz hm hmk hconduct
  simpa only [show r+2+selectedShift k=r+selectedShift k+2 by omega] using hh

theorem selected_geometric_orders (k : ℕ) (hk : 21≤k) (P : ℕ → ℝ → Prop)
    (roots : ∀ r x, SubsetMoment k r x → P r x)
    (finiteStep : k<180000^2 → ShorteningStep DualStage P k)
    (largeStep : 180000^2≤k → ShorteningStep WaringSharpTail.Branch P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)<(8183:ℝ)/1000*k+6 := by
  let Q (r : ℕ) (x : ℝ) := P (r+selectedShift k) x
  have ord : ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ Q r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
    by_cases f : k<180000^2
    · obtain ⟨c,hl,hr,hfin,hlo,hhi,sz,hc⟩ := WaringSharp.selected_heights_geometric k hk f
      obtain ⟨r,a,x,er,ea,_,hP,hx,hgap,hprice⟩ := finite_shortening_at_selected_seed c _ k Q hk hl hr hfin sz hc hhi
        (roots _ _ (selected_shifted_subset_seed k _ (by omega) hlo hhi)) (selected_shift_step (finiteStep f))
      refine ⟨r,a,x,er,ea,hP,hx,hgap,?_⟩
      have cfg := hc.1
      simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at cfg
      have hb := WaringSharp.extra_variable_allowance c.first k (by omega) hl
      rw [Nat.cast_add,Nat.cast_one,add_div]
      exact (add_lt_add_right hprice _).trans_le hb
    · have hlarge := le_of_not_gt f
      obtain ⟨r,a,x,er,ea,hP,hx,hgap,hp⟩ := WaringSharpTail.large_degree_shortening_order hlarge Q
        (roots _ _ (selected_shifted_subset_seed k WaringSharpTail.z₀ (by omega) (by decide) (by decide)))
        (selected_shift_step (largeStep hlarge))
      exact ⟨r,a,x,er,ea,hP,hx,hgap,hp.trans (by norm_num)⟩
  obtain ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩ := ord
  have he : Even (selectedShift k) := ⟨⌈(131:ℝ)/200*k⌉₊+2,by unfold selectedShift;omega⟩
  refine ⟨r+selectedShift k,a,x,er.add he,ea,hP,hx,hgap,?_⟩
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have h := (div_lt_iff₀ hk').mp hprice
  have ht := Nat.ceil_lt_add_one (by positivity : 0≤(131:ℝ)/200*k)
  unfold selectedShift
  push_cast at h ⊢
  linarith only [h,ht]

#print axioms selected_shifted_subset_seed
#print axioms selected_geometric_orders
end WaringLinear

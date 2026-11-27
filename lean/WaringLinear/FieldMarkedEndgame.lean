import WaringLinear.MarkedMinorAbsorption

/-! # The marked minor-arc endgame from degree 2501

The terminal allocation pays the old defect using all but one of its
variables at a saving of 1/(15k) on the restricted exponential sum.
The remaining variable supplies the ordinary positive comparison. -/
noncomputable section
open WaringEnvelope WaringDualEnvelope
namespace WaringLinear

private theorem log_bound_pow (n : ℕ) (x : ℝ) (hx : (11/10:ℝ)^n≤x) :
    (n:ℝ)/11≤Real.log x := by
  have hb := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<11/10)
  have hb' : (1:ℝ)/11≤Real.log (11/10:ℝ) := by norm_num at hb ⊢;exact hb
  have h := Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<11/10) n) hx
  rw [Real.log_pow] at h
  calc
    (n:ℝ)/11 = n*(1/11:ℝ) := by ring
    _ ≤ n*Real.log (11/10:ℝ) := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg _)
    _ ≤ _ := h

private theorem gap_transfer {k a : ℕ} {x : ℝ} (hk : 0<k) (ha : 2≤a) (T : ℝ)
    (hT : 0<T) (hlog : T≤Real.log (k:ℝ)+802113/100000)
    (hbig : 15*(a:ℝ)≤((a:ℝ)-1)*T)
    (gap : (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000))) :
    (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) := by
  have hkp : 0<(k:ℝ) := by exact_mod_cast hk
  have hap : (2:ℝ)≤a := by exact_mod_cast ha
  have hden := mul_pos hkp (hT.trans_le hlog)
  have hA := hbig.trans (mul_le_mul_of_nonneg_left hlog (by linarith : 0≤(a:ℝ)-1))
  apply gap.trans_le
  rw [mul_one_div]
  apply (div_le_div_iff₀ hden (by positivity : (0:ℝ)<15*k)).2
  have h := mul_le_mul_of_nonneg_left hA hkp.le
  linarith only [h]

private theorem finite_fee_ge_hundred (c : WaringDualEnvelope.Config) {k : ℕ}
    (hk : 2501≤k) (hf : c.root^2≤k) (hr : 0<c.root) :
    (100:ℝ)≤(k:ℝ)*((fee c.toConfig).1:ℝ)/(fee c.toConfig).2 := by
  have hk' : (2501:ℝ)≤k := by exact_mod_cast hk
  have hr' : (0:ℝ)<c.root := by exact_mod_cast hr
  have hr50 : 50*c.root≤k := by
    by_cases h : c.root≤50
    · omega
    · have hh : 50*c.root≤c.root*c.root := Nat.mul_le_mul_right _ (by omega)
      simpa only [pow_two] using hh.trans (by simpa only [pow_two] using hf)
  have hh : (50:ℝ)*c.root≤k := by exact_mod_cast hr50
  unfold fee
  split
  · norm_num;linarith
  · simp only [Nat.cast_ofNat,Nat.cast_mul]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<10*c.root)).2
    linarith

/-- Every certified finite band at k≥2501 has at least one hundred
terminal variables after even rounding. -/
theorem finite_field_marked_orders (k : ℕ) (lo : 2501≤k) (hi : k<180000^2)
    (P : ℕ → ℝ → Prop) (seed : SelectedSeeds P k) (step : ShorteningStep DualStage P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ 100≤a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  have hk : 21≤k := by omega
  have hk' : (2501:ℝ)≤k := by exact_mod_cast lo
  obtain ⟨c,hl,hr,hfin,h₃,sz,hc⟩ := WaringSharp.selected_heights_6873 k hk hi
  obtain ⟨r,a,x,er,ea,ha,hP,hx,hgap,hprice⟩ := finite_shortening_order_with_fee c _ k P
    hk hl hr hfin sz hc h₃ seed step
  have checks := hc.1
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at checks
  have hroot := checks.2.2.1
  have hroot' := checks.2.2.2.1
  have hrootpos : 0<c.root := by
    by_contra! hr
    have he : c.root=0 := by omega
    rw [he] at hroot'
    norm_num at hroot'
    omega
  have h100 : (100:ℝ)≤a := (finite_fee_ge_hundred c lo (hroot.trans hl) hrootpos).trans ha
  have a100 : 100≤a := by exact_mod_cast h100
  have hlog := log_bound_pow 81 (k:ℝ) ((by norm_num : (11/10:ℝ)^81≤2501).trans hk')
  have tgap := gap_transfer (show 0<k by omega) (show 2≤a by omega) (76/5) (by norm_num)
    (by norm_num at hlog;linarith) (by linarith only [h100]) hgap
  refine ⟨r,a,x,er,ea,a100,hP,hx,tgap,?_⟩
  have hK : 1≤c.first := by have := checks.1;omega
  have hb := WaringSharp.extra_variable_allowance c.first k hK hl
  rw [Nat.cast_add,Nat.cast_one,add_div]
  exact (add_lt_add_right hprice _).trans_le hb

variable {K : Type*} [Field K] [NumberField K]

/-- At all degrees k≥2501 the field order certificate gives a loss-free
moment on the actual trace torus, given the algebraic ED counts and the
marked shortening estimate. At each allowed cutoff the ordinary major
moment, the marked outer bound and the trivial ordinary bound are the
analytic inputs of uniformMarkedMomentAt. -/
theorem field_marked_orders_of_differencing (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 2501≤k) (count : DifferencingCounts W k)
    (shorten : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ 0<a ∧ cutoffAdmissible W k r x ∧ 0≤x ∧
      (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  have hk0 : 21≤k := by omega
  by_cases h : k<180000^2
  · have hs : ShorteningStep DualStage (cutoffAdmissible W k) k := by
      simpa only [ShorteningStep,fieldConductorStage,if_pos h] using shorten
    obtain ⟨r,a,x,er,ea,ha,had,hx,gap,price⟩ := finite_field_marked_orders k hk h _
      (selectedSeeds_of_differencingCounts hk0 count) hs
    exact ⟨r,a,x,er,ea,by omega,had,hx,gap,price⟩
  · obtain ⟨r,a,x,er,ea,had,hx,gap,price⟩ := field_shortening_orders_of_differencing W k hk0 count shorten
    have hlarge : 180000^2≤k := Nat.le_of_not_gt h
    have hk' : (32400000000:ℝ)≤k := by exact_mod_cast hlarge
    have ha : 0<a := by
      by_contra! hr
      rw [show a=0 by omega,Nat.cast_zero,zero_div] at gap
      exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg k) hx)) gap
    have ha2 : 2≤a := by obtain ⟨b,hb⟩ := ea;omega
    have ha' : (2:ℝ)≤a := by exact_mod_cast ha2
    have hlog := log_bound_pow 250 (k:ℝ)
      ((by norm_num : (11/10:ℝ)^250≤32400000000).trans hk')
    have tgap := gap_transfer (show 0<k by omega) ha2 30 (by norm_num)
      (by norm_num at hlog;linarith) (by linarith only [ha']) gap
    exact ⟨r,a,x,er,ea,ha,had,hx,tgap,price⟩

theorem field_marked_loss_free_of_differencing (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 2501≤k) (count : DifferencingCounts W k)
    (shorten : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMarkedMomentAt (W η) k r a (1/(15*k)) := by
  obtain ⟨r,a,x,er,ea,ha,had,_,gap,price⟩ :=
    field_marked_orders_of_differencing W k hk count shorten
  exact ⟨r,a,er,ea,price,cutoff_marked_loss_free_at W k r a x _ er ea ha had gap⟩

#print axioms field_marked_orders_of_differencing
#print axioms finite_field_marked_orders
#print axioms field_marked_loss_free_of_differencing
end WaringLinear

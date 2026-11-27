import WaringLimit.Check
import WaringEnvelope.LogBounds

/-! Real logarithms and the accumulated charge attached to a certified
limiting menu. Finite Fourier estimates, the moment iteration and the
passage to the continuous tail are analytic results in the paper. -/
namespace WaringLimit
open WaringEnvelope (ceilDiv expLoopScale)

set_option maxHeartbeats 800000
set_option maxRecDepth 8192

private theorem d_pos : 0 < D := by decide
private theorem retention_pos : 0 < retentionNum := by decide
private theorem mesh_pos : 0 < B := by decide
private theorem hopDen_pos : 0 < hopDen := by decide
attribute [local irreducible] D T F B hopNum hopDen retentionNum retentionDen z₀

/-- An integer exponential test implies the claimed upper real logarithm. -/
theorem validLog_sound (p q h : Nat) (hv : validLog p q h = true) :
    Real.log ((p:ℝ)/q) ≤ (h:ℝ)/D := by
  simp only [validLog,Bool.and_eq_true,decide_eq_true_eq] at hv
  obtain ⟨⟨hp,hq⟩,v⟩ := hv
  have hd : (0:ℝ) < D := by exact_mod_cast d_pos
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hi : 0 < D^2 := Nat.pow_pos d_pos
  have hi' : (0:ℝ) < (D^2 : Nat) := by exact_mod_cast hi
  apply (Real.log_le_iff_le_exp (div_pos hp' hq')).mpr
  calc
    _ ≤ (expLoopScale (D^2) (h*D) 120 (D^2) : ℝ)/(D^2 : Nat) := by
      apply (div_le_div_iff₀ hq' hi').mpr
      exact_mod_cast v.trans_eq (Nat.mul_comm _ _)
    _ ≤ Real.exp (((h*D : Nat):ℝ)/(D^2:Nat)) :=
      WaringEnvelope.expLoopScale_le_exp (D^2) (h*D) 120 hi
    _ = _ := by push_cast; congr 1; field_simp

private theorem ceiling_covers (a b : Nat) (hb : 0<b) :
    a ≤ ceilDiv a b * b := by
  have h1 := Nat.mod_lt (a+b-1) hb
  have h2 := Nat.mod_add_div (a+b-1) b
  rw [Nat.mul_comm b] at h2
  unfold ceilDiv
  omega

private theorem step_data {s t : State} {c : Nat}
    (ok : step s c = some t) :
    s.m ≤ t.m ∧ 0<t.z ∧ t.z<s.z ∧ s.z*hopDen ≤ t.z*hopNum ∧
    t.cost = s.cost + ceilDiv (2*hopLog*B*retentionDen) (t.m*retentionNum) := by
  cases h : endpoint s.z c with
  | none => simp [step,h] at ok
  | some m =>
    simp only [step,h,bind,Option.bind,pure] at ok
    split at ok
    · contradiction
    · rename_i hn
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true,
        decide_eq_true_eq] at hn
      injection ok with ht
      subst t
      exact ⟨hn.1.1.1.1.1, hn.1.1.1.2, hn.1.1.2, hn.1.2, rfl⟩

private theorem weighted_upper (A den h : Nat) (l : ℝ) (hden : 0<den)
    (hl : l ≤ (h:ℝ)/D) :
    (A:ℝ)*l/den ≤ (ceilDiv (A*h) den : ℝ)/D := by
  have hden' : (0:ℝ)<den := by exact_mod_cast hden
  have hD : (0:ℝ)<D := by exact_mod_cast d_pos
  have hraw := (le_div_iff₀ hD).mp hl
  have hi : A*h ≤ ceilDiv (A*h) den * den := ceiling_covers _ _ hden
  apply (div_le_div_iff₀ hden' hD).mpr
  calc
    _ = (A:ℝ)*(l*D) := by ring
    _ ≤ (A:ℝ)*h := mul_le_mul_of_nonneg_left hraw (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast hi

noncomputable def charge (s t : State) : ℝ :=
  2 * Real.log ((s.z:ℝ)/t.z) * B * retentionDen / ((t.m:ℝ)*retentionNum)

/-- A sum of the actual real logarithmic charges in the finite menu. -/
inductive RealPath : State → State → ℝ → Prop
  | refl : RealPath s s 0
  | snoc : RealPath s t x → step t c = some u → RealPath s u (x+charge t u)

private theorem charge_le {s t : State} {c : Nat} (ok : step s c = some t)
    (hpos : 0<s.m) (hl : Real.log ((hopNum:ℝ)/hopDen) ≤ (hopLog:ℝ)/D) :
    charge s t ≤ ((t.cost:ℝ)-s.cost)/D := by
  obtain ⟨hm,hz,hlt,hr,hcost⟩ := step_data ok
  have hm' : (0:ℝ) < t.m := by exact_mod_cast hpos.trans_le hm
  have hz' : (0:ℝ) < t.z := by exact_mod_cast hz
  have hs' : (0:ℝ) < s.z := by exact_mod_cast hz.trans hlt
  have hden : (0:ℝ) < hopDen := by exact_mod_cast hopDen_pos
  have hd : (0:ℝ) < D := by exact_mod_cast d_pos
  have hkeep : (0:ℝ) < retentionNum := by exact_mod_cast retention_pos
  have hratio : (s.z:ℝ)/t.z ≤ (hopNum:ℝ)/hopDen := by
    apply (div_le_div_iff₀ hz' hden).mpr
    exact_mod_cast hr.trans_eq (Nat.mul_comm _ _)
  have hlog := (Real.log_le_log (div_pos hs' hz') hratio).trans hl
  have HH := weighted_upper (2*B*retentionDen) (t.m*retentionNum) hopLog
    (Real.log ((s.z:ℝ)/t.z)) (Nat.mul_pos (hpos.trans_le hm) retention_pos) hlog
  rw [hcost,Nat.cast_add,add_sub_cancel_left]
  rw [show 2*hopLog*B*retentionDen = (2*B*retentionDen)*hopLog by ac_rfl]
  simp only [Nat.cast_mul,Nat.cast_ofNat] at HH
  exact le_trans (le_of_eq (by unfold charge; ring)) HH

theorem path_real_charge {s t : State} (p : Path s t) (hs : 0<s.m)
    (hl : Real.log ((hopNum:ℝ)/hopDen) ≤ (hopLog:ℝ)/D) :
    0<t.m ∧ ∃ x, RealPath s t x ∧ x ≤ ((t.cost:ℝ)-s.cost)/D := by
  induction p with
  | refl => exact ⟨hs,0,.refl,by simp⟩
  | snoc _ e ih =>
    obtain ⟨hm,v,hv,hb⟩ := ih
    refine ⟨hm.trans_le (step_data e).1,v+_,.snoc hv e,?_⟩
    have h := charge_le e hm hl
    exact (add_le_add hb h).trans_eq (by rw [← add_div]; congr 1; ring)

/-- Finite menu plus the continuous-tail integral from F to infinity.
All logarithms here are the analytic real logarithm. -/
noncomputable def totalCharge (s : State) (x : ℝ) : ℝ :=
  2 + Real.log (((T-z₀ : Nat):ℝ)/z₀) + x +
    (2*retentionDen:ℝ)*Real.log (((s.z*F^2*14 : Nat):ℝ)/T) / (F*retentionNum:Nat) +
    (4*retentionDen:ℝ)/(F*retentionNum:Nat)

theorem certified_real_bound {bound : Nat} (h : Certified bound) :
    ∃ s x, RealPath start s x ∧ totalCharge s x ≤ (bound:ℝ)/D := by
  obtain ⟨_,s,p,c,hc⟩ := h
  simp only [certifiedEnd,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hbase := validLog_sound _ _ _ hc.1.1.1.2
  have hplateau := validLog_sound _ _ _ hc.1.1.2
  have hhop := validLog_sound _ _ _ hc.1.2
  have hden : 0<F*retentionNum := Nat.mul_pos (by decide +kernel) retention_pos
  have hD : (0:ℝ)<D := by exact_mod_cast d_pos
  have hF := weighted_upper (2*retentionDen) (F*retentionNum) plateauLog
    (Real.log (((s.z*F^2*14 : Nat):ℝ)/T)) hden hplateau
  have htail := weighted_upper (4*retentionDen) (F*retentionNum) D 1 hden
    (by rw [div_self hD.ne'])
  obtain ⟨_,v,hp,hv⟩ := path_real_charge p (show 0<start.m from mesh_pos) hhop
  have hcost : finalCost s ≤ bound := hc.2
  have hcost' : ((finalCost s:Nat):ℝ)/D ≤ (bound:ℝ)/D :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcost) hD.le
  refine ⟨s,v,hp,le_trans ?_ hcost'⟩
  simp only [totalCharge,finalCost,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] at *
  simp only [start, Nat.cast_zero,sub_zero,mul_one] at hv htail
  have hconstant : (D:ℝ)*2/D = 2 := by field_simp
  simp only [add_div,hconstant]
  rw [mul_comm (retentionDen:ℝ) 2] at hF
  rw [mul_comm (retentionDen:ℝ) 4] at htail
  exact add_le_add (add_le_add (add_le_add (add_le_add (le_refl 2) hbase) hv) hF) htail

#print axioms certified_real_bound
#print axioms validLog_sound
#print axioms path_real_charge
end WaringLimit

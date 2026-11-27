import WaringEnvelope.FiniteDrift
import WaringEnvelope.IntegerMomentOrder

/-! # Applying the actual finite conductor stages to a moment recurrence -/
noncomputable section
namespace WaringEnvelope
open Set MeasureTheory

def normalizedHeight (z : ℕ) : ℝ := (z:ℝ)/T
def seedDefect (z : ℕ) : ℝ := normalizedHeight z/(1-normalizedHeight z)
def seedOrder (z : ℕ) : ℝ := 1-seedDefect z-Real.log (seedDefect z)

def StageUpdate (C : ℕ → ℝ → ℝ → ℝ → Prop) (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ r x z m, P r x → 0≤x → ConductorsAt C k z m →
    P (r+2) (max 0 (x-(2/k)*min (normalizedHeight z) (length m*x/2)))

theorem seed_range (z : ℕ) (hl : T≤20*z) (hu : 2*z≤T) :
    1/20≤normalizedHeight z ∧ normalizedHeight z≤1/2 ∧
    normalizedHeight z≤seedDefect z ∧ seedDefect z≤1 ∧ 0≤seedOrder z := by
  have hT : (0:ℝ)<T := by norm_num [T]
  have h₁ : (T:ℝ)≤20*z := by exact_mod_cast hl
  have h₂ : 2*(z:ℝ)≤T := by exact_mod_cast hu
  have hz : (1:ℝ)/20≤normalizedHeight z := (le_div_iff₀ hT).2 (by linarith)
  have hz' : normalizedHeight z≤1/2 := (div_le_iff₀ hT).2 (by linarith)
  have hden : 0<1-normalizedHeight z := by linarith
  have h₃ : normalizedHeight z≤seedDefect z := (le_div_iff₀ hden).2 (by nlinarith [sq_nonneg (normalizedHeight z)])
  have h₄ : seedDefect z≤1 := (div_le_iff₀ hden).2 (by linarith)
  have hlog := Real.log_nonpos (by linarith : 0≤seedDefect z) h₄
  exact ⟨hz,hz',h₃,h₄,by unfold seedOrder;linarith⟩

theorem seed_price_identity (z : ℕ) (hz : 0<z) (hu : 2*z≤T) :
    seedOrder z+seedDefect z/normalizedHeight z=2+Real.log (((T-z:ℕ):ℝ)/z) := by
  have hT : (0:ℝ)<T := by norm_num [T]
  have hzp : (0:ℝ)<z := by exact_mod_cast hz
  have h₂ : 2*(z:ℝ)≤T := by exact_mod_cast hu
  have hh : 0<normalizedHeight z := div_pos hzp hT
  have hd : 0<1-normalizedHeight z := by unfold normalizedHeight;apply sub_pos.mpr;exact (div_lt_one hT).2 (by linarith)
  have hr : ((T-z:ℕ):ℝ)/z=(seedDefect z)⁻¹ := by
    rw [Nat.cast_sub (by omega)]
    unfold seedDefect normalizedHeight
    field_simp
  rw [hr,Real.log_inv]
  unfold seedOrder seedDefect
  field_simp [hh.ne',hd.ne']
  ring

namespace IndexedStages
variable {C k z₀ z m R} (p : IndexedStages C k z₀ z m R)

theorem starting_knee (hlo : T≤20*z₀) (hhi : 2*z₀≤T) :
    2*p.heightAt 0/p.lengthAt 0≤seedDefect z₀ := by
  have ⟨hl,hu,_,_,_⟩ := seed_range z₀ hlo hhi
  have ht : p.heightAt 0=normalizedHeight z₀ := by unfold heightAt normalizedHeight;rw [p.first]
  rw [ht]
  apply potential_knee_le_start (by linarith) (by linarith)
  have hg : 2*((T-z₀:ℕ):ℝ)*V*B < (U:ℝ)*p.modulus 0*T := by exact_mod_cast p.gain
  rw [Nat.cast_sub (by omega)] at hg
  have hT : (0:ℝ)<T := by norm_num [T]
  have hden : (0:ℝ)<V*B := by norm_num [V,B]
  unfold normalizedHeight lengthAt length
  apply (le_div_iff₀ hden).2
  apply (mul_le_mul_right hT).mp
  calc
    _=2*((T:ℝ)-z₀)*V*B := by field_simp <;> ring
    _≤_ := hg.le

include p in
/-- An actual admissible moment below the finite menu price follows from
the seed moment and one analytic fibre update at each certified stage. -/
theorem finite_order (P : ℕ → ℝ → Prop) (hk : 21≤k)
    (hlo : T≤20*z₀) (hhi : 2*z₀≤T) (fee : ℝ) (hf : 0<fee) (hf₁ : fee≤1)
    (hstop : 2*((z:ℝ)/T)/length m<fee/((k:ℝ)*(Real.log k+81/10)))
    (hseed : P (evenOrder (k*seedOrder z₀)) (seedDefect z₀))
    (hstep : StageUpdate C P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a:ℕ):ℝ)/k < 2+Real.log (((T-z₀:ℕ):ℝ)/z₀)+R-2/length m+fee+6/k := by
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
  obtain ⟨r,a,x,er,ea,hP,hx,hxt,ha,hs⟩ := even_moment_order_of_integral P k (by omega) p.drift
    (seedDefect z₀) target (seedOrder z₀) fee ht.le hd hv hf.le
    p.continuous_drift.continuousOn (fun t h => p.positive_drift _ (ht.trans_le h.1))
    (p.monotone_drift.monotoneOn _) hseed (fun r x hp hx => by
      obtain ⟨i,hi,he⟩ := p.exists_active x
      rw [he]
      exact hstep r x _ _ hp hx (p.stage i hi))
  refine ⟨r,a,x,er,ea,hP,hx,ordinary_minor_gap k a (by omega) x fee hf hxt ha,?_⟩
  have h₀' : p.heightAt 0=normalizedHeight z₀ := by unfold heightAt normalizedHeight;rw [p.first]
  have hN : p.lengthAt p.N=length m := by unfold lengthAt; rw [p.lastModulus]
  rw [h₀',hN] at price
  have hz : 0<z₀ := p.first ▸ p.posHeight 0 (by omega)
  linarith [seed_price_identity z₀ hz hhi]

#print axioms finite_order
end IndexedStages
end WaringEnvelope

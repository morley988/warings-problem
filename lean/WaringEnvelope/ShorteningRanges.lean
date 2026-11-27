import WaringEnvelope.FiniteOrder
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Conductor lengths and moment orders in a shortening step -/
noncomputable section
namespace WaringEnvelope
open MeasureTheory Set

/-- Both the incoming and outgoing moments are even. The incoming order is
at least the degree. The shortening length lies strictly between one and k. -/
def ShorteningStep (C : ℕ → ℝ → ℝ → ℝ → Prop) (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ (r : ℕ) (x z M : ℝ), k≤r → Even r → P r x → 0≤x → 0<z → 1<M → M<k →
    (∃ σ, 2*z<σ ∧ ∀ u : ℝ, 1<u → u≤M → C k (M/k) u σ) →
    P (r+2) (max 0 (x-(2/k)*min z (((U:ℝ)/V)*M*x/2)))

def Guarded (P : ℕ → ℝ → Prop) (k r : ℕ) (x : ℝ) : Prop := k≤r ∧ Even r ∧ P r x

theorem guarded_seed {P : ℕ → ℝ → Prop} {k z : ℕ} (hlo : T≤20*z) (hhi : 3*z≤T)
    (seed : P (evenOrder (k*seedOrder z)) (seedDefect z)) :
    Guarded P k (evenOrder (k*seedOrder z)) (seedDefect z) := by
  have h₂ : 2*z≤T := by omega
  obtain ⟨h₀,h₁,h₂',_,_⟩ := seed_range z hlo h₂
  have hT : (0:ℝ)<T := by norm_num [T]
  have hhi' : (3:ℝ)*z≤T := by exact_mod_cast hhi
  have hz : normalizedHeight z≤1/3 := (div_le_iff₀ hT).2 (by linarith)
  have hd : seedDefect z≤1/2 :=
    (div_le_iff₀ (by linarith : 0<1-normalizedHeight z)).2 (by linarith)
  have hlog := Real.log_le_sub_one_of_pos (by linarith only [h₀,h₂'] : 0<seedDefect z)
  have hv : 1≤seedOrder z := by unfold seedOrder; linarith only [hd,hlog]
  have hk := Nat.cast_nonneg (α:=ℝ) k
  have h := (evenOrder_bounds ((k:ℝ)*seedOrder z) (mul_nonneg hk (by linarith))).1
  have hk' : (k:ℝ)≤evenOrder ((k:ℝ)*seedOrder z) :=
    calc
      (k:ℝ) ≤ k*seedOrder z := by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hv hk)
      _ ≤ _ := h
  exact ⟨by exact_mod_cast hk',⟨⌈((k:ℝ)*seedOrder z)/2⌉₊,by unfold evenOrder;omega⟩,seed⟩

/-- The implicit positive root in the smooth mean-value seed is bounded
by the scheduled defect at the rounded initial order. -/
theorem wooley_seed_defect (k z r : ℕ) (δ : ℝ) (hk : 0<k) (hlo : T≤20*z)
    (hhi : 2*z≤T) (hr : (k:ℝ)*seedOrder z≤r)
    (eqn : δ*Real.exp δ=Real.exp (1-(r:ℝ)/k)) : δ≤seedDefect z := by
  obtain ⟨hz,_,hD,_,_⟩ := seed_range z hlo hhi
  have hD0 : 0<seedDefect z := by linarith only [hz,hD]
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  have hratio : seedOrder z≤(r:ℝ)/k := (le_div_iff₀ hk').2 (by simpa [mul_comm] using hr)
  have he : Real.exp (1-(r:ℝ)/k)≤seedDefect z*Real.exp (seedDefect z) := by
    calc
      _ ≤ Real.exp (Real.log (seedDefect z)+seedDefect z) := by
        apply Real.exp_le_exp.mpr
        unfold seedOrder at hratio
        linarith only [hratio]
      _ = _ := by rw [Real.exp_add,Real.exp_log hD0]
  by_contra! H
  have hprod := mul_lt_mul_of_pos_right H (Real.exp_pos δ)
  have hmono := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr H.le) hD0.le
  linarith only [eqn,he,hprod,hmono]

namespace IndexedStages
variable {C k z₀ z m R} (p : IndexedStages C k z₀ z m R)

theorem modulus_between {i j : ℕ} (h : i≤j) (hj : j≤p.N) : p.modulus i≤p.modulus j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j h ih => exact (ih (by omega)).trans (p.increasing j (by omega))

include p in
theorem actual_modulus {i : ℕ} (hi : i≤p.N) (hhi : 2*z₀≤T) (hlast : m<B*k) :
    1<(p.modulus i:ℝ)/B ∧ (p.modulus i:ℝ)/B<k := by
  have hB : (0:ℝ)<B := by norm_num [B]
  have hfirst : B<p.modulus 0 := by
    by_contra! h
    have hl := Nat.mul_le_mul_right T (Nat.mul_le_mul (by decide : U≤V) h)
    have hu := Nat.mul_le_mul_right (V*B) (show T≤2*(T-z₀) by omega)
    have he : U*p.modulus 0*T≤2*(T-z₀)*V*B := hl.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hu)
    exact (not_lt_of_ge he) p.gain
  have he := p.modulus_between (Nat.zero_le i) hi
  have hu := p.modulus_between hi le_rfl
  rw [p.lastModulus] at hu
  constructor
  · apply (one_lt_div hB).2;exact_mod_cast hfirst.trans_le he
  · apply (div_lt_iff₀ hB).2
    simpa only [mul_comm] using (show (p.modulus i:ℝ)<B*k by exact_mod_cast hu.trans_lt hlast)

theorem guarded_row {P : ℕ → ℝ → Prop} {i r : ℕ} {x : ℝ} (hi : i≤p.N)
    (hhi : 2*z₀≤T) (hlast : m<B*k) (step : ShorteningStep C P k)
    (hr : Guarded P k r x) (hx : 0≤x) :
    Guarded P k (r+2) (max 0 (x-(2/k)*p.rowDrift i x)) := by
  obtain ⟨hr,er,hP⟩ := hr
  obtain ⟨hl,hh⟩ := p.actual_modulus hi hhi hlast
  obtain ⟨σ,hs,hu⟩ := p.stage i hi
  have hc : ∃ σ, 2*p.heightAt i<σ ∧ ∀ u : ℝ, 1<u → u≤(p.modulus i:ℝ)/B →
      C k (((p.modulus i:ℝ)/B)/k) u σ := by
    refine ⟨σ,hs,?_⟩
    convert hu using 2 <;> unfold actualTheta <;> ring
  refine ⟨by omega,er.add (by decide : Even 2),?_⟩
  have H := step r x _ _ hr er hP hx (p.positive_height i hi) hl hh hc
  convert H using 1 <;> unfold rowDrift lengthAt length <;> ring

end IndexedStages
#print axioms guarded_seed
#print axioms IndexedStages.guarded_row
end WaringEnvelope

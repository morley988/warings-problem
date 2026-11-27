import WaringDualEnvelope.CalibratedTerminal
import WaringEnvelope.ExtendedDrift

/-! # The real conductor actions in the clipped degree band -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope Set
set_option maxRecDepth 8192

def RealConductors (k : ℕ) (height M : ℝ) : Prop :=
  ∃ σ, 2*height<σ ∧ ∀ u : ℝ, 1<u → u≤M → DualStage k (M/k) u σ

def RealStageUpdate (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ r x height M, P r x → 0≤x → RealConductors k height M →
    P (r+2) (max 0 (x-(2/k)*min height (((U:ℝ)/V)*M*x/2)))

theorem real_of_indexed {k z m} (h : ConductorsAt DualStage k z m) :
    RealConductors k (normalizedHeight z) ((m:ℝ)/B) := by
  obtain ⟨σ,hs,hu⟩ := h
  refine ⟨σ,hs,?_⟩
  convert hu using 2 <;> unfold actualTheta <;> ring

theorem RealStageUpdate.natural {P k} (step : RealStageUpdate P k) : StageUpdate DualStage P k := by
  intro r x z m hP hx h
  have H := step r x _ _ hP hx (real_of_indexed h)
  convert H using 1 <;> unfold length <;> ring

theorem root_bound_for_clipped_theta (r k : ℕ) (hr : 0<r) (hk : r^2≤k)
    (M : ℝ) (hM : M≤Real.sqrt k/8) :
    M/k≤1/(8*(r:ℝ)) := by
  have hr' : (0:ℝ)<r := by exact_mod_cast hr
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k from (pow_pos hr _).trans_le hk)
  have hsq := Real.sq_sqrt hk'.le
  have hroot : (r:ℝ)≤Real.sqrt k := (Real.le_sqrt (Nat.cast_nonneg r) hk'.le).2
    (by exact_mod_cast hk)
  apply (div_le_div_iff₀ hk' (by positivity : 0<8*(r:ℝ))).2
  have hm := mul_le_mul_of_nonneg_right hM (by positivity : 0≤8*(r:ℝ))
  have hs := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (k:ℝ))
  nlinarith

theorem extended_real_conductors {c : WaringDualEnvelope.Config} {s : State} {bound k : ℕ}
    (h0 : c.last=0) (hK : 21≤c.first) (hr : 0<c.root) (hk : c.first≤k)
    (hp : WaringDualEnvelope.Path c start s) (hf : infiniteFinal c.toConfig s bound=true)
    (M : ℝ) (hM : M∈Icc (F:ℝ) (Real.sqrt k/8)) :
    RealConductors k (1/(14*M^2)) M := by
  have hcheck := hf
  simp only [infiniteFinal,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hcheck
  have hroot : c.first=c.root^2 := hcheck.2.1
  have hlimit : T≤s.height*14*F^2 := hcheck.2.2.2.2.1
  have hθ := root_bound_for_clipped_theta c.root k hr (hroot ▸ hk) M hM.2
  obtain ⟨s₀,hs₀,small⟩ := calibrated_last_row h0 hK hr hk hp hf (M/k) hθ
  have hF : (0:ℝ)<F := by norm_num [F]
  have hmpos := hF.trans_le hM.1
  have h₂ : 1/(14*M^2)≤normalizedHeight s.height := by
    have h₁ : (T:ℝ)≤(s.height:ℝ)*14*(F:ℝ)^2 := by exact_mod_cast hlimit
    have hT : (0:ℝ)<T := by norm_num [T]
    unfold normalizedHeight
    apply (div_le_div_iff₀ (by positivity : 0<14*M^2) hT).2
    rw [one_mul,←mul_assoc]
    exact h₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hF.le hM.1 2) (by positivity))
  let s₁ := ((1/7:ℝ)+1/1000)/M^2
  have hs₁ := (real_tail_weyl_action k M M hM.1 le_rfl hM.2).1
  refine ⟨min s₀ s₁,lt_min ((mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤2)).trans_lt hs₀) hs₁,?_⟩
  intro u h1 hu
  by_cases h : u≤(F:ℝ)
  · exact (small u h1 h).lower le_rfl (min_le_left _ _)
  · have hw := (real_tail_weyl_action k M u (le_of_not_ge h) hu hM.2).2
    exact (show DualStage k (M/k) u s₁ from Or.inl (Or.inr hw)).lower le_rfl (min_le_right _ _)

#print axioms extended_real_conductors
end WaringDualEnvelope

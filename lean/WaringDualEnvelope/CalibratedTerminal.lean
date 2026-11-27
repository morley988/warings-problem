import WaringDualEnvelope.SemanticMenu
import WaringEnvelope.FiniteOrder
import WaringEnvelope.InfinitePrice

/-! # The terminal conductor row at the full radical of the clipped continuum -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope
set_option maxRecDepth 8192

theorem DualStage.lower {k : ℕ} {θ θ' u σ σ' : ℝ} (p : DualStage k θ u σ)
    (ht : θ'≤θ) (hs : σ'≤σ) : DualStage k θ' u σ' := by
  rcases p with h|⟨w,hw,h⟩
  · exact Or.inl (h.mono le_rfl ht hs)
  · refine Or.inr ⟨w,hw,hs.trans (h.trans ?_)⟩
    apply sub_le_sub_left
    exact mul_le_mul_of_nonneg_left ht (by unfold radical;positivity)

theorem strong_test (c : WaringDualEnvelope.Config) (z m k code : ℕ) (θ : ℝ)
    (hz : 0<z) (hk : c.first≤k) (hK : 21≤c.first) (hr : 0<c.root)
    (hθ : θ≤stageTheta c.toConfig m)
    (test : conductorTest c m (ceilDiv (20001*z) 10000) code=true) :
    ∃ σ : ℝ, 2*normalizedHeight z<σ ∧
      ∀ u : ℝ, 1<u → u≤(m:ℝ)/B → DualStage k θ u σ := by
  refine ⟨_,strict_height_saving z hz,fun u h1 h2 => ?_⟩
  by_cases hfast : code<2^130
  · simp only [conductorTest,hfast,if_true] at test
    exact Or.inl ((chain_sound_of_positive c.toConfig m _ code u (by omega) hr test h1 h2).mono hk hθ le_rfl)
  · simp only [conductorTest,hfast,if_false] at test
    split at test
    · exact False.elim (Bool.false_ne_true test)
    · rename_i row he
      obtain ⟨hpair,hsafe⟩ := bank_sound row
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? he)) k (hK.trans hk)
      refine Or.inr ⟨row.1,hsafe,?_⟩
      rw [hpair]
      apply pairAdmits_sound c row.2 m _ test u θ h2
      by_cases hzero : c.last=0 <;> simpa [stageTheta,thetaData,hzero] using hθ

theorem Path.last_test {c : WaringDualEnvelope.Config} {s : State}
    (p : WaringDualEnvelope.Path c start s) (hp : 0<s.modulus) :
    0<s.height ∧ ∃ code, conductorTest c s.modulus (ceilDiv (20001*s.height) 10000) code=true := by
  cases p with
  | refl => simp [start] at hp
  | @extend t x u _ hrow =>
    have h := dualRow_properties c t _ x hrow
    exact ⟨h.1,h.2.2.2.2.1⟩

theorem calibrated_last_row {c : WaringDualEnvelope.Config} {s : State} {bound k : ℕ}
    (h0 : c.last=0) (hK : 21≤c.first) (hr : 0<c.root) (hk : c.first≤k)
    (hp : WaringDualEnvelope.Path c start s) (hf : infiniteFinal c.toConfig s bound=true)
    (θ : ℝ) (hθ : θ≤1/(8*(c.root:ℝ))) :
    ∃ σ : ℝ, 2*normalizedHeight s.height<σ ∧ ∀ u : ℝ, 1<u → u≤(F:ℝ) → DualStage k θ u σ := by
  have hcheck := hf
  simp only [infiniteFinal,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hcheck
  have hm : s.modulus=F*B := hcheck.2.2.2.1
  have hmp : 0<s.modulus := by rw [hm]; decide
  obtain ⟨hz,code,test⟩ := hp.last_test hmp
  obtain ⟨σ,hs,hcover⟩ := strong_test c s.height s.modulus k code θ hz hk hK hr
    (by simpa [stageTheta,thetaData,h0] using hθ) test
  refine ⟨σ,hs,fun u hu hu' => hcover u hu ?_⟩
  simpa [hm,Nat.cast_mul,B] using hu'

#print axioms calibrated_last_row
end WaringDualEnvelope

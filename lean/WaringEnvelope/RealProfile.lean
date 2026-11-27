import WaringEnvelope.RealCosts
import WaringEnvelope.ContinuousCover
import WaringEnvelope.AllDegrees

/-! # Real logarithmic profiles extracted from the integer certificates -/
noncomputable section
namespace WaringEnvelope
set_option maxRecDepth 8192

/-- A real profile consists of decreasing heights and retained conductors.
Its cost is the exact piecewise logarithmic integral at those conductors. -/
inductive RealProfile (c : Config) : ℕ → ℕ → ℝ → Prop
  | initial (m : ℕ) (hm : B≤m) (hk : m<B*c.first)
      (hθ : c.last≠0 ∨ m*8*c.root≤B*c.first)
      (hab : ∃ code, chain c m (ceilDiv (20001*top) 10000) 16 B code=true)
      (hgain : U*m*T>2*(T-top)*V*B) : RealProfile c top m 0
  | next {z m R} (prior : RealProfile c z m R) (zz mm : ℕ)
      (hz : 0<zz) (hzz : zz<z) (hmono : m≤mm) (hcap : mm<B*c.first)
      (hθ : c.last≠0 ∨ mm*8*c.root≤B*c.first)
      (hab : ∃ code, chain c mm (ceilDiv (20001*zz) 10000) 16 B code=true) :
      RealProfile c zz mm (R+2*Real.log ((z:ℝ)/zz)/((U:ℝ)*m/(V*B)))

theorem RealProfile.modulus_pos {c : Config} {z m R} (h : RealProfile c z m R) : 0<m := by
  induction h with
  | initial _ hm _ _ _ _ => exact (by decide : 0<B).trans_le hm
  | next _ _ _ _ _ hmono _ _ _ ih => exact ih.trans_le hmono

/-- At every checked positive endpoint there is a profile with exact real
logarithmic cost bounded by the integer running charge, divided by D. -/
theorem Path.realProfile {c : Config} {s : State} (h : Path c start s) :
    s=start ∨ ∃ R : ℝ, RealProfile c s.height s.modulus R ∧ R≤(s.cost:ℝ)/D := by
  induction h with
  | refl => exact Or.inl rfl
  | @extend t x u hpath hr ih =>
    obtain ⟨hz,hm,hk,hθ,hchain,hcases⟩ := row_properties c t u x hr
    right
    rcases hcases with ⟨ht0,hu,gain,cost⟩ | ⟨htpos,hh,hmono,cost⟩
    · rw [hu] at hchain ⊢
      exact ⟨0,.initial _ hm hk hθ hchain gain,by rw [cost]; simp⟩
    · rcases ih with hs|⟨R,hR,hRc⟩
      · simp [hs,start] at htpos
      · refine ⟨_,.next hR _ _ hz hh hmono hk hθ hchain,?_⟩
        rw [cost,Nat.cast_add,add_div]
        exact add_le_add hRc (intervalCost_sound _ _ _ hz hh.le htpos)

theorem Certified.realProfile {c : Config} {bound : ℕ} (h : Certified c bound) :
    ∃ s R, RealProfile c s.height s.modulus R ∧ R≤(s.cost:ℝ)/D ∧
      (if c.last=0 then infiniteFinal c s bound else finiteFinal c s bound)=true := by
  obtain ⟨_,s,hp,hf⟩ := h
  rcases hp.realProfile with hs|⟨R,hR,hRc⟩
  · subst s
    by_cases h0 : c.last=0
    · simp [h0,infiniteFinal,start,F,B] at hf
    · simp [h0,finiteFinal,start] at hf
  · exact ⟨s,R,hR,hRc,hf⟩

/-- In particular, every integer degree k≥21 has an actual real-logarithmic
profile and the certified terminal test for the 6.919 envelope. -/
theorem all_large_degrees_real_6919 (k : ℕ) (hk : 21≤k) :
    ∃ c s R, c.first≤k ∧ (c.last=0 ∨ k≤c.last) ∧
      RealProfile c s.height s.modulus R ∧ R≤(s.cost:ℝ)/D ∧
      (if c.last=0 then infiniteFinal c s (6919*D/1000) else
        finiteFinal c s (6919*D/1000))=true := by
  obtain ⟨c,hk0,hk1,hc⟩ := all_large_degrees_6919 k hk
  obtain ⟨s,R,hform,hcharge,hfinal⟩ := hc.realProfile
  exact ⟨c,s,R,hk0,hk1,hform,hcharge,hfinal⟩

#print axioms all_large_degrees_real_6919
end WaringEnvelope

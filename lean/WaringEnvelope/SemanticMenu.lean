import WaringEnvelope.CellSound
import WaringEnvelope.RealProfile

/-! # A decreasing sequence of heights with continuous conductor coverage -/
noncomputable section
namespace WaringEnvelope

theorem DifferencingBranch.mono {θ θ' u σ σ' : ℝ} {j : ℕ}
    (hb : DifferencingBranch θ j u σ) (ht : θ'≤θ) (hs : σ'≤σ) :
    DifferencingBranch θ' j u σ' := by
  induction hb generalizing σ' with
  | completion u σ hl hh => exact .completion _ _ (by linarith) (by linarith)
  | shift a ha hau hd hb ih =>
    exact .shift a (ht.trans ha) hau (by linarith) (ih (by linarith))

theorem StageConclusion.mono {k k' : ℕ} {θ θ' u σ σ' : ℝ}
    (h : StageConclusion k θ u σ) (hk : k≤k') (ht : θ'≤θ) (hs : σ'≤σ) :
    StageConclusion k' θ' u σ' := by
  rcases h with ⟨j,hj,hb⟩|hw
  · exact Or.inl ⟨j,hj.trans hk,hb.mono ht hs⟩
  · exact Or.inr (hw.mono hk ht hs)

def actualTheta (m k : ℕ) : ℝ := (m:ℝ)/(B*k)

theorem actualTheta_le_stage (c : Config) (m k : ℕ) (hc : 0<c.first) (hr : 0<c.root)
    (hk : c.first≤k) (hcap : c.last≠0 ∨ m*8*c.root≤B*c.first) :
    actualTheta m k ≤ stageTheta c m := by
  have hB : (0:ℝ)<B := by norm_num [B]
  have hK : (0:ℝ)<c.first := by exact_mod_cast hc
  have hk' : (c.first:ℝ)≤k := by exact_mod_cast hk
  have hr' : (0:ℝ)<c.root := by exact_mod_cast hr
  unfold actualTheta stageTheta thetaData
  by_cases h0 : c.last=0
  · simp only [h0,if_true,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
    rcases hcap with hbad|hbound
    · exact False.elim (hbad h0)
    · have hh : (m:ℝ)*8*c.root≤B*c.first := by exact_mod_cast hbound
      rw [div_le_div_iff₀ (mul_pos hB (hK.trans_le hk')) (by positivity)]
      have hinc := mul_le_mul_of_nonneg_left hk' hB.le
      linarith
  · simp only [h0,if_false,Nat.cast_mul]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hB hK)
      (mul_le_mul_of_nonneg_left hk' hB.le)

theorem strict_height_saving (z : ℕ) (hz : 0<z) :
    2*((z:ℝ)/T) < (ceilDiv (20001*z) 10000 : ℝ)/T := by
  have ht : (0:ℝ)<T := by norm_num [T]
  have h := real_le_ceilDiv (20001*z) 10000 (by decide)
  push_cast at h
  have h' : 2*(z:ℝ) < ceilDiv (20001*z) 10000 := by
    have hz' : (0:ℝ)<z := by exact_mod_cast hz
    linarith
  simpa only [mul_div_assoc] using (div_lt_div_iff_of_pos_right ht).2 h'

/-- C is a mathematically interpreted predicate for one real conductor,
for example a valid differencing tree or Weyl degree. -/
def ConductorsAt (C : ℕ → ℝ → ℝ → ℝ → Prop) (k z m : ℕ) : Prop :=
  ∃ σ : ℝ, 2*((z:ℝ)/T)<σ ∧ ∀ u : ℝ, 1<u → u≤(m:ℝ)/B → C k (actualTheta m k) u σ

/-- The exact real charge of a menu of strictly admissible heights. -/
inductive MathematicalMenu (C : ℕ → ℝ → ℝ → ℝ → Prop) (k z₀ : ℕ) : ℕ → ℕ → ℝ → Prop
  | initial (m : ℕ) (hm : B≤m) (hs : ConductorsAt C k z₀ m)
      (hgain : U*m*T>2*(T-z₀)*V*B) : MathematicalMenu C k z₀ z₀ m 0
  | next {z m R} (prior : MathematicalMenu C k z₀ z m R) (zz mm : ℕ)
      (hz : 0<zz) (hzz : zz<z) (hm : m≤mm) (hs : ConductorsAt C k zz mm) :
      MathematicalMenu C k z₀ zz mm (R+2*Real.log ((z:ℝ)/zz)/((U:ℝ)*m/(V*B)))

theorem conductorsAt_of_chain (c : Config) (z m k : ℕ) (hz : 0<z) (hk : c.first≤k)
    (hc : configOK c=true) (hθ : c.last≠0 ∨ m*8*c.root≤B*c.first)
    (hchain : ∃ code, chain c m (ceilDiv (20001*z) 10000) 16 B code=true) :
    ConductorsAt StageConclusion k z m := by
  obtain ⟨code,hcode⟩ := hchain
  obtain ⟨hK,hroot⟩ := config_indices_pos c hc
  refine ⟨_,strict_height_saving z hz,fun u h1 h2 => ?_⟩
  exact (chain_sound c m _ code u hc hcode h1 h2).mono hk
    (actualTheta_le_stage c m k hK hroot hk hθ) le_rfl

theorem RealProfile.mathematicalMenu {c : Config} {z m k : ℕ} {R : ℝ}
    (h : RealProfile c z m R) (hk : c.first≤k) (hc : configOK c=true) :
    MathematicalMenu StageConclusion k top z m R := by
  induction h with
  | initial m hm _ hθ hab hgain =>
    exact .initial _ hm (conductorsAt_of_chain c top m k (by decide) hk hc hθ hab) hgain
  | next _ zz mm hz hzz hm _ hθ hab ih =>
    exact .next ih _ _ hz hzz hm (conductorsAt_of_chain c zz mm k hz hk hc hθ hab)

theorem all_large_degrees_continuous_6919 (k : ℕ) (hk : 21≤k) :
    ∃ (c : Config) (s : State) (R : ℝ), c.first≤k ∧ (c.last=0 ∨ k≤c.last) ∧
      MathematicalMenu StageConclusion k top s.height s.modulus R ∧ R≤(s.cost:ℝ)/D ∧
      (if c.last=0 then infiniteFinal c s (6919*D/1000) else
        finiteFinal c s (6919*D/1000))=true := by
  obtain ⟨c,hl,hr,hc⟩ := all_large_degrees_6919 k hk
  obtain ⟨s,R,hreal,hR,hfinal⟩ := hc.realProfile
  exact ⟨c,s,R,hl,hr,hreal.mathematicalMenu hl hc.1,hR,hfinal⟩

#print axioms all_large_degrees_continuous_6919
end WaringEnvelope

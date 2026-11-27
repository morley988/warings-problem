import WaringDualEnvelope.ConductorPairs
import WaringEnvelope.SemanticMenu

/-! # Mathematical meaning of every A/B or degree-reduction stage in the dual menus -/
noncomputable section
namespace WaringDualEnvelope
open WaringEnvelope
set_option maxRecDepth 8192

def DualStage (k : ℕ) (θ u σ : ℝ) : Prop :=
  StageConclusion k θ u σ ∨ ∃ word : List Bool,
    SafeAt k (0,1) (1,0) word.reverse ∧
      σ ≤ 1-lambda (pairOfWord word)+kappa (pairOfWord word)-
        kappa (pairOfWord word)*u-(1+radical (pairOfWord word))*θ

private theorem config_indices (c : WaringDualEnvelope.Config) (hc : WaringDualEnvelope.configOK c=true) :
    21≤c.first ∧ 0<c.root ∧ 0<c.heightTop := by
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at hc
  refine ⟨by omega,?_,by omega⟩
  by_contra! h
  have hr : c.root=0 := by omega
  simp [hr] at hc
  omega

theorem conductorsAt_of_test (c : WaringDualEnvelope.Config) (z m k code : ℕ)
    (hz : 0<z) (hk : c.first≤k) (hc : WaringDualEnvelope.configOK c=true)
    (hθ : c.last≠0 ∨ m*8*c.root≤B*c.first)
    (hcode : conductorTest c m (ceilDiv (20001*z) 10000) code=true) :
    ConductorsAt DualStage k z m := by
  obtain ⟨hK,hr,_⟩ := config_indices c hc
  have hKp : 0<c.first := by omega
  have ht := actualTheta_le_stage c.toConfig m k hKp hr hk hθ
  refine ⟨_,strict_height_saving z hz,fun u h1 h2 => ?_⟩
  by_cases hfast : code < 2^130
  · simp only [conductorTest,hfast,if_true] at hcode
    exact Or.inl ((chain_sound_of_positive c.toConfig m _ code u hKp hr hcode h1 h2).mono hk ht le_rfl)
  · simp only [conductorTest,hfast,if_false] at hcode
    split at hcode
    · exact False.elim (Bool.false_ne_true hcode)
    · rename_i row he
      obtain ⟨hpair,hsafe⟩ := bank_sound row
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? he)) k (hK.trans hk)
      refine Or.inr ⟨row.1,hsafe,?_⟩
      rw [hpair]
      apply pairAdmits_sound c row.2 m _ hcode u (actualTheta m k) h2
      by_cases hzero : c.last=0 <;> simpa [stageTheta,thetaData,hzero] using ht


theorem dualRow_properties (c : WaringDualEnvelope.Config) (s u : State) (x : Nat)
    (h : WaringDualEnvelope.row c s x = some u) :
    0<u.height ∧ B≤u.modulus ∧ u.modulus < B*c.first ∧
    (c.last≠0 ∨ u.modulus*8*c.root≤B*c.first) ∧
    (∃ code, conductorTest c u.modulus (ceilDiv (20001*u.height) 10000) code=true) ∧
    ((s.modulus=0 ∧ u.height=c.heightTop ∧ U*u.modulus*T>2*(T-c.heightTop)*V*B ∧ u.cost=0) ∨
     (0<s.modulus ∧ u.height<s.height ∧ s.modulus≤u.modulus ∧
       u.cost=s.cost+intervalCost s.height u.height s.modulus)) := by
  unfold WaringDualEnvelope.row at h
  simp only [Bool.not_eq_true',Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    bne_iff_ne,Option.pure_def,bind,Option.bind] at h
  split at h <;> try contradiction
  rename_i hguard
  simp only [Bool.and_eq_false_imp,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    bne_iff_ne] at hguard
  split at h
  · rename_i hs
    split at h <;> try contradiction
    rename_i hi
    simp only [Option.some.injEq] at h
    subst u
    simp only [State.mk.injEq,gt_iff_lt] at *
    grind
  · rename_i hs
    split at h <;> try contradiction
    rename_i hi
    simp only [Option.some.injEq] at h
    subst u
    simp only [gt_iff_lt] at *
    grind

theorem Path.mathematicalMenu {c : WaringDualEnvelope.Config} {s : State} {k : ℕ}
    (h : WaringDualEnvelope.Path c start s) (hk : c.first≤k) (hc : WaringDualEnvelope.configOK c=true) :
    s=start ∨ ∃ R : ℝ, MathematicalMenu DualStage k c.heightTop s.height s.modulus R ∧
      R≤(s.cost:ℝ)/D := by
  induction h with
  | refl => exact Or.inl rfl
  | @extend t x u hp hrow ih =>
    obtain ⟨hz,hm,hcap,hθ,⟨code,hcode⟩,hcases⟩ := dualRow_properties c t u x hrow
    have hab := conductorsAt_of_test c _ _ k code hz hk hc hθ hcode
    right
    rcases hcases with ⟨ht0,hu,gain,cost⟩ | ⟨htpos,hh,hmono,cost⟩
    · rw [hu] at hab ⊢
      exact ⟨0,.initial _ hm hab gain,by rw [cost]; simp⟩
    · rcases ih with hs|⟨R,hR,hRc⟩
      · simp [hs,start] at htpos
      · refine ⟨_,.next hR _ _ hz hh hmono hab,?_⟩
        rw [cost,Nat.cast_add,add_div]
        exact add_le_add hRc (intervalCost_sound _ _ _ hz hh.le htpos)

theorem Certified.mathematicalMenu {c : WaringDualEnvelope.Config} {bound k : ℕ}
    (h : WaringDualEnvelope.Certified c bound) (hk : c.first≤k) :
    ∃ s R, MathematicalMenu DualStage k c.heightTop s.height s.modulus R ∧ R≤(s.cost:ℝ)/D ∧
      (if c.last=0 then infiniteFinal c.toConfig s bound else finiteFinal c.toConfig s bound)=true := by
  obtain ⟨hc,s,hp,hf⟩ := h
  rcases hp.mathematicalMenu hk hc with hs|⟨R,hR,hRc⟩
  · subst s
    by_cases h0 : c.last=0
    · simp [h0,infiniteFinal,start,F,B] at hf
    · simp [h0,finiteFinal,start] at hf
  · exact ⟨s,R,hR,hRc,hf⟩

#print axioms conductorsAt_of_test
#print axioms Certified.mathematicalMenu
end WaringDualEnvelope

import WaringFieldSmall.RowProof

/-! # Finite arithmetic witness for the middle conductor range
A witness consists only of natural numbers, an envelope configuration and
the Boolean results of the existing arithmetic exponent-pair/cell checker.
Its soundness covers every real conductor in the interval. -/
noncomputable section
open WaringEnvelope WaringDualEnvelope WaringLinear
namespace WaringFieldSmall

def MiddleRowTests (Listed : Schedule → Prop) (k : ℕ) : Prop :=
  ∀ band, Listed band → band.lo≤k → k≤band.hi → ∀ u∈band.data,
    let s := unpack u
    0<s.gain ∧ modulusScale<s.modulus ∧ s.modulus<modulusScale*k ∧
    ∃ (cfg : WaringDualEnvelope.Config) (code : ℕ),
      cfg.first≤k ∧ cfg.last≠0 ∧ WaringDualEnvelope.configOK cfg=true ∧
      conductorTest cfg s.modulus (ceilDiv (20001*liftHeight s.gain) 10000) code=true

theorem rowCoverage_of_middleRowTests (Listed : Schedule → Prop) (k : ℕ) (hk : k≤2500)
    (tests : MiddleRowTests Listed k) : RowCoverage Listed k := by
  intro band listed hl hh u hu
  obtain ⟨hg,hm,hcap,cfg,code,hfirst,hlast,hcfg,hcode⟩ := tests band listed hl hh u hu
  let s := unpack u
  obtain ⟨σ,hs,hσ⟩ := conductorsAt_of_test cfg (liftHeight s.gain) s.modulus k code
    (Nat.mul_pos hg (by decide)) hfirst hcfg (Or.inl hlast) hcode
  have hB : (0:ℝ)<modulusScale := by norm_num [modulusScale]
  have hg' : (0:ℝ)<s.gain := by exact_mod_cast hg
  have hm' : (modulusScale:ℝ)<s.modulus := by exact_mod_cast hm
  have hcap' : (s.modulus:ℝ)<modulusScale*k := by exact_mod_cast hcap
  have hzh : (s.gain:ℝ)/(2*scale)=(liftHeight s.gain:ℝ)/T := by norm_num [scale,liftHeight,T];ring
  dsimp only
  refine ⟨div_pos hg' (by norm_num [scale]),(one_lt_div hB).2 hm',(div_lt_iff₀ hB).2 ?_,σ,?_,?_⟩
  · linarith only [hcap']
  · change 2*((s.gain:ℝ)/(2*scale))<σ
    rwa [hzh]
  · intro v hv hvm
    have hstage := hσ v hv hvm
    simp only [fieldConductorStage,if_pos (by omega : k<180000^2)]
    convert hstage using 2 <;> unfold actualTheta <;> change _=_ <;> try rfl
    change ((s.modulus:ℝ)/modulusScale)/k=s.modulus/(modulusScale*k)
    ring

#print axioms rowCoverage_of_middleRowTests
end WaringFieldSmall

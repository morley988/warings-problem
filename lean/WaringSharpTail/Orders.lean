import WaringSharpTail.Meaning
import WaringSharpTail.Final
import WaringSharpTail.Pairs
import WaringEnvelope.TailCellSound
import WaringEnvelope.TailMonotonicity
import WaringLimit.Tail
import WaringEnvelope.IndexedStages
import WaringEnvelope.ExtendedDrift
import WaringEnvelope.FiniteOrder
import WaringEnvelope.ShorteningRanges





/-! The finite-degree menu gives an arithmetic exponent pair, with its
actual radical loss, or a valid degree-reduction Weyl inequality at every
real conductor between one and the computed endpoint. -/
noncomputable section
namespace WaringSharpTail
open WaringLimit (words Entry decode)
open WaringDualEnvelope (SafeAt)

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def Covered (k σ : Nat) (θ u : ℝ) : Prop :=
  (∃ w : List Bool, SafeAt k (0,1) (1,0) w.reverse ∧
    let p := sharpPair w
    (σ:ℝ)/T ≤ 1-(p.y:ℝ)/p.denominator-(p.x:ℝ)/p.denominator*(u-1)-
      (1+(p.loss:ℝ)/p.lossDen)*θ) ∨
  WaringEnvelope.WeylBranch k θ u ((σ:ℝ)/T)

private theorem cell {k σ j lo hi : Nat} {u θ : ℝ} (hc : cellOK j σ lo hi = true)
    (hk : 2*F+1≤k) (hθ : θ≤1/radicalDen) (hl : (lo:ℝ)/B≤u)
    (hu : u≤(hi:ℝ)/B) : Covered k σ θ u := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  obtain ⟨hj,hjK,h1,h2,h3⟩ := hc
  let v := WaringEnvelope.weylWeight j
  change B*(j+1)*(v*σ*radicalDen+j*T)≤lo*T*radicalDen at h1
  change hi*T*radicalDen+B*(j+1)*(v*σ*radicalDen+T)≤B*(j+1)*T*radicalDen at h2
  change hi*T*radicalDen+B*(v*σ*radicalDen+j*T)≤B*j*T*radicalDen at h3
  have h₁ : (B:ℝ)*(j+1)*(v*σ*radicalDen+j*T)≤lo*T*radicalDen := by exact_mod_cast h1
  have h₂ : (hi:ℝ)*T*radicalDen+B*(j+1)*(v*σ*radicalDen+T)≤B*(j+1)*T*radicalDen := by exact_mod_cast h2
  have h₃ : (hi:ℝ)*T*radicalDen+B*(v*σ*radicalDen+j*T)≤B*j*T*radicalDen := by exact_mod_cast h3
  right
  apply WaringEnvelope.WeylBranch.mono (θ:=1/radicalDen) (k:=2*F+1) _ hk hθ le_rfl
  apply WaringEnvelope.interval_has_weyl_branch j _ _ _ _ hj hjK
  · change (j+1:ℝ)*(v*((σ:ℝ)/T)+j*(1/radicalDen))≤u
    norm_num [B,T,radicalDen,root] at h₁ hl ⊢
    linarith only [h₁,hl]
  · change u≤min ((j+1:ℝ)*(1-1/(radicalDen:ℝ)-v*((σ:ℝ)/T)))
        ((j:ℝ)-j*(1/radicalDen)-v*((σ:ℝ)/T))
    apply le_min
    · norm_num [B,T,radicalDen,root] at h₂ hu ⊢
      linarith only [h₂,hu]
    · norm_num [B,T,radicalDen,root] at h₃ hu ⊢
      linarith only [h₃,hu]

private theorem initial {k σ hi : Nat} {θ u : ℝ} (e : Entry) (em : e ∈ words)
    (hk : 21≤k) (hlo : 0≤θ) (ht : θ≤1/radicalDen) (hc : pairOK e σ hi = true)
    (hu : u≤(hi:ℝ)/B) : Covered k σ θ u := by
  have hmem := Array.all_eq_true_iff_forall_mem.mp sharp_words_checked e em
  simp only [sharpEntryOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] at hmem
  obtain ⟨hx,hd,hp,hq,hxv,hyv,hr,hsafe⟩ := hmem
  let p := sharpPair (decode 14 e.bits)
  have eqx : (p.x:ℝ)/p.denominator=(e.x:ℝ)/e.den := by
    apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hp)) (by exact_mod_cast (Nat.ne_of_gt hd))).2
    exact_mod_cast hxv
  have eqy : (p.y:ℝ)/p.denominator=(e.y:ℝ)/e.den := by
    apply (div_eq_div_iff (by exact_mod_cast (Nat.ne_of_gt hp)) (by exact_mod_cast (Nat.ne_of_gt hd))).2
    exact_mod_cast hyv
  have hr' : (p.loss:ℝ)/p.lossDen≤1 :=
    (div_le_iff₀ (by exact_mod_cast hq)).2 (by simpa using (show (p.loss:ℝ)≤p.lossDen by exact_mod_cast hr))
  have hrad : (1+(p.loss:ℝ)/p.lossDen)*θ ≤ 2*(1/radicalDen:ℝ) := by
    calc
      _ ≤ 2*θ := mul_le_mul_of_nonneg_right (by linarith only [hr']) hlo
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (by norm_num)
  have hcore : (hi:ℝ)*e.x*T*radicalDen+B*(e.y*T*radicalDen+e.den*σ*radicalDen+2*e.den*T)
      ≤ B*(e.den+e.x)*T*radicalDen := by
    simp only [pairOK,decide_eq_true_eq] at hc
    exact_mod_cast hc
  have hB : (0:ℝ)<B := by norm_num [B]
  have hu' := mul_le_mul_of_nonneg_right ((le_div_iff₀ hB).mp hu) (Nat.cast_nonneg e.x)
  have hd' : (0:ℝ)<e.den := by exact_mod_cast hd
  left
  refine ⟨decode 14 e.bits,WaringDualEnvelope.avoidsPoles_sound _ _ _ hsafe k hk,?_⟩
  change (σ:ℝ)/T ≤ 1-(p.y:ℝ)/p.denominator-(p.x:ℝ)/p.denominator*(u-1)-(1+(p.loss:ℝ)/p.lossDen)*θ
  rw [eqx,eqy]
  have hmain : (σ:ℝ)/T ≤ 1-(e.y:ℝ)/e.den-(e.x:ℝ)/e.den*(u-1)-2*(1/radicalDen:ℝ) := by
    rw [show (e.x:ℝ)/e.den*(u-1)=((e.x:ℝ)*(u-1))/e.den by ring]
    norm_num [B,T,radicalDen,root] at hu' hcore ⊢
    field_simp
    linarith only [hcore,hu']
  linarith only [hmain,hrad]

private theorem chain {k σ h code n : Nat} {θ : ℝ} (fuel : Nat)
    (hk : 2*F+1≤k) (ht : θ≤1/radicalDen) (ok : weylChain fuel σ h code = some n)
    (base : ∀ u : ℝ, 1≤u → u≤(h:ℝ)/B → Covered k σ θ u) :
    ∀ u : ℝ, 1≤u → u≤(n:ℝ)/B → Covered k σ θ u := by
  induction fuel generalizing h code n with
  | zero =>
    simp only [weylChain] at ok
    split at ok
    · injection ok with hn
      subst n
      exact base
    · contradiction
  | succ f ih =>
    simp only [weylChain,bind,Option.bind,pure] at ok
    split at ok
    · injection ok with hn
      subst n
      exact base
    · split at ok
      · rename_i hv
        simp only [Bool.and_eq_true] at hv
        apply ih ok
        intro u hu hup
        by_cases hh : u≤(h:ℝ)/B
        · exact base u hu hh
        · exact cell hv.1 hk ht (le_of_not_ge hh) hup
      · contradiction

/-- The strict saving above twice the height holds at every real
conductor, uniformly throughout the degree band and all smaller losses. -/
theorem endpoint_covers {z code m k : Nat} {θ : ℝ} (hk : root^2≤k)
    (hθ₀ : 0≤θ) (hθ : θ≤1/radicalDen) (ok : endpoint z code = some m) :
    ∃ σ : Nat, 2*z<σ ∧ ∀ u : ℝ, 1≤u → u≤(m:ℝ)/B → Covered k σ θ u := by
  cases he : words[code%256]? with
  | none => simp [endpoint,he] at ok
  | some e =>
    simp only [endpoint,he,bind,Option.bind,pure] at ok
    split at ok
    · contradiction
    · rename_i hv
      simp only [Bool.not_eq_true',Bool.not_eq_false,Bool.and_eq_true,decide_eq_true_eq] at hv
      let σ := WaringEnvelope.ceilDiv (200001*z) 100000
      let h := B+B*((e.den-e.y)*T*radicalDen-e.den*(σ*radicalDen+2*T))/(e.x*T*radicalDen)
      have emem : e ∈ words := Array.mem_of_getElem? he
      refine ⟨σ,hv.1.2,?_⟩
      cases hc : weylChain 3 σ h (code/256) with
      | none =>
        dsimp only [h,σ] at hc
        simp only [hc] at ok
        contradiction
      | some n =>
        have hc' := hc
        dsimp only [h,σ] at hc'
        simp only [hc'] at ok
        injection ok with hm
        subst m
        intro u hu hup
        have hun : u≤(n:ℝ)/B := hup.trans (div_le_div_of_nonneg_right
          (by exact_mod_cast Nat.min_le_right (F*B) n) (Nat.cast_nonneg _))
        apply chain 3 ((by decide : 2*F+1≤root^2).trans hk) hθ hc _ u hu hun
        intro v _ huv
        exact initial e emem ((by decide : 21≤root^2).trans hk) hθ₀ hθ hv.2 huv

#print axioms endpoint_covers
end WaringSharpTail





/-! The logarithmic terminal correction is bounded at its worst degree.
The seven final variables and the square-root cap are counted here. -/
noncomputable section
namespace WaringSharpTail
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

def logK : Nat := 242014242597446949
def capLog : Nat := 49949470777798184

theorem cap_cert : validLog (root^2) 1 logK = true ∧
    validLog (64*retentionDen*(10*logK+81*D)) (14*retentionNum*10*D) capLog = true := by
  decide +kernel

noncomputable def capCorrection (k : Nat) : ℝ :=
  (16*retentionDen:ℝ)/retentionNum*
      (Real.log ((64*retentionDen/(14*retentionNum):ℝ)*(Real.log k+81/10))/Real.sqrt k)
     +16/Real.sqrt k+7/k

/-- Outward upper bound at every actual degree, including the integer terminal rounding. -/
theorem clipping_price {k : Nat} (hk : root^2≤k) :
    capCorrection k ≤ (5328888407384:ℝ)/10000000000000000 := by
  let A : ℝ := 64*retentionDen/(14*retentionNum)
  let K : Nat := root^2
  have hK : 0<(K:ℝ) := by norm_num [K,root]
  have hr : 0<(root:ℝ) := by norm_num [root]
  have hKr : 1≤(K:ℝ) := by norm_num [K,root]
  have hkk : (K:ℝ)≤k := by exact_mod_cast hk
  have hsqrt : Real.sqrt (K:ℝ) = root := by
    dsimp [K]
    rw [Nat.cast_pow,Real.sqrt_sq (by positivity)]
  have hrootmono := Real.sqrt_le_sqrt hkk
  rw [hsqrt] at hrootmono
  have hA : 1≤A := by norm_num [A,retentionNum,retentionDen]
  have hAp := zero_lt_one.trans_le hA
  have hLg : Real.log (K:ℝ) ≤ (logK:ℝ)/D := by
    simpa [K] using validLog_sound _ _ _ cap_cert.1
  have hArg : 0 < Real.log (K:ℝ)+81/10 := by linarith [Real.log_nonneg hKr]
  have hexp : Real.exp 1 ≤ A*(Real.log K+81/10) := by
    have hj := le_mul_of_one_le_left hArg.le hA
    have half : Real.exp (1/2:ℝ) ≤ 2 := by
      convert Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1) using 1
      norm_num
    have he : Real.exp 1 ≤ 4 := calc
      _ = Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ) := by rw [← Real.exp_add]; norm_num
      _ ≤ 2*2 := mul_le_mul half half (Real.exp_pos _).le (by norm_num)
      _ = _ := by norm_num
    linarith [Real.log_nonneg hKr]
  have hmono := WaringEnvelope.log_log_div_sqrt_antitone hKr hkk hAp (by norm_num : (2:ℝ)≤81/10) hexp
  have hlcap := validLog_sound _ _ _ cap_cert.2
  have hquot : (((64*retentionDen*(10*logK+81*D):Nat):ℝ)/(14*retentionNum*10*D:Nat)) =
      A*((logK:ℝ)/D+81/10) := by norm_num [A,retentionDen,retentionNum,logK,D]
  rw [hquot] at hlcap
  have hlK : Real.log (A*(Real.log K+81/10)) ≤ (capLog:ℝ)/D :=
    (Real.log_le_log (mul_pos hAp hArg) (mul_le_mul_of_nonneg_left
      (add_le_add_right hLg _) hAp.le)).trans hlcap
  rw [hsqrt] at hmono
  have hratio := hmono.trans (div_le_div_of_nonneg_right hlK hr.le)
  have har := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ (16*retentionDen:ℝ)/retentionNum)
  have hb := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤16) hr hrootmono
  have hc := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤7) hK hkk
  change (16*retentionDen:ℝ)/retentionNum*(Real.log (A*(Real.log k+81/10))/Real.sqrt k)
      +16/Real.sqrt k+7/k≤_
  apply (add_le_add (add_le_add har hb) hc).trans
  norm_num [K,root,capLog,D,retentionNum,retentionDen]

#print axioms clipping_price
end WaringSharpTail






/-! A uniform conductor-cover theorem joins the certified finite path
to its continuous tail at modulus F. The integrations below use
Lebesgue measure and the real logarithm. -/
noncomputable section
namespace WaringSharpTail
open WaringDualEnvelope
open MeasureTheory Set Real
set_option maxRecDepth 8192

private theorem Tpos : 0<T := by decide
private theorem Bpos : 0<B := by decide
private theorem Fval : F=300 := rfl
attribute [local irreducible] F B T

def Branch (k : Nat) (θ u s : ℝ) : Prop :=
  (∃ w : List Bool, SafeAt k (0,1) (1,0) w.reverse ∧
    s≤1-lambda (sharpPair w)-kappa (sharpPair w)*(u-1)
       -(1+radical (sharpPair w))*θ) ∨
  WaringEnvelope.WeylBranch k θ u s

private theorem real_endpoint {z code m k : Nat} {θ u : ℝ} (he : endpoint z code=some m)
    (hk : root^2≤k) (h₀ : 0≤θ) (hθ : θ≤1/radicalDen)
    (hu : 1≤u) (hm : u≤(m:ℝ)/B) :
    ∃ s : ℝ, 2*(z:ℝ)/T<s ∧ Branch k θ u s := by
  obtain ⟨σ,hs,h⟩ := endpoint_covers hk h₀ hθ he
  refine ⟨(σ:ℝ)/T,(div_lt_div_iff_of_pos_right (show (0:ℝ)<T by exact_mod_cast Tpos)).2
    (by exact_mod_cast hs),h u hu hm⟩

private theorem step_endpoint {s t : State} {c : Nat} (h : step s c=some t) :
    endpoint s.z c=some t.m := by
  cases he : endpoint s.z c with
  | none => simp [step,he] at h
  | some m =>
    simp only [step,he,bind,Option.bind,pure] at h
    split at h
    · contradiction
    · injection h with ht
      subst t
      rfl

/-- Each edge of this path carries a saving at all real conductors,
and its real price is the actual logarithmic price for that edge. -/
inductive EffectivePath (k : Nat) (θ : ℝ) : State → State → ℝ → Prop
  | refl : EffectivePath k θ s s 0
  | snoc : EffectivePath k θ s t x → step t c=some v →
      (∀ u : ℝ, 1≤u → u≤(v.m:ℝ)/B →
        ∃ saving, 2*(t.z:ℝ)/T<saving ∧ Branch k θ u saving) →
      EffectivePath k θ s v (x+charge t v)

private theorem effective {k : Nat} (hk : root^2≤k) {θ : ℝ}
    (h₀ : 0≤θ) (hθ : θ≤1/radicalDen)
    {s t : State} {x : ℝ} (p : RealPath s t x) : EffectivePath k θ s t x := by
  induction p with
  | refl => exact .refl
  | snoc _ h ih =>
    exact .snoc ih h (fun u hu hm => real_endpoint (step_endpoint h) hk h₀ hθ hu hm)

/-- A single path, with its actual real logarithmic charge, covers the
entire finite menu at every sufficiently large finite degree. -/
theorem effective_budget {k : Nat} (hk : root^2≤k) {θ : ℝ}
    (h₀ : 0≤θ) (hθ : θ≤1/radicalDen) :
    ∃ s x, EffectivePath k θ start s x ∧
      (∃ c, certifiedEnd s c 68720937332479399 = true) ∧
      totalCharge s x+capCorrection k ≤ (68726266220886783:ℝ)/10000000000000000 := by
  obtain ⟨s,x,p,hend,_,h⟩ := certified_real_bound limiting_certificate
  refine ⟨s,x,effective hk h₀ hθ p,hend, (add_le_add h (clipping_price hk)).trans ?_⟩
  norm_num [D]

/-- Beyond the terminal modulus the finite menu covers small real
conductors while the continuous Weyl tail covers the remaining ones.
The radical parameter is the same in both branches. -/
theorem joined_tail {k : Nat} {M u θ : ℝ} (hk : root^2≤k)
    (hθ₀ : 0≤θ) (hθ : θ≤1/radicalDen) (hθM : θ≤M/k)
    (hF : F≤M) (hcap : M≤Real.sqrt k/8) (hu : 1≤u) (hm : u≤M) :
    ∃ s : ℝ, 2*(1/(14*M^2))<s ∧ Branch k θ u s := by
  by_cases h : u≤F
  · obtain ⟨_,v,_,c,hc⟩ := limiting_certificate
    simp only [certifiedEnd,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
    have he := hc.1.1.1.1.1.1.1
    have hz : T≤v.z*14*F^2 := hc.1.1.1.1.1.2
    have hB : (0:ℝ)<B := by exact_mod_cast Bpos
    have hT : (0:ℝ)<T := by exact_mod_cast Tpos
    have hfp : (0:ℝ)<F := by rw [Fval]; norm_num
    have hmp := hfp.trans_le hF
    have hp : u≤(↑(F*B:Nat):ℝ)/B := by
      rw [Nat.cast_mul,mul_div_cancel_right₀ _ hB.ne']; exact h
    have hk' := hk
    obtain ⟨s,hs,hbr⟩ := real_endpoint he hk' hθ₀ hθ hu hp
    have hv : (T:ℝ)≤(v.z:ℝ)*14*(F:ℝ)^2 := by exact_mod_cast hz
    have hfs : (F:ℝ)^2≤M^2 := (sq_le_sq₀ hfp.le hmp.le).mpr hF
    have hval : 1/(14*M^2)≤(v.z:ℝ)/T := by
      apply (div_le_div_iff₀ (by positivity) hT).mpr
      calc
        _ ≤ (v.z:ℝ)*14*(F:ℝ)^2 := by linarith only [hv]
        _ ≤ (v.z:ℝ)*14*M^2 := mul_le_mul_of_nonneg_left hfs (by positivity)
        _ = _ := by ring
    refine ⟨s,?_,hbr⟩
    calc
      _ ≤ 2*((v.z:ℝ)/T) := mul_le_mul_of_nonneg_left hval (by norm_num)
      _ = 2*v.z/T := by ring
      _ < _ := hs
  · obtain ⟨hs,hw⟩ := WaringLimit.tail_weyl (le_trans (by decide : 10000≤root^2) hk) (by simp only [Fval,Nat.cast_ofNat] at h; exact (lt_of_not_ge h).le) hm hcap hθ₀ hθM
    exact ⟨_,hs,Or.inr hw⟩

#print axioms effective_budget
#print axioms joined_tail
end WaringSharpTail




/-! Transfer from the fine conductor mesh to the standard mesh. The
real charge increases by at most one part in ten thousand. -/
noncomputable section
namespace WaringSharpTail
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem round_conductor (m : Nat) :
    (((m/100:Nat):ℝ)/WaringEnvelope.B)≤(m:ℝ)/B := by
  have h : ((m/100:Nat):ℝ)*100≤m := by exact_mod_cast Nat.div_mul_le_self m 100
  norm_num [WaringEnvelope.B,B] at *
  linarith only [h]

private theorem rescaled_stage {k z m c : Nat} (hk : root^2≤k)
    (hm : m≤F*B) (he : endpoint z c=some m) :
    WaringEnvelope.ConductorsAt Branch k z (m/100) := by
  let θ := WaringEnvelope.actualTheta (m/100) k
  have ht : θ≤1/radicalDen := by
    have hK : (32400000000:ℝ)≤k := by exact_mod_cast hk
    have h : (m:ℝ)≤300000000 := by exact_mod_cast hm
    have hm' := round_conductor m
    have hkp : 0<(k:ℝ) := by linarith only [hK]
    dsimp [θ,WaringEnvelope.actualTheta]
    norm_num [WaringEnvelope.B,B,root,radicalDen,F] at hm' ⊢
    apply (div_le_iff₀ (by positivity)).2
    linarith only [hK,hm',h]
  have hpos : 0≤θ := by dsimp [θ,WaringEnvelope.actualTheta];positivity
  obtain ⟨σ,hs,h⟩ := endpoint_covers hk hpos ht he
  refine ⟨(σ:ℝ)/T,?_,fun u hu hm' => h u hu.le (hm'.trans (round_conductor m))⟩
  have hT : (0:ℝ)<T := by norm_num [T]
  change 2*((z:ℝ)/T)<_
  rw [←mul_div_assoc]
  exact (div_lt_div_iff_of_pos_right hT).2 (by exact_mod_cast hs)

private theorem rounded_charge {s t : State} (hm : B≤t.m) (hz : 0<t.z) (hzz : t.z<s.z) :
    2*Real.log ((s.z:ℝ)/t.z)/WaringEnvelope.length (t.m/100) ≤
      (10001/10000:ℝ)*charge s t := by
  have hlo : 10000≤t.m/100 := by change 1000000≤t.m at hm;omega
  have hround : 10000*t.m≤10001*100*(t.m/100) := by omega
  have hround' : 10000*(t.m:ℝ)≤10001*100*(((t.m/100:Nat):ℝ)) := by exact_mod_cast hround
  have hpos : 0<(t.m:ℝ) := by exact_mod_cast (show 0<t.m from (by decide : 0<B).trans_le hm)
  have hpos' : 0<((t.m/100:Nat):ℝ) := by exact_mod_cast (show 0<t.m/100 by omega)
  have hlog : 0≤Real.log ((s.z:ℝ)/t.z) := Real.log_nonneg
    ((one_le_div (by exact_mod_cast hz)).2 (by exact_mod_cast hzz.le))
  unfold WaringEnvelope.length charge
  norm_num [WaringEnvelope.B,WaringEnvelope.U,WaringEnvelope.V,B,retentionNum,retentionDen]
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_right hround' hlog]

private theorem step_info {s t : State} {c : Nat} (ok : step s c=some t) :
    endpoint s.z c=some t.m ∧ s.m≤t.m ∧ t.m≤F*B ∧ 0<t.z ∧ t.z<s.z ∧
      (s.z=z₀ → retentionNum*(t.m/100)*T>2*(T-z₀)*retentionDen*(B/100)) := by
  cases h : endpoint s.z c with
  | none => simp [step,h] at ok
  | some m =>
    simp only [step,h,bind,Option.bind,pure] at ok
    split at ok
    · contradiction
    · rename_i hn
      simp only [Bool.not_eq_true',Bool.not_eq_false,Bool.and_eq_true,
        decide_eq_true_eq,Bool.or_eq_true,bne_iff_ne] at hn
      injection ok with ht
      subst t
      refine ⟨rfl,hn.1.1.1.1.1,hn.1.1.1.1.2.le,hn.1.1.1.2,hn.1.1.2,?_⟩
      intro hz
      simpa [hz] using hn.2

private theorem path_modulus {s t : State} {x : ℝ} (p : RealPath s t x) : s.m≤t.m := by
  induction p with
  | refl => exact le_rfl
  | snoc _ h ih => exact ih.trans (step_info h).2.1

/-- Every completed path yields an ordinary indexed menu on the standard mesh. -/
theorem rounded_menu {k : Nat} (hk : root^2≤k) {s : State} {x : ℝ}
    (p : RealPath start s x) (m c : Nat) (he : endpoint s.z c=some m)
    (hinc : s.m≤m) (hcap : m≤F*B)
    (hgain : s.z=z₀ → retentionNum*(m/100)*T>2*(T-z₀)*retentionDen*(B/100)) :
    ∃ R : ℝ, WaringEnvelope.MathematicalMenu Branch k z₀ s.z (m/100) R ∧
      R≤(10001/10000:ℝ)*x := by
  induction p generalizing m c with
  | refl =>
    have hi : WaringEnvelope.B≤m/100 := by change 1000000≤m at hinc;change 10000≤m/100;omega
    exact ⟨0,.initial _ hi (rescaled_stage hk hcap he) (hgain rfl),by norm_num⟩
  | @snoc t y e v p h ih =>
    obtain ⟨hp,hm,hb,hz,hzz,hg⟩ := step_info h
    obtain ⟨R,menu,hR⟩ := ih v.m e hp hm hb hg
    have hv : B≤v.m := (path_modulus p).trans hm
    have hc := rounded_charge hv hz hzz
    refine ⟨_,.next menu _ _ hz hzz (Nat.div_le_div_right hinc) (rescaled_stage hk hcap he),?_⟩
    change R+2*Real.log ((t.z:ℝ)/v.z)/WaringEnvelope.length (v.m/100)≤_
    linarith only [hc,hR]

#print axioms rounded_menu
end WaringSharpTail




/-! A common saving on the full conductor interval of each effective
step, including the extension past 300 up to the degree-dependent cap. -/
noncomputable section
namespace WaringSharpTail
open Set
set_option maxRecDepth 8192

theorem Branch.lower {k : Nat} {θ u s t : ℝ} (h : Branch k θ u s) (ht : t≤s) :
    Branch k θ u t := by
  rcases h with ⟨w,safe,hw⟩|hw
  · exact Or.inl ⟨w,safe,ht.trans hw⟩
  · exact Or.inr (hw.mono le_rfl le_rfl ht)

def Conductors (k : Nat) (height M : ℝ) : Prop :=
  ∃ σ, 2*height<σ ∧ ∀ u : ℝ, 1<u → u≤M → Branch k (M/k) u σ

def Update (P : ℕ → ℝ → Prop) (k : ℕ) : Prop :=
  ∀ r x height M, P r x → 0≤x → Conductors k height M →
    P (r+2) (max 0 (x-(2/k)*min height (((retentionNum:ℝ)/retentionDen)*M*x/2)))

theorem Update.natural {P k} (step : Update P k) : WaringEnvelope.StageUpdate Branch P k := by
  intro r x z m hP hx h
  obtain ⟨σ,hs,hu⟩ := h
  have hh : Conductors k (WaringEnvelope.normalizedHeight z) ((m:ℝ)/WaringEnvelope.B) := by
    refine ⟨σ,hs,?_⟩
    have e : WaringEnvelope.actualTheta (m:ℕ) k = ((m:ℝ)/WaringEnvelope.B)/k := by
      unfold WaringEnvelope.actualTheta
      rw [div_div]
    rw [←e]
    exact hu
  have he := step r x _ _ hP hx hh
  have e : WaringEnvelope.length m = ((retentionNum:ℝ)/retentionDen)*((m:ℝ)/WaringEnvelope.B) := by
    unfold WaringEnvelope.length
    norm_num [WaringEnvelope.B,WaringEnvelope.U,WaringEnvelope.V,retentionNum,retentionDen]
    ring
  rwa [e]

private theorem theta_bound {k : ℕ} (hk : root^2≤k) {M : ℝ} (hm : M≤Real.sqrt k/8) :
    M/k≤1/radicalDen := by
  have hr' : 0<(root:ℝ) := by norm_num [root]
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k from (by decide : 0<root^2).trans_le hk)
  have hsq := Real.sq_sqrt hk'.le
  have hr : (root:ℝ)≤Real.sqrt k := (Real.le_sqrt (Nat.cast_nonneg root) hk'.le).2 (by exact_mod_cast hk)
  rw [radicalDen,Nat.cast_mul,Nat.cast_ofNat]
  apply (div_le_div_iff₀ hk' (by positivity)).2
  have h := mul_le_mul_of_nonneg_right hm (by positivity : 0≤8*(root:ℝ))
  have hs := mul_le_mul_of_nonneg_left hr (Real.sqrt_nonneg (k:ℝ))
  nlinarith only [h,hs,hsq]

theorem tail_conductors {k : ℕ} (hk : root^2≤k) (M : ℝ) (hM : M∈Icc (F:ℝ) (Real.sqrt k/8)) :
    Conductors k (1/(14*M^2)) M := by
  obtain ⟨_,v,_,c,hc⟩ := limiting_certificate
  simp only [certifiedEnd,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hc
  have he := hc.1.1.1.1.1.1.1
  have hz : T≤v.z*14*F^2 := hc.1.1.1.1.1.2
  have hF : (0:ℝ)<F := by norm_num [F]
  have hT : (0:ℝ)<T := by norm_num [T]
  have hB : (0:ℝ)<B := by norm_num [B]
  have hpM := hF.trans_le hM.1
  have hθ : 0≤M/k := by positivity
  obtain ⟨σ,hs,small⟩ := endpoint_covers hk hθ (theta_bound hk hM.2) he
  have hs' : 2*((v.z:ℝ)/T)<(σ:ℝ)/T := by
    rw [←mul_div_assoc];exact (div_lt_div_iff_of_pos_right hT).2 (by exact_mod_cast hs)
  have h₂ : 1/(14*M^2)≤(v.z:ℝ)/T := by
    apply (div_le_div_iff₀ (by positivity) hT).2
    rw [one_mul,←mul_assoc]
    have hZ : (T:ℝ)≤(v.z:ℝ)*14*(F:ℝ)^2 := by exact_mod_cast hz
    exact hZ.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hF.le hM.1 2) (by positivity))
  have h₁ := (WaringLimit.tail_weyl (le_trans (by decide : 10000≤root^2) hk)
    (by simpa [F] using hM.1) le_rfl hM.2 hθ le_rfl).1
  refine ⟨min ((σ:ℝ)/T) (29/(200*M^2)),lt_min ((mul_le_mul_of_nonneg_left h₂ (by norm_num : (0:ℝ)≤2)).trans_lt hs') h₁,?_⟩
  intro u h1 hu
  by_cases h : u≤(F:ℝ)
  · have hp : u≤((F*B:Nat):ℝ)/B := by rwa [Nat.cast_mul,mul_div_cancel_right₀ _ hB.ne']
    have hs₀ : Branch k (M/k) u ((σ:ℝ)/T) := small u h1.le hp
    exact hs₀.lower (min_le_left _ _)
  · have hw := (WaringLimit.tail_weyl (le_trans (by decide : 10000≤root^2) hk)
      (by simpa [F] using (le_of_not_ge h)) hu hM.2 hθ le_rfl).2
    exact (show Branch k (M/k) u (29/(200*M^2)) from Or.inr hw).lower (min_le_right _ _)

#print axioms tail_conductors
end WaringSharpTail




/-! Even integer moment orders at every degree in the large-degree band.
The only hypotheses are the seed mean value and the analytic fibre update. -/
noncomputable section
namespace WaringSharpTail
open WaringEnvelope (IndexedStages normalizedHeight seedDefect seedOrder clippedStop evenOrder)
open Set
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem large_degree_shortening_order {k : ℕ} (hk : root^2≤k) (P : ℕ → ℝ → Prop)
    (seed : P (evenOrder (k*seedOrder z₀)) (seedDefect z₀)) (step : WaringEnvelope.ShorteningStep Branch P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6872927/1000000 := by
  obtain ⟨s,x,path,⟨c,hcheck⟩,hrx,hprice⟩ := certified_real_bound limiting_certificate
  have htest := hcheck
  simp only [certifiedEnd,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] at htest
  obtain ⟨hterminal,hm,hZ,_,_,_,_,hcost⟩ := htest
  have hstart : s.z=z₀ → retentionNum*(F*B/100)*T>2*(T-z₀)*retentionDen*(B/100) :=
    fun _ => by decide +kernel
  obtain ⟨R,menu,hR⟩ := rounded_menu hk path _ c hterminal hm le_rfl hstart
  obtain ⟨p⟩ := menu.indexed (by decide : 0<z₀)
  have h2 : 2*D+baseLog+s.cost≤68720937332479399 := by
    unfold finalCost at hcost;omega
  have hxbound : x≤3 := by
    have hsc : s.cost≤3*D := by norm_num [D,baseLog] at h2 ⊢;omega
    have hD : (0:ℝ)<D := by norm_num [D]
    apply hrx.trans ((div_le_iff₀ hD).2 (by exact_mod_cast hsc))
  have hprec := add_le_add hprice (clipping_price hk)
  let v : ℝ := (retentionNum:ℝ)/retentionDen
  let cap := Real.sqrt (k:ℝ)/8
  let fee := 16/Real.sqrt (k:ℝ)
  have hk' : (32400000000:ℝ)≤k := by exact_mod_cast hk
  have hkp : (0:ℝ)<k := by linarith
  have hk1 : 1≤(k:ℝ) := by linarith
  have hlog := Real.log_nonneg hk1
  have hroot : 0<Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hkp
  have hF : (0:ℝ)<F := by norm_num [F]
  have hv : 0<v := by norm_num [v,retentionNum,retentionDen]
  have hv1 : v≤1 := by norm_num [v,retentionNum,retentionDen]
  have hcap : (F:ℝ)≤cap := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<8)).2
    apply (Real.le_sqrt (by positivity) hkp.le).2
    calc
      ((F:ℝ)*8)^2 ≤ (root:ℝ)^2 := by norm_num [F,root]
      _ ≤ (k:ℝ) := by exact_mod_cast hk
  have hfee : 0<fee := div_pos (by norm_num) hroot
  have hfee1 : fee≤1 := by
    apply (div_le_one hroot).2
    exact (Real.le_sqrt (by norm_num) hkp.le).2 (by linarith)
  have hden : 0<(k:ℝ)*(Real.log k+81/10) := mul_pos hkp (by linarith)
  have hsdef : clippedStop k=fee/((k:ℝ)*(Real.log k+81/10)) := by
    unfold clippedStop fee;rw [div_div];congr 1;ring
  have ht : 0<clippedStop k := by rw [hsdef];exact div_pos hfee hden
  have hlo : WaringEnvelope.T≤20*z₀ := by decide
  have hhi : 2*z₀≤WaringEnvelope.T := by decide
  obtain ⟨hz,_,hseed0,_,hseed⟩ := WaringEnvelope.seed_range z₀ hlo hhi
  have hle : clippedStop k≤seedDefect z₀ := by
    apply le_trans _ (hz.trans hseed0)
    rw [hsdef];apply (div_le_iff₀ hden).2
    nlinarith only [hk',hfee1,mul_nonneg hkp.le hlog]
  have hlast : p.lengthAt p.N=v*F := by
    unfold IndexedStages.lengthAt WaringEnvelope.length
    rw [p.lastModulus]
    norm_num [v,WaringEnvelope.U,WaringEnvelope.V,WaringEnvelope.B,retentionNum,retentionDen,B,F]
  have hheight : 1/(14*(F:ℝ)^2)≤p.heightAt p.N := by
    have hT : (0:ℝ)<T := by norm_num [T]
    unfold IndexedStages.heightAt
    rw [p.lastHeight]
    apply (div_le_div_iff₀ (by positivity) hT).2
    rw [one_mul,←mul_assoc]
    exact_mod_cast hZ
  have integr := p.extended_degree_integral v F k (seedDefect z₀) hv hv1 hF hk1
    hcap hlast hheight (p.starting_knee hlo hhi)
  have h₃ : 3*z₀≤WaringEnvelope.T := by decide
  have hmk : F*B/100 < WaringEnvelope.B*k := (by decide : F*B/100 < WaringEnvelope.B*root^2).trans_le (Nat.mul_le_mul_left _ hk)
  obtain ⟨r,a,y,er,ea,hP,hy,hyt,ha,hord⟩ :=
    WaringEnvelope.even_moment_order_of_integral (WaringEnvelope.Guarded P k) k ((by decide : 0<root^2).trans_le hk)
    (p.extendedDrift v F cap) (seedDefect z₀) (clippedStop k) (seedOrder z₀) fee
    ht.le hle hseed hfee.le (p.continuous_extendedDrift v F cap hF).continuousOn
    (fun t h => p.positive_extendedDrift v F cap t (ht.trans_le h.1))
    ((p.monotone_extendedDrift v F cap hv hF hcap).monotoneOn _)
    (WaringEnvelope.guarded_seed hlo h₃ seed) (fun n y hP hy => by
      rcases p.extendedDrift_attained v F cap y hF hcap with ⟨i,hi,he⟩|⟨M,hM,he⟩
      · rw [he];exact p.guarded_row hi hhi hmk step hP hy
      · rw [he]
        obtain ⟨hrk,er,hrP⟩ := hP
        have hM1 : 1<M := (by norm_num [F] : (1:ℝ)<F).trans_le hM.1
        have hMk : M<(k:ℝ) := by
          apply lt_of_le_of_lt hM.2
          apply (div_lt_iff₀ (by norm_num : (0:ℝ)<8)).2
          have hl : Real.sqrt (k:ℝ)≤k := (Real.sqrt_le_iff).2
            ⟨hkp.le,by nlinarith only [sq_nonneg ((k:ℝ)-1),hk1]⟩
          linarith only [hl,hkp]
        have hMp : 0<M := zero_lt_one.trans hM1
        refine ⟨by omega,er.add (by decide : Even 2),?_⟩
        exact step n y _ M hrk er hrP hy (by positivity) hM1 hMk (tail_conductors hk M hM))
  rw [hsdef] at hyt
  refine ⟨r,a,y,er,ea,hP.2.2,hy,WaringEnvelope.ordinary_minor_gap k a
    ((by decide : 1≤root^2).trans hk) y fee hfee hyt ha,?_⟩
  have hs₀ : p.heightAt 0=normalizedHeight z₀ := by unfold IndexedStages.heightAt normalizedHeight;rw [p.first]
  have hsN : p.heightAt p.N=(s.z:ℝ)/T := by unfold IndexedStages.heightAt;rw [p.lastHeight];rfl
  rw [hs₀,hsN] at integr
  have hseedID := WaringEnvelope.seed_price_identity z₀ (by decide) hhi
  have hscal : totalCharge s x=2+Real.log (((WaringEnvelope.T-z₀:ℕ):ℝ)/z₀)+x+
      2/(v*F)*Real.log (14*(F:ℝ)^2*((s.z:ℝ)/T))+4/(v*F) := by
    rw [show WaringEnvelope.T=T from rfl]
    unfold totalCharge
    push_cast
    rw [show (s.z:ℝ)*F^2*14/T=14*(F:ℝ)^2*((s.z:ℝ)/T) by ring]
    norm_num [v,F,retentionNum,retentionDen]
    ring
  have hcorr : capCorrection k=16/v*(Real.log ((64/(14*v))*(Real.log k+81/10))/Real.sqrt k)+fee+7/k :=
    by norm_num [capCorrection,v,fee,retentionNum,retentionDen]
  rw [hscal,hcorr] at hprec
  norm_num only [D,Nat.cast_pow,Nat.cast_ofNat] at hprec
  have h1 : ((r+a+1:ℕ):ℝ)/k=((r+a:ℕ):ℝ)/k+1/k := by push_cast;ring
  rw [h1]
  dsimp only [cap] at hord
  have hc : R-x≤3/10000 := by linarith only [hR,hxbound]
  have hround : (6:ℝ)/k+1/k=7/k := by ring
  linarith only [hord,integr,hseedID,hprec,hc,hround]

theorem large_degree_order {k : ℕ} (hk : root^2≤k) (P : ℕ → ℝ → Prop)
    (seed : P (evenOrder (k*seedOrder z₀)) (seedDefect z₀)) (step : Update P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6872927/1000000 := by
  apply large_degree_shortening_order hk P seed
  intro r x z M _ _ hp hx _ _ _ h
  exact step r x z M hp hx h

#print axioms large_degree_shortening_order
#print axioms large_degree_order
end WaringSharpTail

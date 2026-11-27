import WaringEnvelope.IntegerCells
import WaringEnvelope.WeylInteger
import WaringEnvelope.TailCellSound

/-! # Kernel-checked conductor coverage interpreted at every real height -/
noncomputable section
namespace WaringEnvelope

def thetaData (c : Config) (m : ℕ) : ℕ × ℕ :=
  if c.last=0 then (1,8*c.root) else (m,B*c.first)

def stageTheta (c : Config) (m : ℕ) : ℝ :=
  ((thetaData c m).1:ℝ)/(thetaData c m).2

def StageConclusion (k : ℕ) (θ u σ : ℝ) : Prop :=
  (∃ j, j+2≤k ∧ DifferencingBranch θ j u σ) ∨ WeylBranch k θ u σ

theorem config_indices_pos (c : Config) (hc : configOK c=true) : 0<c.first ∧ 0<c.root := by
  simp only [configOK,Bool.and_eq_true,decide_eq_true_eq] at hc
  constructor
  · omega
  · by_contra! h
    have hr : c.root=0 := by omega
    simp [hr] at hc
    omega

private theorem thetaData_pos (c : Config) (m : ℕ) (hc : 0<c.first) (hr : 0<c.root) :
    0<(thetaData c m).2 := by
  by_cases h0 : c.last=0
  · simpa [thetaData,h0] using hr
  · simp [thetaData,h0,B,hc]

/-- Each accepted finite-grid extension has a real differencing branch or
a real Weyl branch at every conductor in its interval. -/
theorem nextEndpoint_sound (c : Config) (m sig p token q : ℕ) (u : ℝ)
    (hc : 0<c.first) (hr : 0<c.root)
    (e : nextEndpoint c m sig p token = some q) (hp : p<q)
    (hu : (p:ℝ)/B≤u) (hv : u≤(q:ℝ)/B) (hm : u≤(m:ℝ)/B) :
    StageConclusion c.first (stageTheta c m) u ((sig:ℝ)/T) := by
  obtain ⟨h,d,hdata⟩ : ∃ h d : ℕ, thetaData c m = (h,d) := by
    rcases he : thetaData c m with ⟨n,v⟩
    exact ⟨n,v,rfl⟩
  have hd : 0<d := by simpa only [hdata] using thetaData_pos c m hc hr
  have hth : stageTheta c m = (h:ℝ)/d := by simp [stageTheta,hdata]
  rw [hth]
  unfold thetaData at hdata
  simp only [nextEndpoint,hdata] at e
  by_cases ha : token≤41
  · simp only [ha,if_true] at e
    split at e <;> try contradiction
    rename_i guard
    simp only [Bool.not_eq_true',Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
      Bool.not_eq_false'] at guard
    have hguard : 1≤token ∧ token-1+2≤c.first ∧ 2*(2^(token-1)*sig)≤T ∧
        (token-1=0 ∨ h*T≤d*(T-2^(token-1)*sig)) ∧
        B*((token-1)*h*T+2*(2^(token-1)*sig)*d)≤p*(T*d) := by grind
    have hh := Option.some.inj e
    have hq' : q*T≤B*((token-1+2)*T-(4*(2^(token-1)*sig)-2*sig)) := by
      rw [←hh]
      exact Nat.div_mul_le_self _ _
    exact Or.inl ⟨token-1,hguard.2.1,dyadic_integer_cell _ h d sig p q u hd
      hguard.2.2.1 hguard.2.2.2.1 hguard.2.2.2.2 hq' hu hv⟩
  · simp only [ha,if_false] at e
    by_cases hw : token≤240
    · simp only [hw,if_true] at e
      split at e <;> try contradiction
      rename_i guard
      simp only [Bool.not_eq_true',Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_false'] at guard
      let j := token-40
      have hguard : 2≤j ∧ j≤c.first ∧
          B*(j+1)*(weylWeight j*sig*d+j*h*T)≤p*(T*d) := by
        dsimp [j,weylWeight]
        grind
      have hh := Option.some.inj e
      have hq' : q*(T*d)≤B*min ((j+1)*(T*d-h*T-weylWeight j*sig*d))
          (j*(T*d)-j*h*T-weylWeight j*sig*d) := by
        rw [←hh]
        exact Nat.div_mul_le_self _ _
      exact Or.inr (weyl_integer_cell j c.first h d sig p q u hd hguard.1 hguard.2.1
        (by omega) hguard.2.2 hq' hu hv)
    · simp only [hw,if_false] at e
      split at e <;> try contradiction
      rename_i hb
      simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at hb
      obtain ⟨⟨_,hn⟩,hcell⟩ := hb
      simp only [hn,if_false,Prod.mk.injEq] at hdata
      obtain ⟨rfl,rfl⟩ := hdata
      exact Or.inr (by simpa using tailCell_sound c.first m sig p (token-241) u hc hcell hu hm)

/-- A successful interval chain proves a pointwise claim about every real
conductor in the continuum, including nonintegral and irrational values. -/
theorem chain_sound_of_positive (c : Config) (m sig code : ℕ) (u : ℝ)
    (hk : 0<c.first) (hr : 0<c.root) (h : chain c m sig 16 B code=true)
    (hl : 1<u) (hu : u≤(m:ℝ)/B) :
    StageConclusion c.first (stageTheta c m) u ((sig:ℝ)/T) := by
  have hB : (0:ℝ)<B := by norm_num [B]
  let cut (a : ℕ) := u≤(a:ℝ)/B
  have mono : ∀ {a b : ℕ}, a≤b → cut a → cut b := fun hab hcut =>
    hcut.trans (div_le_div_of_nonneg_right (by exact_mod_cast hab) hB.le)
  have hinit : ¬cut B := by simpa [cut,div_self hB.ne'] using not_le.mpr hl
  obtain ⟨p,q,t,hp,hq,hit⟩ := chain_hits_cut c m sig cut mono hu 16 B code h hinit
  have hp' : (p:ℝ)/B < u := lt_of_not_ge hp
  have hq' : u≤(q:ℝ)/B := hq
  have hpq : p<q := by
    by_contra! hn
    exact hp (mono hn hq)
  exact nextEndpoint_sound c m sig p t q u hk hr hit hpq hp'.le hq' hu

theorem chain_sound (c : Config) (m sig code : ℕ) (u : ℝ)
    (hc : configOK c=true) (h : chain c m sig 16 B code=true)
    (hl : 1<u) (hu : u≤(m:ℝ)/B) :
    StageConclusion c.first (stageTheta c m) u ((sig:ℝ)/T) := by
  obtain ⟨hk,hr⟩ := config_indices_pos c hc
  exact chain_sound_of_positive c m sig code u hk hr h hl hu

#print axioms chain_sound
end WaringEnvelope

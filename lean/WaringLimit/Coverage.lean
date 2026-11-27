import WaringLimit.Meaning
import WaringEnvelope.WeylCells

/-! The limiting menu gives a disjunction of real inequalities at every
real conductor in the interval, including the points between rounded
integer endpoints. The arithmetic exponent-pair branch uses a checked
word and the other branch is the degree-reduction Weyl estimate. -/
noncomputable section
namespace WaringLimit

set_option maxRecDepth 8192
set_option maxHeartbeats 600000

private theorem B_pos : 0<B := by decide
private theorem T_pos : 0<T := by decide
attribute [local irreducible] T B F words

def Covered (σ : Nat) (u : ℝ) : Prop :=
  (∃ e ∈ words, entryOK e = true ∧
    (σ:ℝ)/T ≤ 1-(e.y:ℝ)/e.den-(e.x:ℝ)/e.den*(u-1)) ∨
  WaringEnvelope.WeylBranch (2*F+1) 0 u ((σ:ℝ)/T)

private theorem floor_mul (a b : Nat) : ((a/b:Nat):ℝ)*b ≤ (a:ℝ) := by
  exact_mod_cast Nat.div_mul_le_self a b

private theorem cell {σ j h : Nat} {u : ℝ} (hj : 2≤j) (hk : j≤2*F+1)
    (ht : 2*(WaringEnvelope.weylWeight j*σ)≤T)
    (hlo : B*(j+1)*(WaringEnvelope.weylWeight j*σ) ≤ h*T)
    (hu : (h:ℝ)/B ≤ u)
    (hhi : u ≤ ((B*min ((j+1)*(T-WaringEnvelope.weylWeight j*σ))
        (j*T-WaringEnvelope.weylWeight j*σ)/T : Nat):ℝ)/B) : Covered σ u := by
  let t := WaringEnvelope.weylWeight j*σ
  have hB : (0:ℝ)<B := by exact_mod_cast B_pos
  have hT : (0:ℝ)<T := by exact_mod_cast T_pos
  have ht' : t≤T := by change 2*t≤T at ht; omega
  have htj : t≤j*T := ht'.trans (Nat.le_mul_of_pos_left T (by omega))
  have hl : (B:ℝ)*(j+1)*t ≤ (h:ℝ)*T := by exact_mod_cast hlo
  have hA := Nat.min_le_left ((j+1)*(T-t)) (j*T-t)
  have hC := Nat.min_le_right ((j+1)*(T-t)) (j*T-t)
  have hi := (le_div_iff₀ hB).mp hhi
  have hcalc := (mul_le_mul_of_nonneg_right hi hT.le).trans
    (floor_mul (B*min ((j+1)*(T-t)) (j*T-t)) T)
  have ha := hcalc.trans (show ((B*min ((j+1)*(T-t)) (j*T-t):Nat):ℝ) ≤
       (B:ℝ)*(j+1)*(T-t) by
     rw [mul_assoc]
     exact_mod_cast Nat.mul_le_mul_left B hA)
  have hb := hcalc.trans (show ((B*min ((j+1)*(T-t)) (j*T-t):Nat):ℝ) ≤
       (B:ℝ)*(j*T-t) by
     exact_mod_cast Nat.mul_le_mul_left B hC)
  have ha' : u*T ≤ (j+1:ℝ)*(T-t) := (mul_le_mul_iff_right₀ hB).mp (by
     calc
       (B:ℝ)*(u*T) = u*B*T := by ring
       _ ≤ (B:ℝ)*(j+1)*(T-t) := ha
       _ = _ := by ring)
  have hb' : u*T ≤ (j:ℝ)*T-t := (mul_le_mul_iff_right₀ hB).mp (by
     simpa only [mul_left_comm,mul_assoc] using hb)
  have hl' : ((j:ℝ)+1)*t ≤ u*T := (mul_le_mul_iff_right₀ hB).mp (by
     calc
       (B:ℝ)*((j+1)*t) = B*(j+1)*t := by ring
       _ ≤ (h:ℝ)*T := hl
       _ ≤ u*B*T := mul_le_mul_of_nonneg_right ((div_le_iff₀ hB).mp hu) hT.le
       _ = _ := by ring)
  have hval : (WaringEnvelope.weylWeight j:ℝ)*((σ:ℝ)/T) = (t:ℝ)/T := by
    dsimp [t]
    push_cast
    ring
  right
  apply WaringEnvelope.interval_has_weyl_branch j _ _ _ _ hj hk
  · simp only [WaringEnvelope.weylLower,mul_zero,add_zero,hval,mul_div_assoc']
    exact (div_le_iff₀ hT).mpr hl'
  · simp only [WaringEnvelope.weylUpper,sub_zero,mul_zero,hval,le_min_iff]
    constructor
    · field_simp
      linarith only [ha']
    · field_simp
      linarith only [hb']

private theorem chain {σ h code n : Nat} (fuel : Nat)
    (ok : weylChain fuel σ h code = some n)
    (base : ∀ u : ℝ, 1≤u → u≤(h:ℝ)/B → Covered σ u) :
    ∀ u : ℝ, 1≤u → u≤(n:ℝ)/B → Covered σ u := by
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
      · contradiction
      · rename_i hv
        simp only [Bool.not_eq_true',Bool.not_eq_false,Bool.and_eq_true,decide_eq_true_eq] at hv
        split at ok
        · apply ih ok
          intro u hu hup
          by_cases hh : u≤(h:ℝ)/B
          · exact base u hu hh
          · exact cell hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 (le_of_not_ge hh) hup
        · contradiction

private theorem initial {σ : Nat} (e : Entry) (emem : e ∈ words)
    (ex : 0<e.x) (ed : 0<e.den) (spos : 0<σ)
    (hb : e.den*σ≤(e.den-e.y)*T) (u : ℝ)
    (hu : u≤ ((B+B*((e.den-e.y)*T-e.den*σ)/(e.x*T) : Nat):ℝ)/B) :
    Covered σ u := by
  have hB : (0:ℝ)<B := by exact_mod_cast B_pos
  have hT : (0:ℝ)<T := by exact_mod_cast T_pos
  have hx : (0:ℝ)<e.x := by exact_mod_cast ex
  have hd : (0:ℝ)<e.den := by exact_mod_cast ed
  have hy : e.y≤e.den := by
    by_contra! hy
    rw [Nat.sub_eq_zero_of_le hy.le, Nat.zero_mul] at hb
    exact (Nat.mul_pos ed spos).not_ge hb
  have hOK := (Array.all_eq_true_iff_forall_mem.mp words_checked.2) e emem
  have hraw := floor_mul (B*((e.den-e.y)*T-e.den*σ)) (e.x*T)
  simp only [Nat.cast_mul,Nat.cast_sub hy,Nat.cast_sub hb] at hraw
  have hsub := (le_div_iff₀ hB).mp hu
  rw [Nat.cast_add] at hsub
  have hh : u*(B:ℝ)-B ≤ (↑(B*((e.den-e.y)*T-e.den*σ)/(e.x*T):Nat):ℝ) := by linarith
  have hh' := (mul_le_mul_of_nonneg_right hh (mul_pos hx hT).le).trans hraw
  have hcore : (u-1)*e.x*T ≤ ((e.den:ℝ)-e.y)*T-e.den*σ :=
    (mul_le_mul_iff_right₀ hB).mp (by nlinarith only [hh'])
  left
  refine ⟨e,emem,hOK,?_⟩
  field_simp
  linarith only [hcore]

/-- The verified limiting certificate covers every real conductor in
the certified interval with an arithmetic pair or one of the three
precise Weyl inequalities. The margin above 2z is strict. -/
theorem endpoint_covers {z code m : Nat} (ok : endpoint z code = some m) :
    ∃ σ : Nat, 2*z<σ ∧ ∀ u : ℝ, 1≤u → u≤(m:ℝ)/B → Covered σ u := by
  cases he : words[code%256]? with
  | none => simp [endpoint,he] at ok
  | some e =>
    simp only [endpoint,he,bind,Option.bind,pure] at ok
    split at ok
    · contradiction
    · rename_i hv
      simp only [Bool.not_eq_true',Bool.not_eq_false,Bool.and_eq_true,decide_eq_true_eq] at hv
      let σ := WaringEnvelope.ceilDiv (200001*z) 100000
      let h := B+B*((e.den-e.y)*T-e.den*σ)/(e.x*T)
      have emem : e ∈ words := Array.mem_of_getElem? he
      have hed := (Array.all_eq_true_iff_forall_mem.mp words_checked.2) e emem
      simp only [entryOK,Bool.and_eq_true,decide_eq_true_eq] at hed
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
        apply chain 3 hc _ u hu hun
        intro v _ huv
        exact initial e emem hed.1.1.1.1.2 hed.1.1.1.2 (by omega) hv.2 v huv

#print axioms endpoint_covers
end WaringLimit

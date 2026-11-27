import WaringSmall.Coverage
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Real meanings of the checked moment rules -/
namespace WaringSmall
noncomputable section

def Fr.val (x : Fr) : ℝ := x.n / x.d

private theorem denpos {x : Fr} (h : valid x=true) : (0:ℝ)<x.d := by
  exact_mod_cast (show 0<x.d from by simpa [valid] using h)

private theorem validPlus {a b : Fr} (ha : valid a=true) (hb : valid b=true) :
    valid (plus a b)=true := by simpa [valid,plus] using And.intro ha hb

private theorem validTimes {a b : Fr} (ha : valid a=true) (hb : valid b=true) :
    valid (times a b)=true := by simpa [valid,times] using And.intro ha hb

private theorem validMinus {a b : Fr} (ha : valid a=true) (hb : valid b=true) :
    valid (minus a b)=true := by simpa [valid,minus] using And.intro ha hb

private theorem leVal {a b : Fr} (ha : valid a=true) (hb : valid b=true) (h : le a b=true) :
    a.val≤b.val := by
  apply (div_le_div_iff₀ (denpos ha) (denpos hb)).2
  exact_mod_cast (show a.n*b.d≤b.n*a.d from by simpa [le] using h)

private theorem ltVal {a b : Fr} (ha : valid a=true) (hb : valid b=true) (h : lt a b=true) :
    a.val<b.val := by
  apply (div_lt_div_iff₀ (denpos ha) (denpos hb)).2
  exact_mod_cast (show a.n*b.d<b.n*a.d from by simpa [lt] using h)

private theorem eqVal {a b : Fr} (ha : valid a=true) (hb : valid b=true) (h : eq a b=true) :
    a.val=b.val := by
  apply (div_eq_div_iff (denpos ha).ne' (denpos hb).ne').2
  exact_mod_cast (show a.n*b.d=b.n*a.d from by simpa [eq] using h)

@[simp] private theorem wholeVal (k : ℕ) : (whole k).val=k := by simp [Fr.val,whole]
@[simp] private theorem wholeValid (k : ℕ) : valid (whole k)=true := by simp [valid,whole]
private theorem plusVal {a b : Fr} (ha : valid a=true) (hb : valid b=true) :
    (plus a b).val=a.val+b.val := by
  have h₁ := (denpos ha).ne'; have h₂ := (denpos hb).ne'
  simp [Fr.val,plus]; field_simp
private theorem timesVal {a b : Fr} (_ha : valid a=true) (_hb : valid b=true) :
    (times a b).val=a.val*b.val := by
  simp [Fr.val,times,div_mul_div_comm]
private theorem minusVal {a b : Fr} (ha : valid a=true) (hb : valid b=true) (h : le b a=true) :
    (minus a b).val=a.val-b.val := by
  have hnat : b.n*a.d≤a.n*b.d := by simpa [le] using h
  have h₁ := (denpos ha).ne'; have h₂ := (denpos hb).ne'
  simp [Fr.val,minus,Nat.cast_sub hnat]; field_simp

/-- Every parameter of a derived excess has positive denominator. -/
theorem Derivation.validArgs {k seeds u d} (h : Derivation k seeds u d) :
    valid u=true ∧ valid d=true := by
  cases h with
  | seed u d h =>
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.2,h.2⟩
  | interpolate u d hl hh h =>
    simp only [interpolateOK,Bool.and_eq_true] at h
    exact h.1.1.1.1
  | step u d L M z sig hp hh hc h =>
    simp only [stepOK,Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1

/-- The real Holder inequality represented by an accepted interpolation node. -/
theorem checked_interpolation {u d l a h b : Fr}
    (hl : valid l=true) (ha : valid a=true) (hh : valid h=true) (hb : valid b=true)
    (H : interpolateOK u d l a h b=true) :
    l.val<h.val ∧ l.val≤u.val ∧ u.val≤h.val ∧
      (h.val-u.val)*a.val+(u.val-l.val)*b.val≤(h.val-l.val)*d.val := by
  simp only [interpolateOK,Bool.and_eq_true] at H
  obtain ⟨⟨⟨⟨⟨hu,hd⟩,hlt⟩,hlu⟩,huh⟩,hi⟩ := H
  have hlh : le l h=true := by
    simp only [le,decide_eq_true_eq]; exact le_of_lt (by simpa [lt] using hlt)
  have x := leVal (validPlus (validTimes (validMinus hh hu) ha)
    (validTimes (validMinus hu hl) hb)) (validTimes (validMinus hh hl) hd) hi
  rw [plusVal (validTimes (validMinus hh hu) ha) (validTimes (validMinus hu hl) hb),
    timesVal (validMinus hh hu) ha,timesVal (validMinus hu hl) hb,timesVal (validMinus hh hl) hd,
    minusVal hh hu huh,minusVal hu hl hlu,minusVal hh hl hlh] at x
  exact ⟨ltVal hl hh hlt,leVal hl hu hlu,leVal hu hh huh,x⟩

/-- The two branches of an accepted fibre update are bounded by the displayed
new excess, as inequalities of real numbers. -/
theorem checked_step {k : ℕ} (hk : 0<k) {u d p a h b L M z : Fr}
    (hp : valid p=true) (ha : valid a=true) (hh : valid h=true) (hb : valid b=true)
    (hM : valid M=true) (hz : valid z=true) (H : stepOK k u d p a h b L M z=true) :
    0<L.val ∧ L.val<M.val ∧ (k:ℝ)+2≤u.val ∧ p.val+2=u.val ∧ h.val<u.val ∧
      (1-L.val/(k:ℝ))*a.val≤d.val ∧ b.val-(u.val-h.val)*z.val≤d.val := by
  simp only [stepOK,Bool.and_eq_true,decide_eq_true_eq] at H
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu,hd⟩,hvL⟩,hL⟩,hLM⟩,hord⟩,hprev⟩,hearly⟩,hhigh⟩,hlow⟩ := H
  have hi := leVal (validTimes (wholeValid k) ha) (validPlus (validTimes (wholeValid k) hd)
    (validTimes hvL ha)) hhigh
  rw [timesVal (wholeValid k) ha, plusVal (validTimes (wholeValid k) hd) (validTimes hvL ha),
    timesVal (wholeValid k) hd,timesVal hvL ha,wholeVal] at hi
  have lo := leVal (validPlus hb (validTimes hh hz)) (validPlus hd (validTimes hu hz)) hlow
  rw [plusVal hb (validTimes hh hz),plusVal hd (validTimes hu hz),
    timesVal hh hz,timesVal hu hz] at lo
  have h₀ := leVal (wholeValid (k+2)) hu hord
  have h₁ := eqVal (validPlus hp (wholeValid 2)) hu hprev
  rw [plusVal hp (wholeValid 2),wholeVal] at h₁
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  refine ⟨div_pos (by exact_mod_cast hL) (denpos hvL),ltVal hvL hM hLM,by simpa using h₀,
    by simpa using h₁,ltVal hh hu hearly,?_,?_⟩
  · apply (mul_le_mul_iff_of_pos_right hkr).1
    calc
      ((1-L.val/(k:ℝ))*a.val)*k = k*a.val-L.val*a.val := by
        field_simp
      _ ≤ d.val*k := by nlinarith only [hi]
  · linarith only [lo]

/-- A real-valued moment theory with the three analytic inputs proved in
the manuscript. The conductor predicate implies continuous coverage by
`conduct_covers`. -/
structure RealMomentRules (k : ℕ) (seeds : List (Fr × Fr)) (P : ℝ → ℝ → Prop) : Prop where
  source : ∀ u d, (u,d)∈seeds → P u.val d.val
  interpolate : ∀ l a h b u d, P l a → P h b → l<h → l≤u → u≤h →
    (h-u)*a+(u-l)*b≤(h-l)*d → P u d
  fibre : ∀ p a h b u d L (M z sig : Fr), P p a → P h b → conduct k M z sig=true →
    0<L → L<M.val → (k:ℝ)+2≤u → p+2=u → h<u →
    (1-L/(k:ℝ))*a≤d → b-(u-h)*z.val≤d → P u d

/-- Soundness of the entire finite dependency tree in any admissible
analytic moment theory, including every interpolated rational order. -/
theorem Derivation.sound {k : ℕ} (hk : 0<k) {seeds u d} {P : ℝ → ℝ → Prop}
    (R : RealMomentRules k seeds P) (H : Derivation k seeds u d) : P u.val d.val := by
  induction H with
  | seed u d h =>
    simp only [Bool.and_eq_true] at h
    exact R.source u d (by simpa using h.1.1)
  | interpolate u d hl hh hc h₁ h₂ =>
    obtain ⟨hlt,hlu,huh,hc'⟩ := checked_interpolation hl.validArgs.1 hl.validArgs.2
      hh.validArgs.1 hh.validArgs.2 hc
    exact R.interpolate _ _ _ _ _ _ h₁ h₂ hlt hlu huh hc'
  | step u d L M z sig hp hh hc h h₁ h₂ =>
    have hc' := hc
    simp only [conduct,Bool.and_eq_true] at hc'
    have hM : valid M=true := hc'.1.1.1.1.1.1.1
    have hz : valid z=true := hc'.1.1.1.1.1.1.2
    obtain ⟨hL,hLM,hord,hprev,hearly,hhi,hlo⟩ := checked_step hk hp.validArgs.1 hp.validArgs.2
      hh.validArgs.1 hh.validArgs.2 hM hz h
    exact R.fibre _ _ _ _ _ _ _ M z sig h₁ h₂ hc hL hLM hord hprev hearly hhi hlo

/-- The accepted final minor-arc margin, including its exact real value. -/
theorem Outcome.gap {k s a cutoff : ℕ} (hk : 0<k) {seeds g} {P : ℝ → ℝ → Prop}
    (R : RealMomentRules k seeds P) (H : Outcome k s a cutoff seeds g) :
    ∃ r D : ℝ, P r D ∧ 0<g.val ∧
      r*((k*(k+1)-a:ℕ):ℝ) = ((s-a)*(k*(k+1)):ℕ) ∧
      ((k*(k+1):ℕ):ℝ)*g.val+((k*(k+1)-a:ℕ):ℝ)*D=(a:ℝ) := by
  obtain ⟨r,d,hd,ho⟩ := H
  have hv := hd.validArgs
  simp only [outcomeOK,Bool.and_eq_true,decide_eq_true_eq] at ho
  have hgp : valid g=true := ho.1.1.1.2
  have hgn : 0<g.n := ho.1.1.2
  have htime := eqVal (validTimes hv.1 (wholeValid _)) (wholeValid _) ho.1.2
  have hgain := eqVal (validPlus (validTimes (wholeValid _) hgp) (validTimes (wholeValid _) hv.2))
    (wholeValid _) ho.2
  rw [timesVal hv.1 (wholeValid _),wholeVal,wholeVal] at htime
  rw [plusVal (validTimes (wholeValid _) hgp) (validTimes (wholeValid _) hv.2),
    timesVal (wholeValid _) hgp,timesVal (wholeValid _) hv.2,wholeVal,wholeVal,wholeVal] at hgain
  exact ⟨r.val,d.val,hd.sound hk R,div_pos (by exact_mod_cast hgn) (denpos hgp),htime,hgain⟩

#print axioms Derivation.sound
#print axioms Outcome.gap
#print axioms checked_interpolation
#print axioms checked_step
end
end WaringSmall

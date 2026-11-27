import WaringEnvelope.Check

/-! # Pointwise soundness of a successful conductor chain

A monotone cut represents any real conductor threshold, including irrational
thresholds. Every threshold between the initial and final endpoint is covered
by a single accepted interval in the recorded chain.
-/
namespace WaringEnvelope

theorem chain_hits_cut (c : Config) (m sig : Nat) (cut : Nat → Prop)
    (hmono : ∀ {a b}, a≤b → cut a → cut b) (hm : cut m) :
    ∀ fuel p code, chain c m sig fuel p code = true → ¬cut p →
      ∃ a b token, ¬cut a ∧ cut b ∧ nextEndpoint c m sig a token = some b := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro p code h hnot
    simp only [chain,Bool.and_eq_true,decide_eq_true_eq] at h
    exact False.elim (hnot (hmono h.2 hm))
  | succ i ih =>
    intro p code h hnot
    by_cases hzero : code=0
    · simp only [chain,hzero,if_true,decide_eq_true_eq] at h
      exact False.elim (hnot (hmono h hm))
    · simp only [chain,hzero,if_false] at h
      cases hq : nextEndpoint c m sig p (code%256) with
      | none => simp [hq] at h
      | some q =>
        simp only [hq,Bool.and_eq_true,decide_eq_true_eq] at h
        by_cases hc : cut q
        · exact ⟨p,q,code%256,hnot,hc,hq⟩
        · exact ih q (code/256) h.2 hc

/-- First and later successful rows contain exactly the conductor and cost
checks consumed by the real-valued interpretation. -/
theorem row_properties (c : Config) (s u : State) (x : Nat)
    (h : row c s x = some u) :
    0<u.height ∧ B≤u.modulus ∧ u.modulus < B*c.first ∧
    (c.last≠0 ∨ u.modulus*8*c.root≤B*c.first) ∧
    (∃ code, chain c u.modulus (ceilDiv (20001*u.height) 10000) 16 B code=true) ∧
    ((s.modulus=0 ∧ u.height=top ∧ U*u.modulus*T>2*(T-top)*V*B ∧ u.cost=0) ∨
     (0<s.modulus ∧ u.height<s.height ∧ s.modulus≤u.modulus ∧
       u.cost=s.cost+intervalCost s.height u.height s.modulus)) := by
  unfold row at h
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

#print axioms chain_hits_cut
#print axioms row_properties
end WaringEnvelope

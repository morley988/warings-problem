import WaringFieldSmall.Check

/-! # Soundness of each recorded interval schedule
The initial order, each individual two-variable step, both parities,
the final positive minor-arc surplus, and the allowance of one extra
summand are retained as propositions. -/
namespace WaringFieldSmall

private theorem repeat_rule {P : Nat → Nat → Prop} (f : Nat → Nat)
    (rule : ∀ r x, P r x → P (r+2) (f x)) (n r d : Nat) (h : P r d) :
    P (r+2*n) (repeats f n d) := by
  induction n generalizing r d with
  | zero => simpa [repeats] using h
  | succ n ih =>
    have hh := ih (r+2) (f d) (rule r d h)
    simpa only [repeats,show r+2*(n+1)=r+2+2*n by omega] using hh

private theorem fold_rule {P : Nat → Nat → Prop} (hi : Nat) (data : List Nat) (s : State)
    (h : P s.order s.defect) (step : ∀ u∈data, ∀ r d, P r d →
      P (r+2) (fibreRound hi (unpack u) d)) :
    P (data.foldl (advance hi) s).order (data.foldl (advance hi) s).defect := by
  induction data generalizing s with
  | nil => exact h
  | cons u us ih =>
    apply ih _ (repeat_rule _ (step u (by simp)) _ _ _ h)
    exact fun v hv => step v (List.mem_cons_of_mem _ hv)

structure Applicable (band : Schedule) (k : Nat) (P : Nat → Nat → Prop) : Prop where
  base : P (2*(band.edIndex+1)) (start band.lo band.hi band.edIndex).defect
  shorten : ∀ u∈band.data, ∀ r d, k≤r → r%2=0 → P r d →
    P (r+2) (fibreRound band.hi (unpack u) d)

theorem trace_schedule (Listed : Schedule → Prop) (k : Nat) (P : Nat → Nat → Prop)
    (witness : ∃ s : Schedule, Listed s ∧ s.lo≤k ∧ k≤s.hi ∧ s.good)
    (h : ∀ band, Listed band → band.lo≤k → k≤band.hi → band.good → Applicable band k P) :
    ∃ r a d : Nat, r%2=0 ∧ a%2=0 ∧ 0<a ∧ P r d ∧
      15*k*d<(a-1)*scale ∧ 2*k<r+a ∧ 1000*(r+a+1)<6873*k := by
  obtain ⟨band,listed,hl,hh,ok⟩ := witness
  obtain ⟨base,rules⟩ := h band listed hl hh ok
  let s₀ := start band.lo band.hi band.edIndex
  let z := band.data.foldl (advance band.hi) s₀
  have hh' : 11≤band.lo ∧ band.lo≤band.hi ∧ band.hi≤s₀.order ∧ 1≤band.extra ∧
      band.extra%2=0 ∧ 1000*(z.order+band.extra+1)<6873*band.lo ∧
      2*band.hi<z.order+band.extra ∧ 15*band.hi*z.defect<(band.extra-1)*scale := by
    simpa only [Schedule.good,checked,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using ok
  let Q := fun r d => k≤r ∧ r%2=0 ∧ P r d
  have final : Q z.order z.defect := fold_rule band.hi band.data s₀
    (P:=Q) ⟨Nat.le_trans hh hh'.2.2.1,by dsimp [s₀,start];omega,base⟩ (by
      intro u hu r d state
      obtain ⟨hk,er,hP⟩ := state
      exact ⟨by omega,by omega,rules u hu r d hk er hP⟩)
  obtain ⟨_,er,fp⟩ := final
  obtain ⟨_,_,_,ha,ea,hprice,horder,hgap⟩ := hh'
  refine ⟨z.order,band.extra,z.defect,er,ea,ha,fp,?_,by omega,by omega⟩
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hh)) hgap

#print axioms trace_schedule
end WaringFieldSmall

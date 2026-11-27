import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-! # Orthogonal principal layers in a conductor quotient -/
namespace WaringLinear
variable {R : Type*} [CommRing R] [IsDomain R]

theorem product_conductor_annihilator (c d : R) (hc : c≠0)
    (x : R ⧸ Ideal.span {c*d}) :
    Ideal.Quotient.mk (Ideal.span {c*d}) c*x=0 ↔
      x∈Ideal.span {Ideal.Quotient.mk (Ideal.span {c*d}) d} := by
  let I : Ideal R := Ideal.span {c*d}
  let π := Ideal.Quotient.mk I
  change π c*x=0 ↔ x∈Ideal.span {π d}
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  change π c*π a=0 ↔ π a∈Ideal.span {π d}
  have hcd : π c*π d=0 := by
    rw [←map_mul]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_singleton _))
  constructor
  · intro h
    rw [←map_mul] at h
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).1 h)
    have ha : a=d*b := mul_left_cancel₀ hc (by simpa [mul_assoc] using hb)
    exact Ideal.mem_span_singleton.mpr ⟨π b,by rw [ha,map_mul]⟩
  · intro h
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp h
    rw [hb,←mul_assoc,hcd,zero_mul]

theorem swapped_product_annihilator (c d : R) (hd : d≠0)
    (x : R ⧸ Ideal.span {c*d}) :
    Ideal.Quotient.mk (Ideal.span {c*d}) d*x=0 ↔
      x∈Ideal.span {Ideal.Quotient.mk (Ideal.span {c*d}) c} := by
  revert x
  rw [mul_comm c d]
  exact product_conductor_annihilator d c hd

theorem odd_conductor_conditions (c d : R) (hc : c≠0) (hd : d≠0) (h₁ : d∣c) (h₂ : c∣d^2) :
    let π := Ideal.Quotient.mk (Ideal.span {c*d})
    (π c)^2=0 ∧ (π d)^3=0 ∧
    (∀ x, π c*x=0 ↔ x∈Ideal.span {π d}) ∧
    (∀ x, π d*x=0 → x∈Ideal.span {π d}) := by
  dsimp only
  let π := Ideal.Quotient.mk (Ideal.span {c*d})
  have hcd : π c*π d=0 := by
    rw [←map_mul]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨u,hu⟩ := h₁
  obtain ⟨v,hv⟩ := h₂
  have h₁' : π c=π d*π u := by rw [←map_mul,←hu]
  have h₂' : (π d)^2=π c*π v := by rw [←map_pow,←map_mul,←hv]
  refine ⟨?_,?_,product_conductor_annihilator c d hc,?_⟩
  · change (π c)^2=0
    calc
      _ = π c*(π d*π u) := by rw [←h₁',pow_two]
      _ = 0 := by rw [←mul_assoc,hcd,zero_mul]
  · change (π d)^3=0
    rw [pow_succ,h₂',mul_right_comm,hcd,zero_mul]
  · intro x hx
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp ((swapped_product_annihilator c d hd x).1 hx)
    exact Ideal.mem_span_singleton.mpr ⟨π u*b,by change x=π d*(π u*b);rw [←mul_assoc,←h₁',←hb]⟩

#print axioms odd_conductor_conditions
end WaringLinear

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-! # The self-annihilator of a half-conductor in a principal quotient -/
namespace WaringLinear
variable {R : Type*} [CommRing R] [IsDomain R]

/-- In R/(d²), the annihilator of d is precisely its principal ideal. This
applies with d a power of a uniformizer at every finite place of a number field. -/
theorem middle_conductor_annihilator (d : R) (hd : d≠0)
    (x : R ⧸ Ideal.span {d^2}) :
    Ideal.Quotient.mk (Ideal.span {d^2}) d * x=0 ↔
      x∈Ideal.span {Ideal.Quotient.mk (Ideal.span {d^2}) d} := by
  let I : Ideal R := Ideal.span {d^2}
  let π := Ideal.Quotient.mk I
  change π d*x=0 ↔ x∈Ideal.span {π d}
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  change π d*π a=0 ↔ π a∈Ideal.span {π d}
  have hc : π d ^ 2=0 := by
    rw [←map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span (Set.mem_singleton _))
  constructor
  · intro h
    rw [←map_mul] at h
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).1 h)
    have ha : a=d*b := mul_left_cancel₀ hd (by simpa [pow_two,mul_assoc] using hb)
    exact Ideal.mem_span_singleton.mpr ⟨π b,by rw [ha,map_mul]⟩
  · intro h
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp h
    rw [hb,←mul_assoc,←pow_two,hc,zero_mul]

#print axioms middle_conductor_annihilator
end WaringLinear

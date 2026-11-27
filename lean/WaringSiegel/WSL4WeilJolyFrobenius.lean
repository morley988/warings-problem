import WaringSiegel.WSL4WeilHensel
import WaringSiegel.WSL4ArchLocalTuples
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.CharP.Frobenius

noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 800000

/-- Eligibility forces a kth-power residue modulo k itself, also in ramified rings. -/
theorem eligible_eq_power_add_prime_mul
    {A : Type*} [CommRing A] [IsLocalRing A]
    (k : ℕ) [Fact k.Prime] [CharP (ResidueField A) k]
    (a : A) (ha : a∈AddSubgroup.closure (Set.range (fun x : A => x^k))) :
    ∃ x z : A, a=x^k+(k:A)*z := by
  have hnon : (k:A)∈nonunits A := by
    intro hu
    have hru := hu.map (residue A)
    have hr0 : residue A (k:A)=0 := by
      rw [map_natCast,CharP.cast_eq_zero]
    rw [hr0] at hru
    exact not_isUnit_zero hru
  let I : Ideal A := Ideal.span {(k:A)}
  let Q := A ⧸ I
  let q : A →+* Q := Ideal.Quotient.mk I
  letI : CharP Q k := CharP.quotient A k hnon
  have hq : q a∈AddSubgroup.closure (Set.range (fun x : Q => x^k)) :=
    WSL4.map_mem_power_closure k q ha
  have hs : AddSubgroup.closure (Set.range (fun x : Q => x^k)) ≤
      (frobenius Q k).range.toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    rintro b ⟨x,rfl⟩
    exact ⟨x,rfl⟩
  obtain ⟨x,hx⟩ := hs hq
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : q (a-x^k)=0 := by
    change (Ideal.Quotient.mk I x)^k=q a at hx
    rw [map_sub,map_pow,hx,sub_self]
  have hd : (k:A)∣a-x^k := Ideal.mem_span_singleton.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp he)
  obtain ⟨z,hz⟩ := hd
  exact ⟨x,z,by rw [← hz]; ring⟩
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.eligible_eq_power_add_prime_mul

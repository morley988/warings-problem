import WaringLinear.CubicDyadicSpan
import WaringLinear.CubicLocalLifting
import WaringSiegel.NumberFieldTargets
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic

/-! Simultaneous integral cube representatives at the conductor six. -/
open scoped NumberField
namespace WaringLinear.CubicResidueSix

private theorem map_cubeClosure {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x : R} (hx : x ∈ AddSubgroup.closure (Set.range fun z : R => z^3)) :
    f x ∈ AddSubgroup.closure (Set.range fun z : S => z^3) := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨t,rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨f t,(map_pow f t 3).symm⟩
  | zero => simp
  | add a b _ _ ha hb => rw [f.map_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [f.map_neg]; exact AddSubgroup.neg_mem _ ha

variable {K : Type*} [Field K] [NumberField K]

set_option synthInstance.maxHeartbeats 100000 in
theorem residue_three_cubes {ν : 𝓞 K} (hν : WaringSiegel.Eligible 3 ν) :
    ∃ a b c : 𝓞 K, (6 : 𝓞 K) ∣ ν-a^3-b^3-c^3 := by
  classical
  let I : Ideal (𝓞 K) := Ideal.span {(2 : 𝓞 K)}
  let q := Ideal.Quotient.mk I
  let A := (𝓞 K) ⧸ I
  have htwo : ∃ a b c : 𝓞 K, q ν=q (a^3+b^3+c^3) := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact ⟨0,0,0,h.elim _ _⟩
    · letI : Nontrivial A := h
      letI : Finite A := Ideal.finiteQuotientOfFreeOfNeBot I (by
        change Ideal.span {(2 : 𝓞 K)} ≠ ⊥
        rw [ne_eq,Ideal.span_singleton_eq_bot]
        norm_num)
      letI : CharP A 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by
        change (2 : (𝓞 K) ⧸ I) = 0
        rw [← map_ofNat q]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))
      have hq := map_cubeClosure q hν
      obtain ⟨z,x,hzx⟩ := CubicDyadicSpan.three_cubes_finite (q ν : A) hq
      obtain ⟨z',rfl⟩ := Ideal.Quotient.mk_surjective (I:=I) z
      obtain ⟨x',rfl⟩ := Ideal.Quotient.mk_surjective (I:=I) x
      exact ⟨z',x',x'+1,by simpa only [q,map_add,map_pow,map_one] using hzx⟩
  obtain ⟨x,y,z,hxyz⟩ := htwo
  have hd : q (ν-(x^3+y^3+z^3)) = 0 := by rw [q.map_sub ν _,hxyz,sub_self]
  obtain ⟨v,hv⟩ := Ideal.mem_span_singleton.mp
    (show ν-(x^3+y^3+z^3) ∈ I from Ideal.Quotient.eq_zero_iff_mem.mp hd)
  obtain ⟨d,w,hw⟩ := CubicLocalLifting.cube_mod_three_of_mem_span hν
  refine ⟨3*x-2*d,3*y,3*z, v-w-4*(x^3+y^3+z^3)+9*x^2*d-6*x*d^2+d^3, ?_⟩
  linear_combination 3*hv - 2*hw

/-- Rounding three roots independently in their fixed classes keeps
the residual in the same principal ideal. -/
theorem preserve_residue {R : Type*} [CommRing R] {a b c ν : R}
    (ha : (6:R) ∣ ν-a^3-b^3-c^3) (x y z : R) :
    (6:R) ∣ ν-(a+6*x)^3-(b+6*y)^3-(c+6*z)^3 := by
  obtain ⟨e,he⟩ := ha
  refine ⟨e - 3*x*a^2 - 18*a*x^2 - 36*x^3
            - 3*y*b^2 - 18*b*y^2 - 36*y^3
            - 3*z*c^2 - 18*c*z^2 - 36*z^3,?_⟩
  linear_combination he

#print axioms residue_three_cubes
end WaringLinear.CubicResidueSix

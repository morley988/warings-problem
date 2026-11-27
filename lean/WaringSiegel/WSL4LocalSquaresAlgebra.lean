import WaringSiegel.CubicAlgebra
import WaringSiegel.NumberFieldTargets
import Mathlib.FieldTheory.Finite.Basic

/-! # Exact algebra behind the local five-square construction -/
noncomputable section
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {R : Type*} [CommRing R]

def squareSpan (R : Type*) [CommRing R] : AddSubgroup R :=
  AddSubgroup.closure (Set.range (fun x:R => x^2))

def squareModTwo (R : Type*) [CommRing R] : AddSubgroup R where
  carrier := {a | ∃b c:R,a=b^2+2*c}
  zero_mem' := ⟨0,0,by ring⟩
  add_mem' := by
    rintro a d ⟨b,c,rfl⟩ ⟨e,f,rfl⟩
    exact ⟨b+e,c+f-b*e,by ring⟩
  neg_mem' := by
    rintro a ⟨b,c,rfl⟩
    exact ⟨b,-c-b^2,by ring⟩

theorem squareSpan_le_squareModTwo : squareSpan R≤squareModTwo R := by
  apply (AddSubgroup.closure_le _).mpr
  rintro a ⟨b,rfl⟩
  exact ⟨b,0,by ring⟩

theorem map_mem_squareSpan {S : Type*} [CommRing S] (f:R→+*S)
    {a:R} (ha:a∈squareSpan R) : f a∈squareSpan S := by
  have hh : squareSpan R≤(squareSpan S).comap f.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).mpr
    rintro a ⟨b,rfl⟩
    change f (b^2)∈squareSpan S
    rw [map_pow]
    exact AddSubgroup.subset_closure ⟨f b,rfl⟩
  exact hh ha

theorem dyadic_five_square_identity (a x c r t : R)
    (hr:r^2= -7) (hct:c^2=c) (he:2*(r*x+3*c)*t=a-(x^2+2*c)) :
    (x+t*r)^2+(c+2*t)^2+(c+t)^2+t^2+t^2=a := by
  calc
    _ = x^2+2*c^2+2*(r*x+3*c)*t+t^2*(r^2+7) := by ring
    _ = a := by rw [hr,hct,he]; ring

theorem three_squares_of_neg_one {F : Type*} [Field F]
    (h2:(2:F)≠0) (b c a:F) (hbc:b^2+c^2= -1) :
    ∃x y z:F,x^2+y^2+z^2=a := by
  refine ⟨(a+1)/2,b*((a-1)/2),c*((a-1)/2),?_⟩
  calc
    _ = ((a+1)/2)^2+(b^2+c^2)*((a-1)/2)^2 := by ring
    _ = a := by rw [hbc]; field_simp; ring

theorem finiteField_three_squares {F : Type*} [Field F] [Finite F]
    (h2:(2:F)≠0) (a:F) : ∃x y z:F,x^2+y^2+z^2=a := by
  letI : NeZero (ringChar F) := ⟨CharP.ringChar_ne_zero_of_finite F⟩
  obtain ⟨b,c,hbc⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  exact three_squares_of_neg_one h2 (b:F) (c:F) a (by simpa using hbc)

theorem power_tuple_unit_pad {k s : ℕ} (hk:0<k) {a:R}
    (h:∃x:Fin s→R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i)) :
    ∃x:Fin (s+1)→R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  obtain ⟨x,hx,i,hi⟩ := h
  refine ⟨Fin.cons 0 x,?_,i.succ,?_⟩
  · simpa [Fin.sum_univ_succ,zero_pow hk.ne'] using hx
  · simpa using hi

#print axioms squareSpan_le_squareModTwo
#print axioms dyadic_five_square_identity
#print axioms finiteField_three_squares
end WaringSiegel.WSL4Local

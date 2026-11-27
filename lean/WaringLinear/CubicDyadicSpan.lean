import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Ring

/-! # Three cubes in a finite local ring of characteristic two

The image of the Artin--Schreier map has additive index two. Each
element of the additive span of cubes can therefore be represented by
three cubes, two of whose roots differ by one. This applies to the
local factors of the ring of integers modulo 2, including at ramified
dyadic places.
-/

namespace WaringLinear.CubicDyadicSpan

variable (A : Type*) [CommRing A] [CharP A 2] [IsLocalRing A] [Finite A] [Nontrivial A]

private def artinSchreier : A →+ A :=
  (frobenius A 2).toAddMonoidHom - AddMonoidHom.id A

omit [IsLocalRing A] [Finite A] [Nontrivial A] in
private theorem artinSchreier_apply (x : A) :
    artinSchreier A x = x^2 - x := rfl

omit [Finite A] in
private theorem ker_card : Nat.card (artinSchreier A).ker = 2 := by
  let e : (artinSchreier A).ker := ⟨1, by change (1:A)^2-1=0; simp⟩
  apply (Nat.card_eq_two_iff' (0 : (artinSchreier A).ker)).2
  refine ⟨e, fun h => one_ne_zero (congrArg Subtype.val h), ?_⟩
  intro x hx
  have hsq : (x:A)^2 = x := sub_eq_zero.mp x.property
  have hprod : (x:A) * (1 - x) = 0 := by rw [mul_sub, mul_one, ← pow_two, hsq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (x:A) with hu | hu
  · apply Subtype.ext
    change (x:A)=1
    symm
    apply sub_eq_zero.mp
    exact hu.mul_left_cancel (by simpa using hprod)
  · exfalso
    apply hx
    apply Subtype.ext
    exact hu.mul_right_cancel (by simpa using hprod)

private theorem range_index : (artinSchreier A).range.index = 2 := by
  let f := artinSchreier A
  have him : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hker := f.ker.card_mul_index
  rw [ker_card,him] at hker
  have hrange := f.range.index_mul_card
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hrange.trans hker.symm)

/-- Each eligible residue in a finite local ring of characteristic
two is the sum of three cubes. The two final roots have difference one. -/
theorem three_cubes (a : A)
    (ha : a ∈ AddSubgroup.closure (Set.range (fun t : A => t^3))) :
    ∃ z x : A, a = z^3 + x^3 + (x+1)^3 := by
  classical
  let H := (artinSchreier A).range
  have hrepr (z : A) (hz : a + 1 + z^3 ∈ H) :
      ∃ x : A, a = z^3 + x^3 + (x+1)^3 := by
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    rw [artinSchreier_apply,CharTwo.sub_eq_add] at hx
    have hid : z^3 + x^3 + (x+1)^3 = z^3 + 1 + (x^2+x) := by
      rw [pow_succ (x+1) 2, CharTwo.add_sq, one_pow]
      calc
        _ = (x^3+x^3)+(z^3+1+(x^2+x)) := by ring
        _ = _ := by rw [CharTwo.add_self_eq_zero,zero_add]
    rw [hid,hx]
    calc
      a = a + ((1:A)+1) + (z^3+z^3) := by simp only [CharTwo.add_self_eq_zero,add_zero]
      _ = _ := by ac_rfl
  by_cases hc : a+1 ∈ H
  · obtain ⟨x,hx⟩ := hrepr 0 (by simpa using hc)
    exact ⟨0,x,hx⟩
  · have hspan : a+1 ∈ AddSubgroup.closure (Set.range (fun t : A => t^3)) :=
      AddSubgroup.add_mem _ ha (AddSubgroup.subset_closure ⟨1,one_pow 3⟩)
    have hout : ∃ z:A, z^3 ∉ H := by
      by_contra! hh
      have hle : AddSubgroup.closure (Set.range (fun t : A => t^3)) ≤ H :=
        (AddSubgroup.closure_le H).2 (by rintro _ ⟨t,rfl⟩; exact hh t)
      exact hc (hle hspan)
    obtain ⟨z,hz⟩ := hout
    have hadd : a+1+z^3 ∈ H :=
      (H.add_mem_iff_of_index_two (range_index A)).2 ⟨fun h => (hc h).elim,fun h => (hz h).elim⟩
    obtain ⟨x,hx⟩ := hrepr z hadd
    exact ⟨z,x,hx⟩

section Global

variable {B : Type*} [CommRing B] [CharP B 2]

private theorem nilpotent_artinSchreier {a : B} (ha : IsNilpotent a) :
    ∃ y : B, y^2+y=a := by
  obtain ⟨m,hm⟩ := ha
  have hstep (n:ℕ) : ∃ y:B, y^2+y=a^(2^n)+a := by
    induction n with
    | zero => exact ⟨0,by simp [CharTwo.add_self_eq_zero]⟩
    | succ n ih =>
      obtain ⟨y,hy⟩ := ih
      refine ⟨y+a^(2^n),?_⟩
      rw [CharTwo.add_sq,pow_succ (2:ℕ) n, pow_mul]
      calc
        _ = (a^(2^n))^2 + (y^2+y) + a^(2^n) := by ac_rfl
        _ = (a^(2^n))^2 + (a^(2^n)+a^(2^n)) + a := by rw [hy]; ac_rfl
        _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]
  obtain ⟨y,hy⟩ := hstep m
  refine ⟨y,?_⟩
  have hm' : a^(2^m)=0 := pow_eq_zero_of_le (Nat.le_of_lt (Nat.lt_two_pow_self)) hm
  simpa [hm'] using hy

omit [CharP B 2] in
private theorem cube_map_mem {C : Type*} [CommRing C] (f : B →+* C) {a : B}
    (ha : a ∈ AddSubgroup.closure (Set.range (fun t : B => t^3))) :
    f a ∈ AddSubgroup.closure (Set.range (fun t : C => t^3)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b,rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨f b,(map_pow f b 3).symm⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using AddSubgroup.add_mem _ hx hy
  | neg x _ hx => simpa using AddSubgroup.neg_mem _ hx

/-- The same three-cube decomposition holds in every finite
commutative ring of characteristic two, including nonreduced rings. -/
theorem three_cubes_finite [Finite B] (a : B)
    (ha : a ∈ AddSubgroup.closure (Set.range (fun t : B => t^3))) :
    ∃ z x : B, a = z^3+x^3+(x+1)^3 := by
  classical
  letI : IsArtinianRing B := isArtinian_of_finite
  let e := IsArtinianRing.quotNilradicalEquivPi B
  let f := e.toRingHom.comp (Ideal.Quotient.mk (nilradical B))
  have hsurj : Function.Surjective f := e.surjective.comp Ideal.Quotient.mk_surjective
  have hlocal (i:MaximalSpectrum B) :
      ∃ z x:B ⧸ i.asIdeal, f a i=z^3+x^3+(x+1)^3 := by
    letI : Finite (B ⧸ i.asIdeal) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I:=i.asIdeal))
    letI : Field (B ⧸ i.asIdeal) := Ideal.Quotient.field i.asIdeal
    letI : CharP (B ⧸ i.asIdeal) 2 :=
      CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
        (by simpa using congrArg (Ideal.Quotient.mk i.asIdeal) (CharTwo.two_eq_zero (R:=B)))
    exact three_cubes _ _ (cube_map_mem ((Pi.evalRingHom _ i).comp f) ha)
  choose z x hz using hlocal
  obtain ⟨z',rfl⟩ := hsurj z
  obtain ⟨x',rfl⟩ := hsurj x
  let d := a-(z'^3+x'^3+(x'+1)^3)
  have hdf : f d=0 := by ext i; simpa [d] using sub_eq_zero.mpr (hz i)
  have hd : IsNilpotent d := mem_nilradical.mp (Ideal.Quotient.eq_zero_iff_mem.mp
    (e.injective (by simpa [f] using hdf)))
  obtain ⟨y,hy⟩ := nilpotent_artinSchreier hd
  refine ⟨z',x'+y,?_⟩
  have hpoly (x y:B) : (x+y)^3+(x+y+1)^3 = x^3+(x+1)^3+(y^2+y) := by
    have h (x:B) : x^3+(x+1)^3=x^2+x+1 := by
      rw [pow_succ (x+1) 2,CharTwo.add_sq,one_pow]
      calc
        _ = (x^3+x^3)+(x^2+x+1) := by ring
        _ = _ := by rw [CharTwo.add_self_eq_zero,zero_add]
    rw [h,h,CharTwo.add_sq]; ring
  rw [add_assoc,hpoly,hy]
  dsimp [d]
  abel

end Global

#print axioms three_cubes_finite
#print axioms three_cubes

end WaringLinear.CubicDyadicSpan

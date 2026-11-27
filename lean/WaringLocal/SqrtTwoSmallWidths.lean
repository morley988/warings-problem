import WaringLocal.SqrtTwoWidths

/-! The exceptional exponents four and eight have exact ordinary and
primitive widths seven and seventeen. -/
noncomputable section
namespace WaringSiegel.SqrtTwo
open WaringLocal.FinitePrecision
open scoped Padic

private abbrev Res (n:Nat) := QuadraticAlgebra (ZMod (2^n)) 2 0

private def reduction (n : Nat) : A →+* Res n where
  toFun x := ⟨PadicInt.toZModPow n x.re,PadicInt.toZModPow n x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp
  map_mul' x y := by
    have h : (PadicInt.toZModPow n) (2:R)=(2:ZMod (2^n)) := map_ofNat _ 2
    ext <;> simp [h]

private def isImage {n : Nat} (D : Nat) (x : Res n) : Prop :=
  x.re=1 ∨ (x.re=D ∧ x.im=0) ∨ (x.re=0 ∧ x.im=0)

private instance {n D : Nat} {x : Res n} : Decidable (isImage D x) := by unfold isImage; infer_instance

private theorem images_four : ∀ u v : ZMod 16, isImage 4 ((⟨u,v⟩:Res 4)^4) := by decide +kernel
private theorem images_eight : ∀ u v : ZMod 32, isImage 16 ((⟨u,v⟩:Res 5)^8) := by decide +kernel

private theorem root_counts (n D k : Nat) (hall : ∀ x : Res n, isImage D (x^k)) (xs : List A) :
    ∃ u v : Nat, u+v≤xs.length ∧
      (reduction n (powerSum k xs)).re=(u+D*v:Nat) ∧
      (u=0 → (reduction n (powerSum k xs)).im=0) := by
  induction xs with
  | nil => exact ⟨0,0,by simp,by simp [powerSum],by simp [powerSum]⟩
  | cons x l ih =>
    obtain ⟨u,v,h,hr,hi⟩ := ih
    have hx := hall (reduction n x)
    rw [←map_pow] at hx
    change ∃ u' v' : Nat, u'+v'≤l.length+1 ∧
      (reduction n (x^k+powerSum k l)).re=↑(u'+D*v') ∧
      (u'=0 → (reduction n (x^k+powerSum k l)).im=0)
    simp only [map_add,QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,hr]
    rcases hx with h1 | ⟨h2,h2'⟩ | ⟨h0,h0'⟩
    · exact ⟨u+1,v,by omega,by rw [h1]; push_cast; ring,by omega⟩
    · exact ⟨u,v+1,by omega,by rw [h2]; push_cast; ring,fun h => by rw [h2',hi h,zero_add]⟩
    · exact ⟨u,v,by omega,by rw [h0,zero_add],fun h => by rw [h0',hi h,zero_add]⟩

private theorem test_eligible (a : Nat) :
    (⟨0,(2:R)^(a+2)⟩:A)∈Eligible (2^(a+2)) := by
  obtain ⟨z,_,hz⟩ := unit_power_coset a 1 (by decide) 0 1
  simp only [Nat.mul_one,mul_zero,add_zero,mul_one] at hz
  have ht : (⟨1,(2:R)^(a+2)⟩:A)∈Eligible (2^(a+2)) :=
    AddSubgroup.subset_closure ⟨z,hz⟩
  have h1 : (1:A)∈Eligible (2^(a+2)) := AddSubgroup.subset_closure ⟨1,one_pow _⟩
  convert (Eligible (2^(a+2))).sub_mem ht h1 using 1
  ext <;> simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]

private theorem small_upper (a S D N : Nat) (hd : D=2^(2^(a+1))) (hN : N=2^(a+4))
    (splitter : ∀ l : Nat, 0<l → l≤N →
      ∃ u v:Nat, 1+u+D*v=l ∧ 1+u+v≤S)
    (z : A) (hz : z∈Eligible (2^(a+2))) : Primitive (2^(a+2)) S z := by
  obtain ⟨t,ht⟩ := eligible_im_div a 1 (by decide) z (by simpa using hz)
  obtain ⟨l,hl,hmax,s,hs⟩ := positive_rep (a+4) z.re
  obtain ⟨u,v,he,hw⟩ := splitter l hl (hN ▸ hmax)
  obtain ⟨xs,hxs,hval,hunit⟩ := assemble_units_nonunits a 1 u v (by decide) s t
  simp only [Nat.mul_one] at hxs hval hunit
  refine ⟨xs,hxs.trans hw,hval.trans ?_,hunit⟩
  apply QuadraticAlgebra.ext
  · have hscale : (2:R)^(a+4)=4*2^(a+2) := by
      rw [show a+4=a+2+2 by omega,pow_add]; ring
    rw [hd] at he
    have he' : 1+(u:R)+(2:R)^(2^(a+1))*v=l := by exact_mod_cast he
    change 1+4*(2:R)^(a+2)*s+u+v*2^(2^(a+1))=z.re
    rw [hs,hscale]
    linear_combination he'
  · exact ht.symm

/-- All eligible targets are attained with a unit in these widths.
The indicated concrete targets require all those slots ordinarily. -/
theorem exact_four :
    (∀ z : A, z∈Eligible 4 → Primitive 4 7 z) ∧
    (⟨0,4⟩:A)∈Eligible 4 ∧ ¬Ordinary 4 6 (⟨0,4⟩:A) := by
  refine ⟨small_upper 0 7 4 16 rfl rfl ?_,test_eligible 0,?_⟩
  · intro l hl hh
    exact ⟨(l-1)%4,(l-1)/4,by omega,by omega⟩
  · rintro ⟨xs,hn,he⟩
    obtain ⟨u,v,hu,hr,hi⟩ := root_counts 4 4 4 (fun x => images_four x.re x.im) xs
    rw [he] at hr hi
    have hq : (0:ZMod 16)=↑(u+4*v) := by simpa [reduction] using hr
    have hu' : u≠0 := by intro h; have hi' := hi h; change PadicInt.toZModPow 4 (4:R)=0 at hi'; rw [map_ofNat] at hi'; exact (by decide : (4:ZMod 16)≠0) hi'
    have hdiv := (ZMod.natCast_eq_zero_iff _ 16).mp hq.symm
    omega

theorem exact_eight :
    (∀ z : A, z∈Eligible 8 → Primitive 8 17 z) ∧
    (⟨0,8⟩:A)∈Eligible 8 ∧ ¬Ordinary 8 16 (⟨0,8⟩:A) := by
  refine ⟨small_upper 1 17 16 32 rfl rfl ?_,test_eligible 1,?_⟩
  · intro l hl hh
    exact ⟨(l-1)%16,(l-1)/16,by omega,by omega⟩
  · rintro ⟨xs,hn,he⟩
    obtain ⟨u,v,hu,hr,hi⟩ := root_counts 5 16 8 (fun x => images_eight x.re x.im) xs
    rw [he] at hr hi
    have hq : (0:ZMod 32)=↑(u+16*v) := by simpa [reduction] using hr
    have hu' : u≠0 := by intro h; have hi' := hi h; change PadicInt.toZModPow 5 (8:R)=0 at hi'; rw [map_ofNat] at hi'; exact (by decide : (8:ZMod 32)≠0) hi'
    have hdiv := (ZMod.natCast_eq_zero_iff _ 32).mp hq.symm
    omega

#print axioms exact_four
#print axioms exact_eight
end WaringSiegel.SqrtTwo

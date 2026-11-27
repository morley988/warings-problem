import WaringSiegel.WSL4MajorRamanujamMonogenicLift

/-! # The localized actual monogenic coefficient image -/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4
variable {B A : Type*} [CommRing B] [CommRing A]

def relativePrimeCoefficientRing (p : ℕ) (f : B →+* A) : Subring A where
  carrier := {c | ∃a b : B,IsCoprime b (p:B) ∧ f b*c=f a}
  zero_mem' := ⟨0,1,isCoprime_one_left,by simp⟩
  one_mem' := ⟨1,1,isCoprime_one_left,by simp⟩
  add_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*d+c*b,b*d,hb.mul_left hd,?_⟩
    simp only [map_add,map_mul]
    calc
      f b*f d*(x+y)=f d*(f b*x)+f b*(f d*y) := by ring
      _=f a*f d+f c*f b := by rw [hx,hy]; ring
  neg_mem' := by
    rintro x ⟨a,b,hb,hx⟩
    exact ⟨-a,b,hb,by simpa only [map_neg,mul_neg] using congrArg Neg.neg hx⟩
  mul_mem' := by
    rintro x y ⟨a,b,hb,hx⟩ ⟨c,d,hd,hy⟩
    refine ⟨a*c,b*d,hb.mul_left hd,?_⟩
    simp only [map_mul]
    calc
      f b*f d*(x*y)=(f b*x)*(f d*y) := by ring
      _=f a*f c := by rw [hx,hy]

theorem mem_relativePrimeCoefficientRing_map (p : ℕ) (f : B →+* A) (a : B) :
    f a∈relativePrimeCoefficientRing p f :=
  ⟨a,1,isCoprime_one_left,by simp⟩

theorem relativePrimeCoefficientRing_inverse_mem (p : ℕ) (f : B →+* A)
    (b : B) (hb : IsCoprime b (p:B)) (u : Aˣ) (hu : (u:A)=f b) :
    ((u⁻¹:Aˣ):A)∈relativePrimeCoefficientRing p f := by
  refine ⟨1,b,hb,?_⟩
  rw [← hu]
  simp

theorem relativePrimeCoefficient_map_isUnit [IsLocalRing A]
    (p : ℕ) [CharP (ResidueField A) p] (f : B →+* A)
    (b : B) (hb : IsCoprime b (p:B)) : IsUnit (f b) := by
  have he := hb.map ((residue A).comp f)
  simp only [RingHom.comp_apply,map_natCast,CharP.cast_eq_zero,isCoprime_zero_right] at he
  exact (residue_ne_zero_iff_isUnit _).mp he.ne_zero

theorem monogenic_coprime_of_residue_ne_zero
    {L : Type*} [Field L] (p : ℕ) (rho : B →+* L)
    (hsurj : Function.Surjective rho)
    (hker : ∀ b : B,rho b=0 ↔ (p:B) ∣ b)
    (b : B) (hb : rho b ≠ 0) : IsCoprime b (p:B) := by
  obtain ⟨c,hc⟩ := hsurj (rho b)⁻¹
  have hz : rho (b*c-1)=0 := by
    rw [map_sub,map_mul,map_one,hc,mul_inv_cancel₀ hb,sub_self]
  obtain ⟨d,hd⟩ := (hker _).mp hz
  refine ⟨c,-d,?_⟩
  linear_combination hd

theorem relativePrimeCoefficientRing_approx (p t : ℕ) (f : B →+* A) {c : A}
    (hc : c∈relativePrimeCoefficientRing p f) :
    ∃ a : B,∃ b : A,c=f a+(p:A)^t*b := by
  obtain ⟨a,b,hb,hc⟩ := hc
  obtain ⟨u,v,hbez⟩ := hb.pow_right (n:=t)
  have hbezA := congrArg f hbez
  simp only [map_add,map_mul,map_pow,map_natCast,map_one] at hbezA
  refine ⟨u*a,f v*c,?_⟩
  rw [map_mul]
  linear_combination -c*hbezA+(f u)*hc

#print axioms relativePrimeCoefficientRing_inverse_mem
#print axioms relativePrimeCoefficient_map_isUnit
#print axioms monogenic_coprime_of_residue_ne_zero
#print axioms relativePrimeCoefficientRing_approx
end WaringSiegel.WSL4

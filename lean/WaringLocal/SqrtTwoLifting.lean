import WaringSiegel.SqrtTwoPowerImages
import WaringLocal.AdicPowerBalls

/-! A single unit power fills each of its full dyadic congruence
classes in ℤ₂[√2]. The lifting uses adic completeness and holds for
all odd cofactors of the power of two. -/
noncomputable section
namespace WaringSiegel.SqrtTwo
open scoped Padic

private abbrev I : Ideal A := Ideal.span {(2:A)}
private abbrev J : Ideal R := Ideal.span {(2:R)}

private instance baseComplete : IsAdicComplete J R := by
  have he : IsLocalRing.maximalIdeal R=J := by
    convert PadicInt.maximalIdeal_eq_span_p (p:=2) using 1
  rw [←he]
  infer_instance

private instance orderComplete : IsAdicComplete I A := by
  have he := AdicPowerBalls.quadratic_complete (2:R) (2:R) (0:R)
  simpa [I] using he

theorem dvd_of_red_zero (n : Nat) (x : R) (h : PadicInt.toZModPow n x=0) :
    (2:R)^n ∣ x := by
  have hk : x ∈ RingHom.ker (PadicInt.toZModPow n : R →+* ZMod (2^n)) := h
  rw [PadicInt.ker_toZModPow,Ideal.mem_span_singleton] at hk
  exact hk

private abbrev r₂ : R →+* ZMod 2 := PadicInt.toZModPow 1
private abbrev r₄ : R →+* ZMod 4 := PadicInt.toZModPow 2

private theorem two_zmod : (2:ZMod 2)=0 := by decide

theorem odd_iff_red (x : R) : Odd x ↔ r₂ x=1 := by
  constructor
  · rintro ⟨a,rfl⟩
    simp only [map_add,map_mul,map_ofNat,map_one]
    simp [two_zmod]
  · intro h
    have hz : r₂ (x-1)=0 := by rw [map_sub,h,map_one,sub_self]
    obtain ⟨a,ha⟩ := dvd_of_red_zero 1 (x-1) hz
    exact ⟨a,by rw [pow_one] at ha; linear_combination ha⟩

theorem odd_or_even (x : R) : Odd x ∨ Even x := by
  by_cases h : r₂ x=1
  · exact Or.inl ((odd_iff_red x).mpr h)
  · have h0 : r₂ x=0 := by
      have hd : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
      exact (hd _).resolve_right h
    obtain ⟨a,ha⟩ := dvd_of_red_zero 1 x h0
    exact Or.inr ⟨a,by rw [pow_one] at ha; linear_combination ha⟩

private theorem base_unit_of_odd (x : R) (h : Odd x) : IsUnit x := by
  by_contra hn
  obtain ⟨a,ha⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp (PadicInt.not_isUnit_iff.mp hn)
  have he := (odd_iff_red x).mp h
  rw [ha,map_mul,map_natCast] at he
  simp [two_zmod] at he

def residue : A →+* ZMod 2 where
  toFun x := r₂ x.re
  map_one' := map_one _
  map_zero' := map_zero _
  map_add' x y := map_add _ _ _
  map_mul' x y := by
    simp only [QuadraticAlgebra.re_mul,map_add,map_mul,map_ofNat]
    simp [two_zmod]

theorem unit_iff_odd (x : A) : IsUnit x ↔ Odd x.re := by
  constructor
  · intro hx
    have h := (hx.map residue).ne_zero
    apply (odd_iff_red x.re).mpr
    have hd : ∀ z : ZMod 2, z=0 ∨ z=1 := by decide
    exact (hd _).resolve_left h
  · intro hx
    let N := x.re^2-2*x.im^2
    have hodd : Odd N := by
      apply (odd_iff_red _).mpr
      dsimp [N]
      simp only [map_sub,map_pow,map_mul,map_ofNat,(odd_iff_red x.re).mp hx]
      simp [two_zmod]
    have hu := (base_unit_of_odd _ hodd).map (algebraMap R A)
    have he : x*(⟨x.re,-x.im⟩:A)=(algebraMap R A) N := by
      ext <;> simp [QuadraticAlgebra.algebraMap_eq,N] <;> ring
    exact isUnit_of_mul_isUnit_left (he ▸ hu)

private theorem m_unit (m : Nat) (hm : Odd m) : IsUnit (m:A) := by
  obtain ⟨t,ht⟩ := hm
  have h : Odd (m:R) := ⟨(t:R),by exact_mod_cast ht⟩
  simpa using (base_unit_of_odd _ h).map (algebraMap R A)

theorem principal_power_ball (a m : Nat) (hm : Odd m) (b : A) :
    ∃ x, (1+4*x)^(2^a*m)=1+4*(2:A)^a*b := by
  have h2 : (2:A)∈I := Ideal.subset_span (by simp)
  have h4 : 4*(2:A)^a∈I := by
    rw [show 4*(2:A)^a=2*(2*2^a) by ring]
    exact I.mul_mem_right (2*(2:A)^a) h2
  obtain ⟨u,hu⟩ := AdicPowerBalls.coprime_power_ball I (4*(2:A)^a) h4 m (m_unit m hm) b
  obtain ⟨x,hx⟩ := AdicPowerBalls.two_power_ball I h2 a u
  exact ⟨x,by rw [pow_mul,hx,hu]⟩

/-- Variable unit root x can absorb every change by 4·2^a times an
arbitrary element, preserving its own unit status. -/
theorem unit_adjust (x : A) (hx : IsUnit x) (a m : Nat) (hm : Odd m) (b : A) :
    ∃ y : A, IsUnit y ∧ y^(2^a*m)=x^(2^a*m)+4*(2:A)^a*b := by
  let k := 2^a*m
  obtain ⟨v,hv⟩ := hx
  let z : A := ↑(v^k)⁻¹
  have hz : x^k*z=1 := by rw [←hv]; exact Units.mul_inv (v^k)
  obtain ⟨t,ht⟩ := principal_power_ball a m hm (z*b)
  have htunit : IsUnit (1+4*t) := (unit_iff_odd _).mpr ⟨2*t.re,by
    simp [QuadraticAlgebra.re_one,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
    ring⟩
  refine ⟨x*(1+4*t),(hv ▸ v.isUnit).mul htunit,?_⟩
  rw [mul_pow,ht]
  change x^k*(1+4*2^a*(z*b))=x^k+4*2^a*b
  linear_combination 4*(2:A)^a*b*hz

private theorem mark_mod : ∀ u t : ZMod 4, let m := 2*u+1
    m*(-m*t)*(1+2*(-m*t)^2)=t := by decide +kernel

/-- Every target with scalar coefficient 1 modulo 4d and remaining
coefficient divisible by d is itself the k-th power of a unit, for
d=2^(a+2) and k=d*m with m odd. -/
theorem unit_power_coset (a m : Nat) (hm : Odd m) (s t : R) :
    ∃ y : A, IsUnit y ∧ y^(2^(a+2)*m)=
      (⟨1+4*(2:R)^(a+2)*s,(2:R)^(a+2)*t⟩:A) := by
  let d := 2^(a+2)
  let T := (2:R)^(a+2)
  let β := -(m:R)*t
  let x : A := ⟨1,β⟩
  have hx : Odd x.re := ⟨0,by dsimp [x]; ring⟩
  have hf := dyadic_power_shape x hx a m
  obtain ⟨u,v,hr,hi⟩ := hf
  have hmark : 4 ∣ t-m*β*(1+2*β^2) := by
    obtain ⟨n,hn⟩ := hm
    have hn' : (m:R)=2*(n:R)+1 := by exact_mod_cast hn
    have hz : r₄ (t-m*β*(1+2*β^2))=0 := by
      dsimp [β]
      rw [hn']
      simp only [map_sub,map_mul,map_add,map_pow,map_neg,map_one,map_ofNat]
      exact sub_eq_zero.mpr (mark_mod (r₄ (n:R)) (r₄ t)).symm
    simpa only [show (2:R)^2=4 by norm_num] using dvd_of_red_zero 2 _ hz
  obtain ⟨j,hj⟩ := hmark
  have hz := unit_adjust x ((unit_iff_odd _).mpr hx) (a+2) m hm
    (⟨s-u,j-v⟩:A)
  obtain ⟨y,hy,he⟩ := hz
  refine ⟨y,hy,he.trans ?_⟩
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hr hi
  change (x^(2^(a+2)*m)).re=1+4*T*u at hr
  change (x^(2^(a+2)*m)).im=T*((m:R)*(1*β*(1^2+2*β^2)))+4*T*v at hi
  have hsc : (4*(2:A)^(a+2))=(algebraMap R A) (4*T) := by dsimp [T]; simp
  rw [hsc,QuadraticAlgebra.algebraMap_eq]
  ext <;> simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hr,hi] <;> try dsimp
  · ring
  · linear_combination -(2:R)^(a+2)*hj

#print axioms unit_iff_odd
#print axioms principal_power_ball
#print axioms unit_power_coset
end WaringSiegel.SqrtTwo

import WaringLocal.SqrtTwoWidths

/-! Direct comparison with the base ring ℤ₂ at every exponent in
the ramified counterexample family. -/
noncomputable section
namespace WaringSiegel.SqrtTwo
open WaringLocal.FinitePrecision
open scoped Padic
private abbrev J : Ideal R := Ideal.span {(2:R)}
private instance baseComplete : IsAdicComplete J R := by
  have h : IsLocalRing.maximalIdeal R=J := by
    convert PadicInt.maximalIdeal_eq_span_p (p:=2) using 1
  rw [←h]
  infer_instance

private theorem rational_unit (x : R) (hx : Odd x) : IsUnit x := by
  by_contra hn
  obtain ⟨y,hy⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp (PadicInt.not_isUnit_iff.mp hn)
  have h := (odd_iff_red x).mp hx
  rw [hy,map_mul,map_natCast] at h
  simp [show (2:ZMod 2)=0 by decide] at h

private theorem ball (a m : Nat) (hm : Odd m) (b : R) :
    ∃ y : R, IsUnit y ∧ y^(2^a*m)=1+4*(2:R)^a*b := by
  have h2 : (2:R)∈J := Ideal.subset_span (by simp)
  have h4 : 4*(2:R)^a∈J := by
    rw [show 4*(2:R)^a=2*(2*2^a) by ring]
    exact J.mul_mem_right (2*(2:R)^a) h2
  obtain ⟨q,hq⟩ := hm
  have hm' := rational_unit (m:R) ⟨(q:R),by exact_mod_cast hq⟩
  obtain ⟨u,hu⟩ := AdicPowerBalls.coprime_power_ball J (4*(2:R)^a) h4 m hm' b
  obtain ⟨x,hx⟩ := AdicPowerBalls.two_power_ball J h2 a u
  refine ⟨1+4*x,rational_unit _ ⟨2*x,by ring⟩,?_⟩
  rw [pow_mul,hx,hu]

private theorem map_ordinary {B C : Type*} [CommRing B] [CommRing C] (f : B →+* C)
    {k s : Nat} {z : B} (h : Ordinary k s z) : Ordinary k s (f z) := by
  obtain ⟨xs,hn,he⟩ := h
  refine ⟨xs.map f,by simpa using hn,?_⟩
  have hmap (l : List B) : powerSum k (l.map f)=f (powerSum k l) := by
    induction l with
    | nil => simp [powerSum]
    | cons x l ih =>
      change (f x)^k+powerSum k (l.map f)=f (x^k+powerSum k l)
      rw [map_add,map_pow,ih]
  rw [hmap,he]

/-- The exact same width occurs already over the 2-adic rational
integers. All 2-adic integers are admissible in this statement. -/
theorem rational_exact_large (a m : Nat) (hm : Odd m) (hk : 12≤2^(a+2)*m) :
    (∀ z : R, Primitive (2^(a+2)*m) (2^(a+4)) z) ∧
    (∀ s : Nat, s<2^(a+4) → ¬Ordinary (2^(a+2)*m) s ((2:R)^(a+4))) := by
  constructor
  · intro z
    obtain ⟨l,hl,hn,w,hw⟩ := positive_rep (a+4) z
    let n := l-1
    have hnl : n+1=l := by dsimp [n]; omega
    have heq : (n:R)+1=l := by exact_mod_cast hnl
    obtain ⟨y,hy,hpow⟩ := ball (a+2) m hm w
    refine ⟨y::List.replicate n 1,by simp; omega,?_,y,List.mem_cons_self,hy⟩
    simp only [powerSum,List.map_cons,List.map_replicate,List.sum_cons,List.sum_replicate,
      one_pow,nsmul_eq_mul,mul_one,hpow]
    have hscale : (2:R)^(a+4)=4*2^(a+2) := by
      rw [show a+4=a+2+2 by omega,pow_add]; ring
    rw [hw,hscale]
    linear_combination heq
  · intro s hs h
    have hbig := large_precision a m hm hk
    have hquad := map_ordinary (algebraMap R A) h
    apply (width_lower a m s hbig hs).2
    simpa using hquad

#print axioms rational_exact_large
end WaringSiegel.SqrtTwo

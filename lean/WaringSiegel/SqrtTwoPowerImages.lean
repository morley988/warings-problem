import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-! Exact dyadic power congruences in the quadratic integer algebra
ℤ₂[π], π²=2. Shapes give actual equalities of p-adic coefficients
up to multiples of the displayed modulus. -/
noncomputable section
namespace WaringSiegel.SqrtTwo
open scoped Padic
abbrev R := ℤ_[2]
abbrev A := QuadraticAlgebra R 2 0

def pi : A := ⟨0,1⟩

theorem pi_sq : pi^2=2 := by
  ext <;> simp [pi,pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

/-- Both real coordinates of x−(1+d*j*π) are multiples of 4d. -/
def Shape (x : A) (d : Nat) (j : R) : Prop :=
  ∃ s t : R, x.re=1+4*d*s ∧ x.im=d*j+4*d*t

private theorem quad_mod : ∀ a b : ZMod 16,
    (2*a+1)^4+12*(2*a+1)^2*b^2+4*b^4=1 := by decide +kernel

private theorem lift_zero (n : Nat) (x : R)
    (h : PadicInt.toZModPow n x=0) : (2:R)^n ∣ x := by
  have hk : x ∈ RingHom.ker (PadicInt.toZModPow n : R →+* ZMod (2^n)) := h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  exact hk

theorem fourth_real (x y : R) (hx : Odd x) :
    16 ∣ x^4+12*x^2*y^2+4*y^4-1 := by
  obtain ⟨a,rfl⟩ := hx
  let f := (PadicInt.toZModPow 4 : R →+* ZMod (2^4))
  have h := quad_mod (f a) (f y)
  have he : f ((2*a+1)^4+12*(2*a+1)^2*y^2+4*y^4-1)=0 := by
    simp only [map_sub,map_add,map_mul,map_pow,map_ofNat,map_one]
    exact sub_eq_zero.mpr h
  simpa only [show (2:R)^4=16 by norm_num] using lift_zero 4 _ he

theorem fourth_shape (x : A) (hx : Odd x.re) :
    Shape (x^4) 4 (x.re*x.im*(x.re^2+2*x.im^2)) := by
  obtain ⟨s,hs⟩ := fourth_real x.re x.im hx
  refine ⟨s,0,?_,?_⟩
  all_goals
    rw [show x^4=(x*x)*(x*x) by ring]
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,Nat.cast_ofNat]
  · linear_combination hs
  · ring

theorem square_shape {x : A} {d : Nat} {j : R} (hd : 4∣d)
    (h : Shape x d j) : Shape (x^2) (2*d) j := by
  obtain ⟨q,rfl⟩ := hd
  obtain ⟨s,t,hs,ht⟩ := h
  refine ⟨s+2*(4*q:R)*s^2+q*(j+4*t)^2,t+(4*q:R)*s*(j+4*t),?_,?_⟩
  all_goals
    simp only [pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
      hs,ht,Nat.cast_mul,Nat.cast_ofNat]
    ring

private theorem mul_shape {x y : A} {d : Nat} {i j : R} (hd : 4∣d)
    (hx : Shape x d i) (hy : Shape y d j) : Shape (x*y) d (i+j) := by
  obtain ⟨q,rfl⟩ := hd
  obtain ⟨s,t,hs,ht⟩ := hx
  obtain ⟨w,v,hw,hv⟩ := hy
  refine ⟨s+w+4*(4*q:R)*s*w+2*q*(i+4*t)*(j+4*v),
    t+v+(4*q:R)*(s*(j+4*v)+w*(i+4*t)),?_,?_⟩
  all_goals
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,hw,hv,hs,ht,
      Nat.cast_mul,Nat.cast_ofNat]
    ring

theorem pow_shape {x : A} {d : Nat} {j : R} (hd : 4∣d)
    (h : Shape x d j) (m : Nat) : Shape (x^m) d (m*j) := by
  induction m with
  | zero => exact ⟨0,0,by simp [QuadraticAlgebra.re_one],by simp [QuadraticAlgebra.im_one]⟩
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ,add_mul,one_mul]
    exact mul_shape hd ih h

/-- Explicit power image of every root with odd scalar part for every
multiple of four, including arbitrary odd cofactors. Its first
coefficient is always 1 modulo four times the dyadic part. -/
theorem dyadic_power_shape (x : A) (hx : Odd x.re) (a m : Nat) :
    Shape (x^(2^(a+2)*m)) (2^(a+2))
      (m*(x.re*x.im*(x.re^2+2*x.im^2))) := by
  have hd (j:Nat) : 4∣2^(j+2) := ⟨2^j,by rw [pow_add]; ring⟩
  have h0 : Shape (x^(2^(a+2))) (2^(a+2))
      (x.re*x.im*(x.re^2+2*x.im^2)) := by
    induction a with
    | zero => exact fourth_shape x hx
    | succ n ih =>
      rw [show n+1+2=(n+2)+1 by omega,pow_succ,pow_mul]
      simpa only [Nat.mul_comm 2] using square_shape (hd n) ih
  rw [pow_mul]
  exact pow_shape (hd a) h0 m

/-- A root with even scalar coordinate is a multiple of π. Its
even power is a multiple of the indicated rational power of 2. -/
theorem nonunit_even_power (x : A) (hx : Even x.re) (n : Nat) :
    (2:A)^n ∣ x^(2*n) := by
  obtain ⟨b,hb⟩ := hx
  let y : A := ⟨x.im,b⟩
  have hp : x=pi*y := by
    ext
    · change x.re=0*x.im+2*1*b
      rw [hb]
      ring
    · change x.im=0*b+1*x.im+0*1*b
      ring
  rw [hp,mul_pow,pow_mul,pi_sq]
  exact dvd_mul_right _ _

#print axioms dyadic_power_shape
#print axioms nonunit_even_power
end WaringSiegel.SqrtTwo

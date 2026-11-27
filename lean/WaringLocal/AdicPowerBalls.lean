import WaringLinear.CubicLocalLifting
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.Tactic

/-! Power-map lifting on principal balls of complete rings. A separate
coefficientwise argument transfers adic completeness to a quadratic
algebra, allowing direct application to ℤ₂[√2]. -/
noncomputable section
namespace WaringSiegel.AdicPowerBalls
open Polynomial
variable {R : Type*} [CommRing R]

/-- If c is in the defining ideal, a polynomial perturbation x+c f(x)
is onto. -/
theorem polynomial_perturbation (I : Ideal R) [IsAdicComplete I R]
    (c : R) (hc : c∈I) (p : R[X]) (b : R) : ∃ x, x+c*p.eval x=b := by
  let f : R → R := fun x => b-c*p.eval x
  have hg (n : ℕ) (x y : R) (hxy : x-y∈I^n) : f x-f y∈I^(n+1) := by
    obtain ⟨v,hv⟩ := Polynomial.sub_dvd_eval_sub x y p
    have h : f x-f y=((x-y)*c)*(-v) := by
      calc
        _ = -(c*(p.eval x-p.eval y)) := by dsimp [f]; ring
        _ = _ := by rw [hv]; ring
    rw [h,pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hxy hc)
  obtain ⟨x,hx⟩ := WaringLinear.CubicLocalLifting.exists_adic_fixed_point I f hg
  exact ⟨x,by dsimp [f] at hx; linear_combination -hx⟩

private def remainder (c : R) : ℕ → R[X]
  | 0 => 0
  | n+1 => remainder c n + C (n:R)*X^2+C c*X*remainder c n

private theorem power_expand (c x : R) (n : ℕ) :
    (1+c*x)^n=1+c*((n:R)*x+c*(remainder c n).eval x) := by
  induction n with
  | zero => simp [remainder]
  | succ n ih =>
    rw [pow_succ,ih]
    simp only [remainder,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_pow,Polynomial.eval_C,Nat.cast_succ]
    ring

/-- The m-th power map is onto the entire ball 1+cR when m is a unit. -/
theorem coprime_power_ball (I : Ideal R) [IsAdicComplete I R]
    (c : R) (hc : c∈I) (m : ℕ) (hm : IsUnit (m:R)) (b : R) :
    ∃ x, (1+c*x)^m=1+c*b := by
  obtain ⟨v,hv⟩ := hm
  let u : R := ↑v⁻¹
  have hu : (m:R)*u=1 := by rw [←hv]; exact Units.mul_inv v
  obtain ⟨x,hx⟩ := polynomial_perturbation I (u*c) (I.mul_mem_left _ hc)
    (remainder c m) (u*b)
  refine ⟨x,?_⟩
  rw [power_expand]
  have h : (m:R)*(x+(u*c)*(remainder c m).eval x)=(m:R)*(u*b) := congrArg ((m:R)*·) hx
  rw [←mul_assoc,hu,one_mul] at h
  rw [mul_add] at h
  have h' : (m:R)*((u*c)*(remainder c m).eval x)=c*(remainder c m).eval x := by
    rw [←mul_assoc,←mul_assoc,hu,one_mul]
  rw [h'] at h
  rw [h]

/-- Successive squaring maps 1+4R onto 1+4*2^a R, provided the
ring is complete at an ideal containing 2. -/
theorem two_power_ball (I : Ideal R) [IsAdicComplete I R] (h₂ : (2:R)∈I)
    (a : ℕ) (b : R) : ∃ x, (1+4*x)^(2^a)=1+4*(2:R)^a*b := by
  induction a generalizing b with
  | zero => exact ⟨b,by simp⟩
  | succ a ih =>
    let v := (2:R)^a
    obtain ⟨t,ht⟩ := polynomial_perturbation I (v*2) (I.mul_mem_left _ h₂) (X^2) b
    simp only [Polynomial.eval_pow,Polynomial.eval_X] at ht
    obtain ⟨x,hx⟩ := ih t
    refine ⟨x,?_⟩
    rw [pow_succ,pow_mul,hx,show (2:R)^(a+1)=v*2 from pow_succ _ _,←ht]
    change (1+4*v*t)^2=1+4*(v*2)*(t+v*2*t^2)
    ring

section Quadratic
variable (r d b : R)
local notation "Q" => QuadraticAlgebra R d b
private abbrev I : Ideal Q := Ideal.span {algebraMap R Q r}
private abbrev J : Ideal R := Ideal.span {r}

private theorem scalar_pow_mul (n : ℕ) (x : Q) :
    (algebraMap R Q r)^n*x=(⟨r^n*x.re,r^n*x.im⟩ : Q) := by
  rw [←map_pow,QuadraticAlgebra.algebraMap_eq]
  ext <;> simp

private theorem mem_power (z : Q) (n : ℕ) :
    z ∈ (I r d b)^n ↔ z.re ∈ (J r)^n ∧ z.im ∈ (J r)^n := by
  simp only [I,J,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x,rfl⟩
    rw [scalar_pow_mul]
    exact ⟨⟨x.re,rfl⟩,⟨x.im,rfl⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨x,y⟩,by rw [scalar_pow_mul]; exact QuadraticAlgebra.ext hx hy⟩

/-- A rank-two quadratic algebra inherits principal-ideal completeness
coordinatewise from its base ring. -/
theorem quadratic_complete [IsAdicComplete (Ideal.span {r}) R] :
    IsAdicComplete (Ideal.span {algebraMap R Q r}) Q where
  haus' x hx := by
    have hmem (n:ℕ) : x.re ∈ (J r)^n ∧ x.im ∈ (J r)^n := by
      apply (mem_power r d b x n).mp
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using hx n
    apply QuadraticAlgebra.ext
    · apply IsHausdorff.haus' (I:=J r)
      intro n
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using (hmem n).1
    · apply IsHausdorff.haus' (I:=J r)
      intro n
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using (hmem n).2
  prec' f hf := by
    have hp {m n : ℕ} (hmn : m≤n) :
        (f m).re-(f n).re∈(J r)^m ∧ (f m).im-(f n).im∈(J r)^m := by
      have hmn' := hf hmn
      simp only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] at hmn'
      exact (mem_power r d b (f m-f n) m).mp hmn'
    obtain ⟨a,ha⟩ := IsPrecomplete.prec' (I:=J r) (fun n => (f n).re)
      (fun h => by simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using (hp h).1)
    obtain ⟨c,hc⟩ := IsPrecomplete.prec' (I:=J r) (fun n => (f n).im)
      (fun h => by simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using (hp h).2)
    refine ⟨⟨a,c⟩,fun n => ?_⟩
    simp only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top]
    apply (mem_power r d b _ n).mpr
    simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using And.intro (ha n) (hc n)
end Quadratic

#print axioms two_power_ball
#print axioms coprime_power_ball
#print axioms quadratic_complete
end WaringSiegel.AdicPowerBalls

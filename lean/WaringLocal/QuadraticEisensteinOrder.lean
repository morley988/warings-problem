import WaringLocal.SqrtTwoRational
import WaringLocal.SqrtTwoSmallWidths
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr

/-! The full ring of integers in a quadratic Eisenstein extension.
The unequal valuation parities of the two norm terms also handle the
dyadic case, where one cannot recover the scalar coordinate by
dividing an integral trace by the degree. -/
noncomputable section
namespace WaringLocal.QuadraticEisensteinOrder
open scoped Padic
variable {p : ℕ} [Fact p.Prime]
abbrev Base (p : Nat) [Fact p.Prime] := ℤ_[p]
abbrev LocalField (p : Nat) [Fact p.Prime] := ℚ_[p]
abbrev Order (D : Base p) := QuadraticAlgebra (Base p) D 0
abbrev Ambient (D : Base p) := QuadraticAlgebra (LocalField p) (D:LocalField p) 0

def embed (D : Base p) : Order D →ₐ[Base p] Ambient D where
  toFun x := ⟨x.re,x.im⟩
  map_zero' := by ext <;> rfl
  map_one' := by ext <;> rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp
  commutes' _ := rfl

private def scalar (D : Base p) : LocalField p →ₐ[Base p] Ambient D where
  toFun x := ⟨x,0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp
  commutes' _ := rfl

private def conj (D : Base p) : Ambient D →ₐ[Base p] Ambient D where
  toFun x := ⟨x.re,-x.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [QuadraticAlgebra.im_one]
  map_add' x y := by ext <;> simp [add_comm]
  map_mul' x y := by ext <;> simp <;> ring
  commutes' x := by
    apply QuadraticAlgebra.ext
    · rfl
    · change -(0:LocalField p)=0
      exact neg_zero

private def discrNorm (D : Base p) (a b : LocalField p) := a^2-D*b^2

private theorem unequal (D : Base p) (hD : (D:LocalField p).valuation=1)
    {a b : LocalField p} (ha : a≠0) (hb : b≠0) :
    ‖a^2‖ ≠ ‖(D:LocalField p)*b^2‖ := by
  have hd : (D:LocalField p)≠0 := by intro h; rw [h,Padic.valuation_zero] at hD; contradiction
  have hp₀ : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp₁ : (p:ℝ)≠1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  intro he
  rw [Padic.norm_eq_zpow_neg_valuation (pow_ne_zero _ ha),
    Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hd (pow_ne_zero _ hb)),
    zpow_right_inj₀ hp₀ hp₁,Padic.valuation_mul hd (pow_ne_zero _ hb),hD,
    Padic.valuation_pow,Padic.valuation_pow] at he
  omega

private theorem norm_max (D : Base p) (hD : (D:LocalField p).valuation=1)
    (a b : LocalField p) :
    ‖discrNorm D a b‖=max ‖a^2‖ ‖(D:LocalField p)*b^2‖ := by
  by_cases ha : a=0
  · simp [discrNorm,ha]; positivity
  by_cases hb : b=0
  · simp [discrNorm,hb]
  have h := unequal D hD ha hb
  have hmax := Padic.add_eq_max_of_ne (q:=a^2) (r:= -((D:LocalField p)*b^2))
    (by simpa using h)
  simpa [discrNorm,sub_eq_add_neg] using hmax

/-- The quadratic algebra at a radicand of valuation one is a field. -/
theorem ambient_is_field (D : Base p) (hD : (D:LocalField p).valuation=1) : IsField (Ambient D) where
  exists_pair_ne := ⟨0,1,zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let N := discrNorm D x.re x.im
    have hN : N≠0 := by
      intro hz
      have h := norm_max D hD x.re x.im
      change ‖N‖=_ at h
      rw [hz,norm_zero] at h
      have ha := (le_max_left ‖x.re^2‖ ‖(D:LocalField p)*x.im^2‖).trans h.symm.le
      have hb := (le_max_right ‖x.re^2‖ ‖(D:LocalField p)*x.im^2‖).trans h.symm.le
      have hd : (D:LocalField p)≠0 := by intro he; rw [he,Padic.valuation_zero] at hD; contradiction
      have hre : x.re=0 := by simpa using (norm_le_zero_iff.mp ha)
      have him : x.im=0 := by simpa [hd] using (norm_le_zero_iff.mp hb)
      exact hx (QuadraticAlgebra.ext hre him)
    refine ⟨⟨x.re/N,-x.im/N⟩,?_⟩
    apply QuadraticAlgebra.ext
    · change x.re*(x.re/N)+(D:LocalField p)*x.im*(-x.im/N)=1
      field_simp [hN]
      dsimp [N,discrNorm]
      ring
    · change x.re*(-x.im/N)+x.im*(x.re/N)+0*x.im*(-x.im/N)=0
      ring

private theorem integral_iff_norm (a : LocalField p) : IsIntegral (Base p) a ↔ ‖a‖≤1 := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y,h⟩ => h ▸ y.property,fun hy => ⟨⟨a,hy⟩,rfl⟩⟩

/-- The image of the quadratic integer order is exactly the full
integral closure, without any hypothesis that two is invertible. -/
theorem integral_iff_in_order (D : Base p) (hD : (D:LocalField p).valuation=1)
    (x : Ambient D) : IsIntegral (Base p) x ↔ ∃ z : Order D, embed D z=x := by
  constructor
  · intro hx
    have hc : IsIntegral (Base p) (conj D x) := IsIntegral.map (conj D) hx
    have hNm : scalar D (discrNorm D x.re x.im)=x*conj D x := by
      ext <;> simp [scalar,conj,discrNorm] <;> ring
    have hinj : Function.Injective (scalar D) := fun _ _ h => congrArg QuadraticAlgebra.re h
    have hn := (isIntegral_algHom_iff (scalar D) hinj).mp (hNm ▸ hx.mul hc)
    have hl := (integral_iff_norm _).mp hn
    rw [norm_max D hD,max_le_iff] at hl
    have ha : ‖x.re‖≤1 := by
      have hnorm := hl.1
      rw [norm_pow] at hnorm
      nlinarith only [hnorm,sq_nonneg (‖x.re‖-1)]
    have hb : ‖x.im‖≤1 := by
      by_cases h : x.im=0
      · simp [h]
      · have hd : (D:LocalField p)≠0 := by intro he; rw [he,Padic.valuation_zero] at hD; contradiction
        have hval := (Padic.norm_le_one_iff_val_nonneg _).mp hl.2
        rw [Padic.valuation_mul hd (pow_ne_zero _ h),hD,Padic.valuation_pow] at hval
        apply (Padic.norm_le_one_iff_val_nonneg _).mpr
        omega
    exact ⟨⟨⟨x.re,ha⟩,⟨x.im,hb⟩⟩,QuadraticAlgebra.ext rfl rfl⟩
  · rintro ⟨z,rfl⟩
    exact IsIntegral.map (embed D) (Algebra.IsIntegral.isIntegral z)

/-- In particular the exact-width results for the explicit quadratic
2-adic ring apply to the full integers of ℚ₂(√2). -/
theorem sqrt_two_full_integers (x : Ambient (2:Base 2)) :
    IsIntegral (Base 2) x ↔ ∃ z : WaringSiegel.SqrtTwo.A, embed (2:Base 2) z=x := by
  apply integral_iff_in_order
  change (2:ℚ_[2]).valuation=1
  simpa using (Padic.valuation_p (p:=2))

#print axioms ambient_is_field
#print axioms integral_iff_in_order
#print axioms sqrt_two_full_integers
end WaringLocal.QuadraticEisensteinOrder

import WaringLinear.RamifiedCubicOrder
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The integers of the local field ℚ₃(√6)

The ambient algebra is explicitly proved to be a field. Its integral
closure of ℤ₃ consists exactly of the pairs of integral coefficients,
so the local cube computation applies to the field's full integer ring.
-/
namespace WaringLinear.RamifiedCubicIntegers
open WaringLinear.RamifiedCubicOrder
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
abbrev Q₃ := ℚ_[3]
abbrev Ambient := QuadraticAlgebra Q₃ 6 0

/-- The natural inclusion of the explicit quadratic integer order. -/
def embed : Order →ₐ[Base] Ambient where
  toFun z := ⟨(z.re:Q₃),(z.im:Q₃)⟩
  map_zero' := by ext <;> rfl
  map_one' := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_mul' x y := by
    have he : ((6:Base):Q₃)=6 := by convert (map_natCast (algebraMap Base Q₃) 6) using 1
    ext <;> simp [he]
  commutes' _ := rfl

private def scalar : Q₃ →ₐ[Base] Ambient where
  toFun x := ⟨x,0⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  commutes' _ := rfl

private def conj : Ambient →ₐ[Base] Ambient where
  toFun z := ⟨z.re,-z.im⟩
  map_zero' := by ext <;> simp
  map_one' := QuadraticAlgebra.ext rfl (show -(0:Q₃) = 0 by simp)
  map_add' _ _ := by ext <;> simp [add_comm]
  map_mul' _ _ := by ext <;> simp <;> ring
  commutes' _ := QuadraticAlgebra.ext rfl (show -(0:Q₃) = 0 by simp)

private theorem scalar_injective : Function.Injective scalar := fun _ _ h =>
  congrArg QuadraticAlgebra.re h

private theorem v₂ : (2:Q₃).valuation = 0 := by
  rw [Padic.valuation_ofNat,padicValNat.eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
  rfl
private theorem v₆ : (6:Q₃).valuation = 1 := by
  rw [show (6:Q₃) = 2*3 by norm_num,Padic.valuation_mul (by norm_num) (by norm_num),v₂]
  convert Padic.valuation_p (p:=3) using 1 <;> simp

private def discrNorm (x : Ambient) : Q₃ := x.re^2-6*x.im^2

private theorem discrNorm_ne_zero (x : Ambient) (hx : x≠0) : discrNorm x≠0 := by
  intro h
  have he := sub_eq_zero.mp h
  by_cases hb : x.im=0
  · rw [hb] at he
    simp at he
    exact hx (QuadraticAlgebra.ext he hb)
  · have hrhs : (6:Q₃)*x.im^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hb)
    have ha : x.re≠0 := by intro ha; apply hrhs; rw [← he,ha]; ring
    have hv := congrArg Padic.valuation he
    rw [Padic.valuation_pow,Padic.valuation_mul (by norm_num) (pow_ne_zero _ hb),
      v₆,Padic.valuation_pow] at hv
    omega

/-- The quadratic ambient algebra is a field. Nonvanishing of its norm
uses the parity of the 3-adic valuations of a² and 6b². -/
theorem ambient_is_field : IsField Ambient where
  exists_pair_ne := ⟨0,1,zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let N := discrNorm x
    have hN : N≠0 := discrNorm_ne_zero x hx
    refine ⟨⟨x.re/N,-x.im/N⟩,?_⟩
    apply QuadraticAlgebra.ext
    · change x.re*(x.re/N)+6*x.im*(-x.im/N) = 1
      field_simp [hN]
      dsimp [N,discrNorm]
      ring
    · change x.re*(-x.im/N)+x.im*(x.re/N)+0*x.im*(-x.im/N) = 0
      ring

private theorem integral_iff_nonneg (x : Q₃) :
    IsIntegral Base x ↔ 0≤x.valuation := by
  rw [IsIntegrallyClosed.isIntegral_iff,← Padic.norm_le_one_iff_val_nonneg]
  constructor
  · rintro ⟨y,rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

/-- An element of ℚ₃(√6) is integral precisely when both coordinates
in the quadratic basis lie in ℤ₃. -/
theorem integral_iff_in_order (x : Ambient) :
    IsIntegral Base x ↔ ∃ z : Order, embed z=x := by
  constructor
  · intro hx
    have hc : IsIntegral Base (conj x) := IsIntegral.map conj hx
    have hTr : scalar (2*x.re)=x+conj x := by ext <;> simp [scalar,conj] <;> ring
    have hNm : scalar (discrNorm x)=x*conj x := by
      ext <;> simp [scalar,conj,discrNorm] <;> ring
    have ht : IsIntegral Base (2*x.re) := (isIntegral_algHom_iff scalar scalar_injective).mp
      (hTr ▸ hx.add hc)
    have hn : IsIntegral Base (discrNorm x) := (isIntegral_algHom_iff scalar scalar_injective).mp
      (hNm ▸ hx.mul hc)
    have ha : 0≤x.re.valuation := by
      by_cases h : x.re=0
      · simp [h]
      · have hh := (integral_iff_nonneg _).mp ht
        rwa [Padic.valuation_mul (by norm_num) h,v₂,zero_add] at hh
    have h₆ : IsIntegral Base (6*x.im^2) := by
      have he : 6*x.im^2=x.re^2-discrNorm x := by unfold discrNorm; ring
      rw [he]
      exact ((integral_iff_nonneg _).mpr ha).pow 2 |>.sub hn
    have hb : 0≤x.im.valuation := by
      by_cases h : x.im=0
      · simp [h]
      · have hh := (integral_iff_nonneg _).mp h₆
        rw [Padic.valuation_mul (by norm_num) (pow_ne_zero _ h),v₆,Padic.valuation_pow] at hh
        omega
    exact ⟨⟨⟨x.re,(Padic.norm_le_one_iff_val_nonneg _).mpr ha⟩,
             ⟨x.im,(Padic.norm_le_one_iff_val_nonneg _).mpr hb⟩⟩,QuadraticAlgebra.ext rfl rfl⟩
  · rintro ⟨z,rfl⟩
    exact IsIntegral.map embed (Algebra.IsIntegral.isIntegral z)

end
#print axioms ambient_is_field
#print axioms integral_iff_in_order
end WaringLinear.RamifiedCubicIntegers

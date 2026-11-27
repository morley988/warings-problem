import Waring.PolicyCompletionSharpPhaseSize
import Waring.PolicyCompletionSourceMajor

/-!
# Source arc widths imply the actual derivative smallness condition

The full power of R in the original major-arc width is retained. The
extra R^k absorbs only a fixed degree/box constant, uniformly in every
height and coefficient parameter. No derivative estimate is assumed.
-/

noncomputable section
namespace Waring.PolicyCompletionSourceMajorSize
open Polynomial IntegerDifferencePolynomial PolicyCompletionPhaseContent
open PolicyCompletionSharpPhaseSize

def derivativeBoxConstant (k j : ℕ) (CP CS : ℝ) : ℝ :=
  (2:ℝ)^j*(k.descFactorial (j+1):ℝ)*(CP+CS)^(k-j-1)

theorem derivativeBoxConstant_nonneg (k j : ℕ) {CP CS : ℝ}
    (hCP : 0≤CP) (hCS : 0≤CS) : 0≤derivativeBoxConstant k j CP CS := by
  unfold derivativeBoxConstant
  positivity

theorem source_derivative_box_bound (k j : ℕ) (hj : j<k)
    {P R N H CP CS : ℝ} (hP : 0<P) (hR : 1≤R) (hN : 0≤N)
    (hH : 0≤H) (hCP : 0≤CP) (hCS : 0≤CS)
    (params : List (ℤ × ℤ)) (hlen : params.length=j)
    (hparams : ∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2)
    (hcenter : N≤CP*P) (hheight : (heightProduct params:ℝ)≤H)
    (hshift : shiftRadius k params≤CS*P*R^k) :
    ((powerPolynomial k params).map (Int.castRingHom ℝ)).derivative.eval N ≤
      derivativeBoxConstant k j CP CS*H*P^(k-j-1)*R^(k*(k-j-1)) := by
  have hrad : N+shiftRadius k params≤(CP+CS)*P*R^k := by
    have hRk : 1≤R^k := one_le_pow₀ hR
    have hC := mul_le_mul_of_nonneg_left hRk (mul_nonneg hCP hP.le)
    nlinarith
  have hbound := source_derivative_bound k params hparams (by omega) hN
  rw [hlen, show k-(j+1)=k-j-1 by omega] at hbound
  apply hbound.trans
  calc
    _ ≤ (2:ℝ)^j*H*(k.descFactorial (j+1):ℝ)*((CP+CS)*P*R^k)^(k-j-1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hheight (by positivity)) (Nat.cast_nonneg _)
      · exact pow_le_pow_left₀ (add_nonneg hN (shiftRadius_nonneg k params)) hrad _
      · exact pow_nonneg (add_nonneg hN (shiftRadius_nonneg k params)) _
      · positivity
    _ = _ := by
      unfold derivativeBoxConstant
      rw [mul_pow, mul_pow, ← pow_mul]
      ring

theorem source_arc_derivative_small (k j : ℕ) (hj : j<k)
    {P R N H CP CS β q : ℝ} (hP : 0<P) (hR : 1≤R) (hN : 0≤N)
    (hH : 0≤H) (hCP : 0≤CP) (hCS : 0≤CS) (hq : 0<q)
    (params : List (ℤ × ℤ)) (hlen : params.length=j)
    (hparams : ∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2)
    (hcenter : N≤CP*P) (hheight : (heightProduct params:ℝ)≤H)
    (hshift : shiftRadius k params≤CS*P*R^k)
    (hwidth : |β| *H*P^(k-j-1)*R^(k*(k-j))≤1/q)
    (hRlarge : 2*derivativeBoxConstant k j CP CS≤R^k) :
    |β| *((powerPolynomial k params).map (Int.castRingHom ℝ)).derivative.eval N≤1/(2*q) := by
  let C := derivativeBoxConstant k j CP CS
  let t : ℝ := |β| *H*P^(k-j-1)*R^(k*(k-j-1))
  have hC : 0≤C := derivativeBoxConstant_nonneg k j hCP hCS
  have ht : 0≤t := by dsimp [t]; positivity
  have hDE : (k-j-1)+1=k-j := by omega
  have htwidth : t*R^k≤1/q := by
    dsimp [t]
    rw [mul_assoc (|β| *H*P^(k-j-1)), ← pow_add,
      show k*(k-j-1)+k=k*(k-j) by
        calc
          k*(k-j-1)+k = k*((k-j-1)+1) := by ring
          _ = k*(k-j) := by rw [hDE]]
    exact hwidth
  have hsmall : C*t≤1/(2*q) := by
    have hmul := mul_le_mul_of_nonneg_right hRlarge ht
    have hid : 1/(2*q)=(1/q)/2 := by ring
    rw [hid]
    change 2*C≤R^k at hRlarge
    nlinarith
  have hderiv := source_derivative_box_bound k j hj hP hR hN hH hCP hCS params hlen
    hparams hcenter hheight hshift
  apply (mul_le_mul_of_nonneg_left hderiv (abs_nonneg _)).trans
  calc
    _ = C*t := by dsimp [C,t]; ring
    _ ≤ _ := hsmall

#print axioms source_derivative_box_bound
#print axioms source_arc_derivative_small
end Waring.PolicyCompletionSourceMajorSize

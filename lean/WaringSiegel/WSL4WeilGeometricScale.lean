import WaringSiegel.WSL4WeilGeometricEvaluation
import WaringSiegel.WSL4WeilVandermondeValuation

noncomputable section
open Polynomial IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

theorem qFactorial_eval_isUnit
    {R : Type*} [CommRing R] [IsLocalRing R] {pi : R} (hpi : ¬ IsUnit pi)
    (m n : ℕ) (hm : 0<m) :
    IsUnit ((WSL4Local.qFactorial n).eval₂ (Int.castRingHom R) (pi^m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [WSL4Local.qFactorial_succ,eval₂_mul,eval₂_sub,eval₂_one,eval₂_pow,eval₂_X]
    apply ih.mul
    apply isUnit_one_sub_self_of_mem_nonunits
    change ¬IsUnit ((pi^m)^(n+1))
    rw [isUnit_pow_succ_iff,isUnit_pow_iff hm.ne']
    exact hpi

theorem geometricRamanujamScale_factor
    {R : Type*} [CommRing R] (pi : R) (m n : ℕ) :
    geometricRamanujamScale pi m n=
      pi^(m*n+1)*(WSL4Local.qFactorial n).eval₂ (Int.castRingHom R) (pi^m) := by
  dsimp [geometricRamanujamScale]
  rw [← pow_mul,pow_succ]
  ring

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem geometricRamanujamScale_valuation {pi : R} (hpi : Irreducible pi)
    (m n : ℕ) (hm : 0<m) :
    IsDiscreteValuationRing.addVal R (geometricRamanujamScale pi m n)=(m*n+1:ℕ) := by
  rw [geometricRamanujamScale_factor,IsDiscreteValuationRing.addVal_mul,
    hpi.addVal_pow,(IsDiscreteValuationRing.addVal_eq_zero_iff).2
      (qFactorial_eval_isUnit hpi.not_isUnit m n hm),add_zero]

theorem geometricRamanujamScale_span {pi : R} (hpi : Irreducible pi)
    (m n : ℕ) (hm : 0<m) :
    Ideal.span ({geometricRamanujamScale pi m n}:Set R)=(maximalIdeal R)^(m*n+1) := by
  rw [geometricRamanujamScale_factor,Ideal.span_singleton_mul_right_unit
    (qFactorial_eval_isUnit hpi.not_isUnit m n hm),
    (IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi,
    Ideal.span_singleton_pow]

theorem mem_maximalIdeal_power_iff_geometricScale_dvd {pi : R} (hpi : Irreducible pi)
    (m n : ℕ) (hm : 0<m) (x : R) :
    x∈(maximalIdeal R)^(m*n+1) ↔ geometricRamanujamScale pi m n∣x := by
  rw [← geometricRamanujamScale_span hpi m n hm,Ideal.mem_span_singleton]
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.geometricRamanujamScale_valuation
#print axioms WaringSiegel.WSL4Weil.geometricRamanujamScale_span
#print axioms WaringSiegel.WSL4Weil.mem_maximalIdeal_power_iff_geometricScale_dvd

import Waring.SeedCompletionTerminalIdentitySeries

/-! # Exact normalized hyperbolic-sine factors of the source symbol -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalIdentity

@[simp] theorem constantCoeff_rescale (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (PowerSeries.rescale a f)=PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

def unitSinh : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (1-(-1 : ℚ)^(n+1))/(2*((n+1).factorial : ℚ)))

theorem unitSinh_constant : PowerSeries.constantCoeff unitSinh=1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  norm_num [unitSinh,PowerSeries.coeff_mk]

theorem qExp_sub (a : ℚ) :
    qExp a-qExp (-a)=PowerSeries.C (2*a)*
      (PowerSeries.X*PowerSeries.rescale a unitSinh) := by
  ext n
  cases n with
  | zero => simp [qExp]
  | succ n =>
      rw [map_sub,PowerSeries.coeff_C_mul]
      rw [show (PowerSeries.X : PowerSeries ℚ)=PowerSeries.X^1 by simp,
        PowerSeries.coeff_X_pow_mul]
      simp only [qExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp,
        unitSinh,PowerSeries.coeff_mk,Algebra.algebraMap_self,RingHom.id_apply,
        Nat.succ_eq_add_one]
      rw [neg_pow a (n+1),pow_succ a n]
      ring

theorem differenceSymbol_eq_sinh (k : ℕ) (h m : ℚ) (hm : m≠0) :
    differenceSymbol k h m=PowerSeries.C (2*h)*
      (PowerSeries.X*PowerSeries.rescale (h*m^k) unitSinh) := by
  rw [differenceSymbol,qExp_sub,← mul_assoc,← map_mul]
  congr 2
  field_simp

def unitSymbol (k : ℕ) (params : List (ℚ×ℚ)) : PowerSeries ℚ :=
  (params.map (fun hm => PowerSeries.rescale (hm.1*hm.2^k) unitSinh)).prod

def symbolFactor (params : List (ℚ×ℚ)) : ℚ :=
  2^params.length*(params.map Prod.fst).prod

theorem unitSymbol_constant (k : ℕ) (params : List (ℚ×ℚ)) :
    PowerSeries.constantCoeff (unitSymbol k params)=1 := by
  induction params with
  | nil => simp [unitSymbol]
  | cons hm rest ih =>
      simp only [unitSymbol,List.map_cons,List.prod_cons,map_mul] at ih ⊢
      simpa [constantCoeff_rescale,unitSinh_constant] using ih

theorem rawSymbol_eq_unitSymbol (k : ℕ) (params : List (ℚ×ℚ))
    (hm : ∀ p∈params,p.2≠0) :
    rawSymbol k params=PowerSeries.C (symbolFactor params)*
      (PowerSeries.X^params.length*unitSymbol k params) := by
  induction params with
  | nil => simp [rawSymbol,unitSymbol,symbolFactor]
  | cons p rest ih =>
      have hr := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
      change differenceSymbol k p.1 p.2*rawSymbol k rest=_
      rw [differenceSymbol_eq_sinh k p.1 p.2 (hm p (List.mem_cons_self ..)),hr]
      simp only [symbolFactor,List.length_cons,pow_succ,List.map_cons,List.prod_cons,
        unitSymbol,map_mul,map_pow,map_ofNat]
      ring

#print axioms qExp_sub
#print axioms rawSymbol_eq_unitSymbol
end Waring.SeedCompletionTerminalIdentity

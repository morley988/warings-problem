import Waring.PolicyCompletionPhaseContent
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Derivative

/-! # The exact exponential generating series of centered source polynomials

The degree of the initial monomial is independent of the normalizing power
in each difference. This makes the formal series identity exact at every
coefficient, before specializing to the actual Waring source polynomial.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalIdentity
open Polynomial IntegerDifferencePolynomial

def qExp (a : ℚ) : PowerSeries ℚ := PowerSeries.rescale a (PowerSeries.exp ℚ)
def polyExp (a : Polynomial ℚ) : PowerSeries (Polynomial ℚ) :=
  PowerSeries.rescale a (PowerSeries.exp (Polynomial ℚ))
def translate (a : ℚ) : Polynomial ℚ →+* Polynomial ℚ :=
  Polynomial.compRingHom (Polynomial.X+Polynomial.C a)

theorem polyExp_add (a b : Polynomial ℚ) : polyExp (a+b)=polyExp a*polyExp b :=
  (PowerSeries.exp_mul_exp_eq_exp_add a b).symm

theorem map_qExp (a : ℚ) :
    PowerSeries.map Polynomial.C (qExp a)=polyExp (Polynomial.C a) := by
  ext n
  simp [qExp,polyExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp]

theorem map_translate_polyExp (a : ℚ) (x : Polynomial ℚ) :
    PowerSeries.map (translate a) (polyExp x)=polyExp (translate a x) := by
  ext n
  simp [translate,polyExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp]

theorem map_translate_scalar (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.map (translate a) (PowerSeries.map Polynomial.C f)=
      PowerSeries.map Polynomial.C f := by
  ext n
  simp [translate]

theorem translate_exponential_product (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.map (translate a)
      (polyExp Polynomial.X*PowerSeries.map Polynomial.C f)=
    polyExp Polynomial.X*PowerSeries.map Polynomial.C (qExp a*f) := by
  rw [map_mul,map_translate_polyExp,map_translate_scalar,map_mul,map_qExp]
  have hx : translate a Polynomial.X=Polynomial.X+Polynomial.C a := by simp [translate]
  rw [hx,polyExp_add,mul_assoc]

def differenceSymbol (k : ℕ) (h m : ℚ) : PowerSeries ℚ :=
  PowerSeries.C ((m^k)⁻¹)*(qExp (h*m^k)-qExp (-(h*m^k)))

def rawSymbol (k : ℕ) (params : List (ℚ×ℚ)) : PowerSeries ℚ :=
  (params.map (fun hm => differenceSymbol k hm.1 hm.2)).prod

def sourceSeries (k : ℕ) (params : List (ℚ×ℚ)) : PowerSeries (Polynomial ℚ) :=
  polyExp Polynomial.X*PowerSeries.map Polynomial.C (rawSymbol k params)

def rationalDifference (k : ℕ) (h m : ℚ) (f : Polynomial ℚ) : Polynomial ℚ :=
  Polynomial.C ((m^k)⁻¹)*(translate (h*m^k) f-translate (-(h*m^k)) f)

def rationalPower (k : ℕ) : List (ℚ×ℚ) → ℕ → Polynomial ℚ
  | [],n => Polynomial.X^n
  | hm::rest,n => rationalDifference k hm.1 hm.2 (rationalPower k rest n)

theorem sourceSeries_cons (k : ℕ) (hm : ℚ×ℚ) (rest : List (ℚ×ℚ)) :
    sourceSeries k (hm::rest)=PowerSeries.C (Polynomial.C ((hm.2^k)⁻¹))*
      (PowerSeries.map (translate (hm.1*hm.2^k)) (sourceSeries k rest)-
       PowerSeries.map (translate (-(hm.1*hm.2^k))) (sourceSeries k rest)) := by
  unfold sourceSeries
  rw [translate_exponential_product,translate_exponential_product]
  simp only [rawSymbol,List.map_cons,List.prod_cons,differenceSymbol,
    map_mul,map_sub,PowerSeries.map_C]
  ring

theorem sourceSeries_coeff (k n : ℕ) (params : List (ℚ×ℚ)) :
    PowerSeries.coeff n (sourceSeries k params)=
      Polynomial.C (1/(n.factorial : ℚ))*rationalPower k params n := by
  induction params with
  | nil =>
      simp only [sourceSeries,rawSymbol,List.map_nil,List.prod_nil,map_one,mul_one,
        polyExp,PowerSeries.coeff_rescale,PowerSeries.coeff_exp,rationalPower]
      change Polynomial.X^n*Polynomial.C (1/(n.factorial : ℚ))=_
      ring
  | cons hm rest ih =>
      rw [sourceSeries_cons,PowerSeries.coeff_C_mul,map_sub,
        PowerSeries.coeff_map,PowerSeries.coeff_map,ih]
      simp only [rationalPower,rationalDifference,map_mul,translate,
        Polynomial.coe_compRingHom_apply,Polynomial.C_comp]
      ring

#print axioms sourceSeries_coeff
end Waring.SeedCompletionTerminalIdentity

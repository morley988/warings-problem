import Waring.SeedCompletionCurveTranslation
import Mathlib.Algebra.Polynomial.Taylor

/-! # Translation preserves monicity and the degree in the second variable -/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation
variable {K : Type*} [CommRing K]

theorem shiftHom_injective (a : K) :
    Function.Injective (eval₂RingHom C (X+C a) : K[X] →+* K[X]) := by
  change Function.Injective (fun p : K[X] => p.comp (X+C a))
  exact taylor_injective a

theorem translate_monic {p : K[X][Y]} (hp : p.Monic) (a b : K) :
    (translate p a b).Monic := by
  rw [translate_eq_map_comp]
  exact (hp.map (eval₂RingHom C (X+C a))).comp_X_add_C (C b)

theorem translate_natDegree (p : K[X][Y]) (a b : K) :
    (translate p a b).natDegree=p.natDegree := by
  rw [translate_eq_map_comp,← taylor_apply,natDegree_taylor,
    natDegree_map_eq_of_injective (shiftHom_injective a)]

#print axioms translate_monic
#print axioms translate_natDegree
end Waring.SeedCompletionCurveTranslation

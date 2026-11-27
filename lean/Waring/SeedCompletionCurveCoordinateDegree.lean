import Waring.SeedCompletionCurveFactors
import Waring.SeedCompletionCurveTranslationDegree

/-! # Coordinate degree under a literal plane translation -/

noncomputable section
open Polynomial
open scoped Polynomial Polynomial.Bivariate
namespace Waring.SeedCompletionCurveTranslation

section Ring
variable {K : Type*} [CommRing K]

theorem swap_translate (p : K[X][Y]) (a b : K) :
    Polynomial.Bivariate.swap (translate p a b)=
      translate (Polynomial.Bivariate.swap p) b a := by
  have he : Polynomial.Bivariate.swap.toRingHom.comp (translateHom a b) =
      (translateHom b a).comp Polynomial.Bivariate.swap.toRingHom := by
    ext <;> simp [translateHom,coe_compRingHom_apply]
  exact congrArg (fun f : K[X][Y] →+* K[X][Y] => f p) he

theorem swap_translate_natDegree (p : K[X][Y]) (a b : K) :
    (Polynomial.Bivariate.swap (translate p a b)).natDegree=
      (Polynomial.Bivariate.swap p).natDegree := by
  rw [swap_translate,translate_natDegree]

end Ring
section Field
variable {K : Type*} [Field K]

theorem translate_factor_coefficient_natDegree_le {p F : K[X][Y]}
    (hF : F ≠ 0) (hp : p ∣ F) (a b : K) (n : ℕ) :
    ((translate p a b).coeff n).natDegree ≤ (Polynomial.Bivariate.swap F).natDegree := by
  apply (SeedCompletionCurveFactors.coefficient_natDegree_le_swap (translate p a b) n).trans
  rw [swap_translate_natDegree]
  apply natDegree_le_of_dvd (map_dvd Polynomial.Bivariate.swap.toRingHom hp)
  exact (map_ne_zero_iff Polynomial.Bivariate.swap.toRingHom
    Polynomial.Bivariate.swap.injective).mpr hF

end Field

#print axioms swap_translate_natDegree
#print axioms translate_factor_coefficient_natDegree_le
end Waring.SeedCompletionCurveTranslation

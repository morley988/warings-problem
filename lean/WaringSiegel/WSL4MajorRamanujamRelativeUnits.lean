import WaringSiegel.WSL4MajorRamanujamRelativeRing

/-! # Rational normalization units belong to the monogenic coefficient ring -/
noncomputable section
namespace WaringSiegel.WSL4
open WSL4Local
variable {B A : Type*} [CommRing B] [CommRing A]

theorem rationalPrimeCoefficientRing_le_relativePrimeCoefficientRing
    (p : ℕ) (f : B →+* A) :
    rationalPrimeCoefficientRing p A ≤ relativePrimeCoefficientRing p f := by
  rintro c ⟨a,b,hb,hc⟩
  refine ⟨(a:B),(b:B),?_,?_⟩
  · simpa only [Int.cast_natCast] using (hb.intCast (R:=B))
  · simpa only [map_intCast] using hc

#print axioms rationalPrimeCoefficientRing_le_relativePrimeCoefficientRing
end WaringSiegel.WSL4

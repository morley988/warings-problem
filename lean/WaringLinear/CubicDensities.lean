import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# Cube residues at the ramified prime of ℚ(√6)

The coefficients of an algebraic integer in the basis (1, √6) are
reduced modulo 9. The finite calculations use kernel reduction.
-/
namespace WaringLinear.CubicDensities

/-- Coefficients of the cube in any commutative ring with an element
satisfying the quadratic equation of √6. -/
theorem cube_expansion {R : Type*} [CommRing R] (a b t : R) (h : t^2 = 6) :
    (a+b*t)^3 = (a^3+18*a*b^2) + 3*b*(a^2+2*b^2)*t := by
  calc
    _ = (a^3+18*a*b^2) + 3*b*(a^2+2*b^2)*t +
        (3*a*b^2+b^3*t)*(t^2-6) := by ring
    _ = _ := by rw [h]; ring

abbrev Residue := ZMod 9 × ZMod 9

def cube (x : Residue) : Residue :=
  (x.1^3 + 18*x.1*x.2^2, 3*x.2*(x.1^2+2*x.2^2))

def allCubes : Finset Residue := Finset.univ.image cube

def fiveResidues : Finset Residue :=
  {(0,0), (1,0), (8,0), (0,3), (0,6)}

set_option maxRecDepth 20000 in
theorem cube_image : allCubes = fiveResidues := by decide

/-- All residues obtained as sums of exactly s cube values. -/
def sums : Nat → Finset Residue
  | 0 => {0}
  | s + 1 => ((sums s) ×ˢ fiveResidues).image (fun p => p.1+p.2)

theorem mem_sums_succ (s : Nat) (z : Residue) :
    z ∈ sums (s+1) ↔ ∃ x ∈ sums s, ∃ y : Residue, x + cube y = z := by
  rw [sums, ← cube_image]
  constructor
  · intro hz
    obtain ⟨⟨x,c⟩, hp, he⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hc⟩ := Finset.mem_product.mp hp
    obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hc
    exact ⟨x,hx,y,by simpa [hy] using he⟩
  · rintro ⟨x,hx,y,he⟩
    apply Finset.mem_image.mpr
    exact ⟨(x,cube y),Finset.mem_product.mpr
      ⟨hx,Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩⟩,he⟩

def eligible : Finset Residue :=
  Finset.univ.filter (fun z => z.2 = 0 ∨ z.2 = 3 ∨ z.2 = 6)

set_option maxRecDepth 20000 in
theorem eligible_card : eligible.card = 27 := by decide

set_option maxRecDepth 20000 in
theorem three_card : (sums 3).card = 17 := by decide

set_option maxRecDepth 20000 in
theorem four_card : (sums 4).card = 23 := by decide

set_option maxRecDepth 20000 in
theorem five_exact : sums 5 = eligible := by decide

/-- A representation in which at least one cube is a unit residue. -/
def withUnit (s : Nat) : Finset Residue :=
  ((sums s) ×ˢ ({(1,0), (8,0)} : Finset Residue)).image (fun p => p.1+p.2)

set_option maxRecDepth 20000 in
theorem three_with_unit : withUnit 2 = sums 3 := by decide

set_option maxRecDepth 20000 in
theorem four_with_unit : withUnit 3 = sums 4 := by decide

set_option maxRecDepth 20000 in
theorem three_eligible : sums 3 ⊆ eligible := by decide

set_option maxRecDepth 20000 in
theorem four_eligible : sums 4 ⊆ eligible := by decide

theorem counts_in_products (r : Nat) :
    Fintype.card (Fin r → ↥(sums 3)) = 17^r ∧
    Fintype.card (Fin r → ↥(sums 4)) = 23^r ∧
    Fintype.card (Fin r → ↥eligible) = 27^r := by
  simp [three_card, four_card, eligible_card]

#print axioms counts_in_products
#print axioms three_eligible
#print axioms four_eligible
#print axioms three_with_unit
#print axioms four_with_unit
#print axioms cube_expansion
#print axioms cube_image
#print axioms mem_sums_succ
#print axioms eligible_card
#print axioms three_card
#print axioms four_card
#print axioms five_exact

end WaringLinear.CubicDensities

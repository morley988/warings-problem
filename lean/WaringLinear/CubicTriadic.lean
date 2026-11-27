import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.Data.ZMod.Basic
import WaringLinear.CubicLocalLifting
import WaringLinear.CubicTernaryPairing

/-! The sharp four-cube obstruction on the quadratic ramified ring modulo
nine and the five-cube upper bound in every ring where two is invertible. -/
open scoped BigOperators
namespace WaringLinear.CubicTriadic

/-- The residue algebra with `π² = -3`, reduced modulo nine. -/
abbrev Residue := QuadraticAlgebra (ZMod 9) (-3) 0

private def letters : Fin 5 → Residue :=
  ![⟨0,0⟩, ⟨1,0⟩, ⟨-1,0⟩, ⟨0,3⟩, ⟨0,-3⟩]

set_option maxRecDepth 16000 in
private theorem cube_letters : ∀ a b : ZMod 9, ∃ i : Fin 5,
    (⟨a,b⟩ : Residue)^3=letters i := by decide +kernel

set_option maxRecDepth 16000 in
private theorem four_letters : ∀ a b c d : Fin 5,
    letters a+letters b+letters c+letters d ≠ (⟨4,3⟩ : Residue) := by decide +kernel

/-- In the genuine residue ring, `4+3π` cannot be represented by four cubes. -/
theorem four_cubes_obstruction (a b c d : Residue) :
    a^3+b^3+c^3+d^3 ≠ (⟨4,3⟩ : Residue) := by
  obtain ⟨i,hi⟩ := cube_letters a.re a.im
  obtain ⟨j,hj⟩ := cube_letters b.re b.im
  obtain ⟨k,hk⟩ := cube_letters c.re c.im
  obtain ⟨l,hl⟩ := cube_letters d.re d.im
  simpa only [QuadraticAlgebra.mk_eta,←hi,←hj,←hk,←hl] using four_letters i j k l

/-- The particular obstruction is itself a sum of five cubes. -/
theorem five_cubes_attained :
    (1:Residue)^3+1^3+1^3+1^3+(⟨0,-1⟩:Residue)^3=⟨4,3⟩ := by decide +kernel

/-- Any ring reducing to these coordinates inherits the obstruction. -/
theorem four_cubes_obstruction_of_map {A : Type*} [CommRing A]
    (φ : A →+* Residue) (n : A) (hn : φ n = ⟨4,3⟩) :
    ¬∃ x : Fin 4 → A, ∑ i, (x i)^3=n := by
  rintro ⟨x,hx⟩
  apply four_cubes_obstruction (φ (x 0)) (φ (x 1)) (φ (x 2)) (φ (x 3))
  simpa [Fin.sum_univ_succ,add_assoc,hn] using congrArg φ hx

/-- Five cubes suffice for the whole additive cube group whenever two
has a multiplicative inverse, without any local-field assumption. -/
theorem five_cubes_of_two_unit {A : Type*} [CommRing A] (u : A) (hu : 2*u=1)
    {n : A} (hn : n ∈ AddSubgroup.closure (Set.range fun x : A => x^3)) :
    ∃ x : Fin 5 → A, ∑ i, (x i)^3=n := by
  obtain ⟨r,s,hr⟩ := CubicLocalLifting.cube_mod_three_of_mem_span hn
  let y := u*s
  refine ⟨![r,y+1,y-1,-y,-y],?_⟩
  simp [Fin.sum_univ_succ]
  dsimp [y]
  linear_combination CubicTernaryPairing.four_signed_cubes (u*s) - hr + 3*s*hu

#print axioms four_cubes_obstruction_of_map
#print axioms five_cubes_attained
#print axioms five_cubes_of_two_unit
end WaringLinear.CubicTriadic

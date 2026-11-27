import WaringSiegel.WSL4LocalSquaresAlgebra
import WaringSiegel.WSL3MomentLocalPowerLift

/-! # The actual Hensel inputs for local squares, including residue characteristic two -/
noncomputable section
set_option maxHeartbeats 1000000
open Polynomial IsLocalRing
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [HenselianLocalRing R]

theorem four_squares_henselian_two_unit [Finite (ResidueField R)]
    (h2:IsUnit (2:R)) (a:R) :
    ∃x:Fin 4→R,(∑i,x i^2)=a ∧ ∃i,IsUnit (x i) := by
  have h2r : (2:ResidueField R)≠0 := by
    simpa only [map_ofNat] using (h2.map (residue R)).ne_zero
  obtain ⟨x,y,z,hxyz⟩ := finiteField_three_squares h2r (residue R a-1)
  let v : Fin 4→ResidueField R := ![1,x,y,z]
  have hs : (∑i,v i^2)=residue R a := by
    calc
      _ = 1+(x^2+y^2+z^2) := by norm_num [v,Fin.sum_univ_succ]; ring
      _ = _ := by rw [hxyz]; ring
  exact power_tuple_lift_of_nonzero_residue 2 (by norm_num) h2 v hs
    ⟨0,by simp [v]⟩

theorem five_squares_henselian_two_unit [Finite (ResidueField R)]
    (h2:IsUnit (2:R)) (a:R) :
    ∃x:Fin 5→R,(∑i,x i^2)=a ∧ ∃i,IsUnit (x i) :=
  power_tuple_unit_pad (by norm_num) (four_squares_henselian_two_unit h2 a)

theorem dyadic_hensel_minus_seven (h2:¬IsUnit (2:R)) :
    ∃r:R,r^2= -7 ∧ residue R r= -1 := by
  have h20 : (2:ResidueField R)=0 := by
    have hh := (residue_ne_zero_iff_isUnit (2:R)).not.mpr h2
    simpa only [map_ofNat,not_not] using hh
  let f : R[X] := X^2-X+C 2
  have hf : f.Monic := by
    dsimp [f]
    rw [sub_eq_add_neg,add_assoc]
    apply monic_X_pow_add
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · simp only [degree_neg,degree_X]
      norm_num
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  have hroot : aeval (0:ResidueField R) f=0 := by simp [f,h2]
  have hder : aeval (0:ResidueField R) f.derivative≠0 := by simp [f]
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨α,hα,-⟩ := hH f hf 0 hroot hder
  have ha : α^2-α+2=0 := by simpa [f,Polynomial.IsRoot] using hα
  refine ⟨2*α-1,?_,?_⟩
  · calc
      _ = 4*(α^2-α+2)-7 := by ring
      _ = _ := by rw [ha]; ring
  · simp only [map_sub,map_mul,map_ofNat,map_one,h20,zero_mul,zero_sub]

#print axioms five_squares_henselian_two_unit
#print axioms dyadic_hensel_minus_seven
end WaringSiegel.WSL4Local

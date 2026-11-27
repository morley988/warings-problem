import WaringSiegel.WSL4ArchRamanujamGenerators
import WaringSiegel.WSL4ArchRamanujamSubring

/-! # A residue-surjective coefficient ring and a deep ghost remainder

Only residue surjectivity is needed. All original eligibility and ramification
information is retained in the literal coefficient map and ideal coordinates.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000
variable {p : ℕ} [Fact p.Prime]
variable {B R : Type*} [CommRing B] [CommRing R]

theorem map_ramanujamPowerTuple (f : B →+* R) (s : ℕ) (x : Fin (s+1) → B) :
    f (ramanujamPowerTuple p s x)=ramanujamPowerTuple p s (fun i => f (x i)) := by
  simp only [ramanujamPowerTuple,map_sum,map_mul,map_pow,map_natCast]

theorem ramanujamPowerTuple_difference_ideal_expression
    (s : ℕ) (I : Ideal R) (x y : Fin (s+1) → R)
    (hxy : ∀i,Ideal.Quotient.mk I (x i)=Ideal.Quotient.mk I (y i)) :
    ∃z : Fin (s+1) → R,(∀i,z i∈I) ∧
      ramanujamPowerTuple p s z=ramanujamPowerTuple p s x-ramanujamPowerTuple p s y := by
  have hmem := Ideal.Quotient.eq.mp (ramanujamPowerTuple_quotient_congr (p:=p) s I x y hxy)
  exact (mem_ramanujamPowerIdeal_iff_fin s I _).mp hmem

theorem ramanujam_coefficient_ghost_decomposition
    (s : ℕ) (I : Ideal R) (f : B →+* R)
    (hf : Function.Surjective ((Ideal.Quotient.mk I).comp f))
    (a : R) (ha : a∈ramanujamPowerSubring p s R) :
    ∃b : B,∃w : Fin (s+1) → R,(∀i,w i∈I) ∧
      a=f b+ramanujamPowerTuple p s w := by
  obtain ⟨x,hx⟩ := (mem_ramanujamPowerSubring_iff_fin (p:=p) s a).mp ha
  have hlift : ∀i : Fin (s+1),∃y : B,Ideal.Quotient.mk I (f y)=Ideal.Quotient.mk I (x i) :=
    fun i => hf (Ideal.Quotient.mk I (x i))
  choose y hy using hlift
  obtain ⟨w,hw,he⟩ := ramanujamPowerTuple_difference_ideal_expression (p:=p)
    s I x (fun i => f (y i)) (fun i => (hy i).symm)
  refine ⟨ramanujamPowerTuple p s y,w,hw,?_⟩
  rw [hx,← map_ramanujamPowerTuple f s y] at he
  linear_combination -he

theorem eligible_coefficient_ghost_decomposition
    (n s : ℕ) (I : Ideal R) (f : B →+* R)
    (hf : Function.Surjective ((Ideal.Quotient.mk I).comp f))
    (a : R) (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^(n*p^s)))) :
    ∃b : B,∃w : Fin (s+1) → R,(∀i,w i∈I) ∧
      a=f b+ramanujamPowerTuple p s w := by
  obtain ⟨b,hba,-⟩ := eligible_power_generator_mem_closure (p:=p) n s a ha
  exact ramanujam_coefficient_ghost_decomposition s I f hf a (hba ▸ b.property)

#print axioms map_ramanujamPowerTuple
#print axioms ramanujamPowerTuple_difference_ideal_expression
#print axioms ramanujam_coefficient_ghost_decomposition
#print axioms eligible_coefficient_ghost_decomposition
end WaringSiegel.WSL4

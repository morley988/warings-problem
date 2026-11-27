import WaringSiegel.WSL4ArchRamanujamGhost
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The ideal version of Ramanujam's truncated power-sum lemma

The Witt vectors with coefficients in I form the kernel of the map to
Witt vectors over R/I. Its ghost image is an ideal of the ghost-image
subring C_s. The membership theorem identifies this ideal with the literal
finite power expressions whose coordinates belong to I.
-/
noncomputable section
open scoped BigOperators
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

def ramanujamWittIdeal (p : ℕ) [Fact p.Prime] (I : Ideal R) : Ideal (WittVector p R) :=
  RingHom.ker (WittVector.map (p:=p) (Ideal.Quotient.mk I))

theorem mem_ramanujamWittIdeal_iff (I : Ideal R) (x : WittVector p R) :
    x∈ramanujamWittIdeal p I ↔ ∀i,x.coeff i∈I := by
  simp only [ramanujamWittIdeal,RingHom.mem_ker,WittVector.ext_iff,
    WittVector.map_coeff,WittVector.zero_coeff,Ideal.Quotient.eq_zero_iff_mem]

def ramanujamPowerIdeal (p s : ℕ) [Fact p.Prime] (I : Ideal R) :
    Ideal (ramanujamPowerSubring p s R) :=
  (ramanujamWittIdeal p I).map (WittVector.ghostComponent (p:=p) (R:=R) s).rangeRestrict

theorem mem_ramanujamPowerIdeal_iff (s : ℕ) (I : Ideal R)
    (a : ramanujamPowerSubring p s R) :
    a∈ramanujamPowerIdeal p s I ↔
      ∃x : ℕ → R,(∀i,x i∈I) ∧ ramanujamPowerSum p s x=(a:R) := by
  rw [ramanujamPowerIdeal,Ideal.mem_map_iff_of_surjective _
    (RingHom.rangeRestrict_surjective _)]
  constructor
  · rintro ⟨x,hx,he⟩
    refine ⟨x.coeff,(mem_ramanujamWittIdeal_iff I x).mp hx,?_⟩
    have hval := congrArg (fun a : ramanujamPowerSubring p s R => (a:R)) he
    exact (ghostComponent_eq_ramanujamPowerSum s x).symm.trans hval
  · rintro ⟨x,hx,he⟩
    refine ⟨WittVector.mk p x,(mem_ramanujamWittIdeal_iff I _).mpr hx,?_⟩
    apply Subtype.ext
    exact (ghostComponent_eq_ramanujamPowerSum s (WittVector.mk p x)).trans he

theorem ramanujamPowerSum_mem_powerIdeal (s : ℕ) (I : Ideal R)
    (x : ℕ → R) (hx : ∀i,x i∈I) :
    (⟨ramanujamPowerSum p s x,ramanujamPowerSum_mem s x⟩ : ramanujamPowerSubring p s R)∈
      ramanujamPowerIdeal p s I :=
  (mem_ramanujamPowerIdeal_iff s I _).mpr ⟨x,hx,rfl⟩

theorem ramanujamPowerSum_ideal_add (s : ℕ) (I : Ideal R)
    (x y : ℕ → R) (hx : ∀i,x i∈I) (hy : ∀i,y i∈I) :
    ∃z : ℕ → R,(∀i,z i∈I) ∧
      ramanujamPowerSum p s z=ramanujamPowerSum p s x+ramanujamPowerSum p s y := by
  let a : ramanujamPowerSubring p s R := ⟨ramanujamPowerSum p s x,ramanujamPowerSum_mem s x⟩
  let b : ramanujamPowerSubring p s R := ⟨ramanujamPowerSum p s y,ramanujamPowerSum_mem s y⟩
  exact (mem_ramanujamPowerIdeal_iff s I (a+b)).mp
    ((ramanujamPowerIdeal p s I).add_mem
      (ramanujamPowerSum_mem_powerIdeal s I x hx) (ramanujamPowerSum_mem_powerIdeal s I y hy))

theorem ramanujamPowerSum_ideal_mul (s : ℕ) (I : Ideal R)
    (x y : ℕ → R) (hx : ∀i,x i∈I) :
    ∃z : ℕ → R,(∀i,z i∈I) ∧
      ramanujamPowerSum p s z=ramanujamPowerSum p s x*ramanujamPowerSum p s y := by
  let a : ramanujamPowerSubring p s R := ⟨ramanujamPowerSum p s x,ramanujamPowerSum_mem s x⟩
  let b : ramanujamPowerSubring p s R := ⟨ramanujamPowerSum p s y,ramanujamPowerSum_mem s y⟩
  exact (mem_ramanujamPowerIdeal_iff s I (a*b)).mp
    ((ramanujamPowerIdeal p s I).mul_mem_right b (ramanujamPowerSum_mem_powerIdeal s I x hx))

theorem ramanujamPowerSum_ideal_neg (s : ℕ) (I : Ideal R)
    (x : ℕ → R) (hx : ∀i,x i∈I) :
    ∃z : ℕ → R,(∀i,z i∈I) ∧ ramanujamPowerSum p s z= -ramanujamPowerSum p s x := by
  let a : ramanujamPowerSubring p s R := ⟨ramanujamPowerSum p s x,ramanujamPowerSum_mem s x⟩
  exact (mem_ramanujamPowerIdeal_iff s I (-a)).mp
    ((ramanujamPowerIdeal p s I).neg_mem (ramanujamPowerSum_mem_powerIdeal s I x hx))

theorem prime_power_difference_truncated_ideal_expression
    (s : ℕ) (I : Ideal R) (x y : R) (hxy : x-y∈I) :
    ∃z : ℕ → R,(∀i,z i∈I) ∧ ramanujamPowerSum p s z=x^(p^s)-y^(p^s) := by
  let w : WittVector p R := WittVector.teichmuller p x-WittVector.teichmuller p y
  have hq : Ideal.Quotient.mk I x=Ideal.Quotient.mk I y := Ideal.Quotient.eq.mpr hxy
  have hw : w∈ramanujamWittIdeal p I := by
    change WittVector.map (Ideal.Quotient.mk I) w=0
    dsimp only [w]
    rw [map_sub,WittVector.map_teichmuller,WittVector.map_teichmuller,hq,sub_self]
  refine ⟨w.coeff,(mem_ramanujamWittIdeal_iff I w).mp hw,?_⟩
  rw [← ghostComponent_eq_ramanujamPowerSum]
  dsimp only [w]
  rw [map_sub,
    WittVector.ghostComponent_teichmuller,WittVector.ghostComponent_teichmuller]

#print axioms mem_ramanujamPowerIdeal_iff
#print axioms ramanujamPowerSum_ideal_add
#print axioms ramanujamPowerSum_ideal_mul
#print axioms prime_power_difference_truncated_ideal_expression
end WaringSiegel.WSL4

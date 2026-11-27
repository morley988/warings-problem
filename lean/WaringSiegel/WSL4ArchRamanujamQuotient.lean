import WaringSiegel.WSL4ArchRamanujamFinite
import Mathlib.SetTheory.Cardinal.Finite

/-! # A quantitative quotient bound for Ramanujam's truncated-power ideal

Only s+1 residue coordinates are required to represent every class of C_s/I_s.
Thus its cardinality is at most card(R/I)^(s+1), for every finite quotient R/I.
-/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

theorem ramanujamPowerSum_difference_ideal_expression
    (s : ℕ) (I : Ideal R) (x y : ℕ → R)
    (hxy : ∀i,Ideal.Quotient.mk I (x i)=Ideal.Quotient.mk I (y i)) :
    ∃z : ℕ → R,(∀i,z i∈I) ∧
      ramanujamPowerSum p s z=ramanujamPowerSum p s x-ramanujamPowerSum p s y := by
  let w : WittVector p R := WittVector.mk p x-WittVector.mk p y
  have hmap : WittVector.map (p:=p) (Ideal.Quotient.mk I) (WittVector.mk p x)=
      WittVector.map (Ideal.Quotient.mk I) (WittVector.mk p y) := by
    ext i
    exact hxy i
  have hw : w∈ramanujamWittIdeal p I := by
    change WittVector.map (Ideal.Quotient.mk I) w=0
    dsimp only [w]
    rw [map_sub,hmap,sub_self]
  refine ⟨w.coeff,(mem_ramanujamWittIdeal_iff I w).mp hw,?_⟩
  rw [← ghostComponent_eq_ramanujamPowerSum]
  dsimp only [w]
  rw [map_sub,ghostComponent_eq_ramanujamPowerSum,ghostComponent_eq_ramanujamPowerSum]
  rfl

def ramanujamPowerTupleElem (p s : ℕ) [Fact p.Prime] (x : Fin (s+1) → R) :
    ramanujamPowerSubring p s R :=
  ⟨ramanujamPowerTuple p s x,(mem_ramanujamPowerSubring_iff_fin s _).mpr ⟨x,rfl⟩⟩

theorem ramanujamPowerTuple_quotient_congr
    (s : ℕ) (I : Ideal R) (x y : Fin (s+1) → R)
    (hxy : ∀i,Ideal.Quotient.mk I (x i)=Ideal.Quotient.mk I (y i)) :
    Ideal.Quotient.mk (ramanujamPowerIdeal p s I) (ramanujamPowerTupleElem p s x)=
      Ideal.Quotient.mk (ramanujamPowerIdeal p s I) (ramanujamPowerTupleElem p s y) := by
  have hext : ∀i,Ideal.Quotient.mk I (ramanujamExtendTuple x i)=
      Ideal.Quotient.mk I (ramanujamExtendTuple y i) := by
    intro i
    by_cases hi : i<s+1
    · simpa only [ramanujamExtendTuple,dif_pos hi] using hxy ⟨i,hi⟩
    · simp only [ramanujamExtendTuple,dif_neg hi]
  obtain ⟨z,hz,he⟩ := ramanujamPowerSum_difference_ideal_expression (p:=p) s I _ _ hext
  rw [ramanujamPowerSum_extend,ramanujamPowerSum_extend] at he
  apply Ideal.Quotient.eq.mpr
  exact (mem_ramanujamPowerIdeal_iff s I _).mpr ⟨z,hz,he⟩

def ramanujamResidueLift (I : Ideal R) (a : R ⧸ I) : R :=
  Classical.choose (Ideal.Quotient.mk_surjective a)

theorem ramanujamResidueLift_spec (I : Ideal R) (a : R ⧸ I) :
    Ideal.Quotient.mk I (ramanujamResidueLift I a)=a :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective a)

def ramanujamQuotientRepresentative (p s : ℕ) [Fact p.Prime] (I : Ideal R)
    (x : Fin (s+1) → R ⧸ I) : (ramanujamPowerSubring p s R) ⧸ ramanujamPowerIdeal p s I :=
  Ideal.Quotient.mk (ramanujamPowerIdeal p s I)
    (ramanujamPowerTupleElem p s (fun i => ramanujamResidueLift I (x i)))

theorem ramanujamQuotientRepresentative_surjective (s : ℕ) (I : Ideal R) :
    Function.Surjective (ramanujamQuotientRepresentative p s I) := by
  intro b
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨x,hx⟩ := (mem_ramanujamPowerSubring_iff_fin (p:=p) s (a:R)).mp a.property
  refine ⟨fun i => Ideal.Quotient.mk I (x i),?_⟩
  have he : ramanujamPowerTupleElem p s x=a := Subtype.ext hx
  rw [← he]
  apply ramanujamPowerTuple_quotient_congr
  intro i
  exact ramanujamResidueLift_spec I _

theorem finite_ramanujamPowerQuotient (s : ℕ) (I : Ideal R) [Finite (R ⧸ I)] :
    Finite ((ramanujamPowerSubring p s R) ⧸ ramanujamPowerIdeal p s I) :=
  Finite.of_surjective _ (ramanujamQuotientRepresentative_surjective (p:=p) s I)

theorem card_ramanujamPowerQuotient_le (s : ℕ) (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card ((ramanujamPowerSubring p s R) ⧸ ramanujamPowerIdeal p s I)≤
      Nat.card (R ⧸ I)^(s+1) := by
  have h := Nat.card_le_card_of_surjective (ramanujamQuotientRepresentative p s I)
    (ramanujamQuotientRepresentative_surjective (p:=p) s I)
  simpa only [Nat.card_fun,Nat.card_fin] using h

#print axioms ramanujamPowerTuple_quotient_congr
#print axioms finite_ramanujamPowerQuotient
#print axioms card_ramanujamPowerQuotient_le
end WaringSiegel.WSL4

import Mathlib.RingTheory.WittVector.Basic
import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Ramanujam's truncated power-sum subring via proved Witt identities

For a prime p, the finite expression
  sum_{i=0}^s p^i x_i^(p^(s-i))
is exactly the s-th p-typical Witt ghost component. Its range is therefore
a subring over every commutative ring, without completeness, unramifiedness,
characteristic, or residue-field assumptions.
-/
noncomputable section
open scoped BigOperators
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000

def ramanujamPowerSum (p s : ℕ) {R : Type*} [CommRing R] (x : ℕ → R) : R :=
  ∑ i ∈ Finset.range (s+1),(p:R)^i*x i^(p^(s-i))

def ramanujamPowerSubring (p s : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] :
    Subring R :=
  (WittVector.ghostComponent (p:=p) (R:=R) s).range

theorem ghostComponent_eq_ramanujamPowerSum
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (s : ℕ) (x : WittVector p R) :
    WittVector.ghostComponent s x=ramanujamPowerSum p s x.coeff := by
  rw [WittVector.ghostComponent_apply,aeval_wittPolynomial]
  rfl

theorem mem_ramanujamPowerSubring_iff
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (a : R) :
    a∈ramanujamPowerSubring p s R ↔ ∃x : ℕ → R,ramanujamPowerSum p s x=a := by
  change (∃x : WittVector p R,WittVector.ghostComponent s x=a) ↔ _
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x.coeff,(ghostComponent_eq_ramanujamPowerSum s x).symm.trans hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨WittVector.mk p x,(ghostComponent_eq_ramanujamPowerSum s (WittVector.mk p x)).trans hx⟩

theorem ramanujamPowerSum_mem
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (x : ℕ → R) :
    ramanujamPowerSum p s x∈ramanujamPowerSubring p s R :=
  (mem_ramanujamPowerSubring_iff s _).mpr ⟨x,rfl⟩

theorem ramanujamPowerSum_add
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (x y : ℕ → R) :
    ∃z : ℕ → R,ramanujamPowerSum p s z=ramanujamPowerSum p s x+ramanujamPowerSum p s y :=
  (mem_ramanujamPowerSubring_iff s _).mp
    ((ramanujamPowerSubring p s R).add_mem (ramanujamPowerSum_mem s x) (ramanujamPowerSum_mem s y))

theorem ramanujamPowerSum_mul
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (x y : ℕ → R) :
    ∃z : ℕ → R,ramanujamPowerSum p s z=ramanujamPowerSum p s x*ramanujamPowerSum p s y :=
  (mem_ramanujamPowerSubring_iff s _).mp
    ((ramanujamPowerSubring p s R).mul_mem (ramanujamPowerSum_mem s x) (ramanujamPowerSum_mem s y))

theorem ramanujamPowerSum_neg
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (x : ℕ → R) :
    ∃z : ℕ → R,ramanujamPowerSum p s z= -ramanujamPowerSum p s x :=
  (mem_ramanujamPowerSubring_iff s _).mp
    ((ramanujamPowerSubring p s R).neg_mem (ramanujamPowerSum_mem s x))

theorem prime_power_mem_ramanujamPowerSubring
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (x : R) :
    x^(p^s)∈ramanujamPowerSubring p s R := by
  refine ⟨WittVector.teichmuller p x,?_⟩
  exact WittVector.ghostComponent_teichmuller p x s

theorem power_closure_le_ramanujamPowerSubring
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) :
    AddSubgroup.closure (Set.range (fun x : R => x^(p^s)))≤
      (ramanujamPowerSubring p s R).toAddSubgroup := by
  apply (AddSubgroup.closure_le _).mpr
  rintro a ⟨x,rfl⟩
  exact prime_power_mem_ramanujamPowerSubring s x

theorem eligible_prime_power_truncated_expression
    {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] (s : ℕ) (a : R)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^(p^s)))) :
    ∃x : ℕ → R,ramanujamPowerSum p s x=a :=
  (mem_ramanujamPowerSubring_iff s a).mp (power_closure_le_ramanujamPowerSubring s ha)

#print axioms mem_ramanujamPowerSubring_iff
#print axioms ramanujamPowerSum_add
#print axioms ramanujamPowerSum_mul
#print axioms eligible_prime_power_truncated_expression
end WaringSiegel.WSL4

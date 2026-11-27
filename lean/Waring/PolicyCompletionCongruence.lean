import Waring.AuxiliaryL2Grouping
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The actual common-residue Cauchy reduction

The fundamental efficient-differencing lemma groups solutions of
`Psi(c,z) + q*U(u) = Psi(c',z') + q*U(v)` by the common residue of Psi
modulo q, then applies Cauchy to the parameter/residue pairs `(c,z mod q)`.
This gives the count with `c=c'` and `z=z' (mod q)`, multiplied by the
maximum number of parameter/residue pairs above one polynomial residue.

The multiplier here is the cardinality of an actual finite set. No root
estimate, efficient-differencing recurrence, or source bound is assumed.
The separate nonsingular-root theorem can subsequently bound this exact
multiplier. This is the finite counting step on printed pages 239--240 of
Wooley's 1990 thesis, Part III, following equation (2.22).
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionCongruence
open AuxiliaryL2Grouping

/-- Frequency collisions retaining equality of the chosen class key. -/
def sameClassCollisions {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (f : ι → ℤ) (key : ι → κ) : Finset (ι × ι) :=
  (collisionPairs A f).filter (fun p => key p.1 = key p.2)

/-- Counting the disjoint class fibers gives exactly the same-class count. -/
theorem sameClassCollisions_card {ι κ : Type*} [DecidableEq κ]
    (A : Finset ι) (f : ι → ℤ) (key : ι → κ) (H : Finset κ)
    (hH : ∀ x ∈ A, key x ∈ H) :
    (sameClassCollisions A f key).card =
      ∑ h ∈ H, (collisionPairs (classFiber A key h) f).card := by
  classical
  have hmap : (sameClassCollisions A f key).toSet.MapsTo
      (fun p => key p.1) H := by
    intro p hp
    exact hH p.1
      (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  ext p
  simp only [sameClassCollisions,collisionPairs,classFiber,
    Finset.mem_filter,Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨⟨hx,hy⟩,hf⟩,hk⟩,hxh⟩
    exact ⟨⟨⟨hx,hxh⟩,hy,hk.symm.trans hxh⟩,hf⟩
  · rintro ⟨⟨⟨hx,hxh⟩,hy,hyh⟩,hf⟩
    exact ⟨⟨⟨⟨hx,hy⟩,hf⟩,hxh.trans hyh.symm⟩,hxh⟩

/-- The actual parameter/residue classes lying above one polynomial residue. -/
def residueKeys {κ : Type*} [DecidableEq κ] (A : Finset (κ × ℤ))
    (Ψ : κ → ℤ → ℤ) (q n : ℤ) : Finset (κ × ℤ) :=
  (A.filter (fun x => Ψ x.1 x.2 % q = n % q)).image
    (fun x => (x.1,x.2 % q))

/-- The largest actual root-class count among residues attained by Ψ on A. -/
def residueCapacity {κ : Type*} [DecidableEq κ] (A : Finset (κ × ℤ))
    (Ψ : κ → ℤ → ℤ) (q : ℤ) : ℕ :=
  (A.image (fun x => Ψ x.1 x.2 % q)).sup
    (fun n => (residueKeys A Ψ q n).card)

theorem residueKeys_card_le_capacity {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (Ψ : κ → ℤ → ℤ) (q n : ℤ) :
    (residueKeys A Ψ q n).card ≤ residueCapacity A Ψ q := by
  classical
  by_cases he : (residueKeys A Ψ q n).Nonempty
  · obtain ⟨a,ha⟩ := he
    obtain ⟨x,hx,hxa⟩ := Finset.mem_image.mp ha
    have hnx : n % q ∈ A.image (fun x => Ψ x.1 x.2 % q) :=
      Finset.mem_image.mpr ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
    have hs := Finset.le_sup
      (f := fun r => (residueKeys A Ψ q r).card) hnx
    simpa only [residueCapacity,residueKeys,Int.emod_emod] using hs
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    exact Nat.zero_le _

/-- Frequency after all smooth variables have the same extracted factor. -/
def liftedFrequency {κ ι : Type*} (Ψ : κ → ℤ → ℤ) (U : ι → ℤ) (q : ℤ)
    (x : (κ × ℤ) × ι) : ℤ :=
  Ψ x.1.1 x.1.2 + q * U x.2

def residueKey {κ ι : Type*} (q : ℤ) (x : (κ × ℤ) × ι) : κ × ℤ :=
  (x.1.1,x.1.2 % q)

/-- Every key above one exact frequency is an actual root class above the
corresponding polynomial residue. -/
theorem frequency_keys_subset {κ ι : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ι) (Ψ : κ → ℤ → ℤ)
    (U : ι → ℤ) (q n : ℤ) :
    (((A ×ˢ B).filter (fun x => liftedFrequency Ψ U q x=n)).image (residueKey q)) ⊆
      residueKeys A Ψ q n := by
  classical
  intro key hkey
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hkey
  rcases Finset.mem_filter.mp hx with ⟨hx,hfreq⟩
  apply Finset.mem_image.mpr
  refine ⟨x.1,Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hx).1,?_⟩,rfl⟩
  have hmod := congrArg (fun a : ℤ => a % q) hfreq
  simpa [liftedFrequency,Int.add_emod] using hmod

/-- Exact finite common-residue reduction. The count on the right retains
the original domains, frequencies, parameters, and smooth tuple variables. -/
theorem common_residue_collision_bound {κ ι : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ι) (Ψ : κ → ℤ → ℤ)
    (U : ι → ℤ) (q : ℤ) :
    ((collisionPairs (A ×ˢ B) (liftedFrequency Ψ U q)).card : ℝ) ≤
      (residueCapacity A Ψ q : ℝ) *
        ((sameClassCollisions (A ×ˢ B) (liftedFrequency Ψ U q) (residueKey q)).card : ℝ) := by
  classical
  let H := (A ×ˢ B).image (residueKey q)
  have hH : ∀ x ∈ A ×ˢ B, residueKey q x ∈ H :=
    fun x hx => Finset.mem_image_of_mem _ hx
  have hbound := collision_card_le_classes (A ×ˢ B) (liftedFrequency Ψ U q)
    (residueKey q) H hH (D := (residueCapacity A Ψ q : ℝ)) (by positivity)
    (fun n _ => by
      exact_mod_cast (Finset.card_le_card (frequency_keys_subset A B Ψ U q n)).trans
        (residueKeys_card_le_capacity A Ψ q n))
  rw [sameClassCollisions_card (A ×ˢ B) (liftedFrequency Ψ U q) (residueKey q) H hH,
    Nat.cast_sum]
  exact hbound

/-- The source congruence is literal equality of residues; the key also
retains equality of all auxiliary polynomial parameters. -/
theorem mem_sameClass_lifted {κ ι : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (B : Finset ι) (Ψ : κ → ℤ → ℤ)
    (U : ι → ℤ) (q : ℤ) (x y : (κ × ℤ) × ι) :
    (x,y) ∈ sameClassCollisions (A ×ˢ B) (liftedFrequency Ψ U q) (residueKey q) ↔
      x.1 ∈ A ∧ x.2 ∈ B ∧ y.1 ∈ A ∧ y.2 ∈ B ∧
      Ψ x.1.1 x.1.2 + q*U x.2 = Ψ y.1.1 y.1.2 + q*U y.2 ∧
      x.1.1=y.1.1 ∧ x.1.2 % q=y.1.2 % q := by
  classical
  simp only [sameClassCollisions,collisionPairs,liftedFrequency,residueKey,
    Finset.mem_filter,Finset.mem_product,Prod.mk.injEq]
  tauto

#print axioms common_residue_collision_bound
#print axioms mem_sameClass_lifted

end Waring.PolicyCompletionCongruence

import WaringSiegel.WSL4ArchLocalTuples
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Agreement of the manuscript's power-generated ring with eligibility

Products of kth powers are kth powers in every commutative ring, and 1 is
a kth power. Thus taking the generated subring or the generated additive
subgroup gives exactly the same set. This identifies the original
eligibility predicate with the local ring used in Ramanujam's theorem.
-/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4Local
variable {R : Type*} [CommRing R]

def powerGeneratedRing (k : ℕ) (R : Type*) [CommRing R] : Subring R :=
  Subring.closure (Set.range (fun x : R => x^k))

theorem power_range_multiplicatively_closed (k : ℕ) :
    (Submonoid.closure (Set.range (fun x : R => x^k)) : Set R)=
      Set.range (fun x : R => x^k) := by
  let M : Submonoid R :=
    { carrier := Set.range (fun x : R => x^k)
      one_mem' := ⟨1,one_pow k⟩
      mul_mem' := by
        rintro a b ⟨x,rfl⟩ ⟨y,rfl⟩
        exact ⟨x*y,mul_pow x y k⟩ }
  change (Submonoid.closure (M : Set R) : Set R)=(M : Set R)
  rw [Submonoid.closure_eq]

theorem mem_powerGeneratedRing_iff (k : ℕ) (a : R) :
    a∈powerGeneratedRing k R ↔
      a∈AddSubgroup.closure (Set.range (fun x : R => x^k)) := by
  rw [powerGeneratedRing,Subring.mem_closure_iff,
    power_range_multiplicatively_closed]

theorem powerGeneratedRing_toAddSubgroup (k : ℕ) :
    (powerGeneratedRing k R).toAddSubgroup=
      AddSubgroup.closure (Set.range (fun x : R => x^k)) := by
  ext a
  exact mem_powerGeneratedRing_iff k a

theorem map_mem_powerGeneratedRing {S : Type*} [CommRing S]
    (k : ℕ) (f : R →+* S) {a : R} (ha : a∈powerGeneratedRing k R) :
    f a∈powerGeneratedRing k S := by
  rw [mem_powerGeneratedRing_iff] at ha ⊢
  exact WSL4.map_mem_power_closure k f ha

theorem eligible_iff_mem_powerGeneratedRing
    {K : Type*} [Field K] [NumberField K] (k : ℕ) (ν : 𝓞 K) :
    Eligible k ν ↔ ν∈powerGeneratedRing k (𝓞 K) :=
  (mem_powerGeneratedRing_iff k ν).symm

#print axioms powerGeneratedRing_toAddSubgroup
#print axioms eligible_iff_mem_powerGeneratedRing
end WaringSiegel.WSL4Local

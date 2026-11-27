import WaringSiegel.WSL4ArchLocalPowerLists
import WaringSiegel.NumberFieldTargets
import Mathlib.Algebra.BigOperators.Fin

/-! # Functorial eligibility and genuine zero-padding of power tuples -/
noncomputable section
open scoped BigOperators NumberField
namespace WaringSiegel.WSL4
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_mem_power_closure (k : ℕ) (f : R →+* S) {a : R}
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^k))) :
    f a∈AddSubgroup.closure (Set.range (fun x : S => x^k)) := by
  let T := AddSubgroup.closure (Set.range (fun x : S => x^k))
  have h : AddSubgroup.closure (Set.range (fun x : R => x^k))≤
      T.comap f.toAddMonoidHom := by
    apply (AddSubgroup.closure_le _).mpr
    rintro b ⟨x,rfl⟩
    change f (x^k)∈T
    rw [map_pow]
    exact AddSubgroup.subset_closure (Set.mem_range_self (f x))
  exact h ha

theorem one_mem_power_closure (k : ℕ) :
    (1:R)∈AddSubgroup.closure (Set.range (fun x : R => x^k)) :=
  AddSubgroup.subset_closure ⟨1,one_pow k⟩

theorem sum_power_get_eq_localPowerListSum (k : ℕ) (l : List R) :
    (∑ i : Fin l.length,(l.get i)^k)=localPowerListSum k l := by
  rw [← Fin.sum_ofFn, List.ofFn_comp' l.get (fun x => x^k),List.ofFn_get]
  rfl

theorem power_tuple_with_unit_succ (k : ℕ) (hk : 0<k) {s : ℕ} {a : R}
    (h : ∃x : Fin s → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i)) :
    ∃x : Fin (s+1) → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  obtain ⟨x,hx,i,hi⟩ := h
  refine ⟨Fin.cons 0 x,?_,i.succ,?_⟩
  · simpa [Fin.sum_univ_succ,zero_pow hk.ne'] using hx
  · simpa using hi

theorem power_tuple_with_unit_mono (k : ℕ) (hk : 0<k) {s t : ℕ} {a : R}
    (h : ∃x : Fin s → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i)) (hst : s≤t) :
    ∃x : Fin t → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hst
  clear hst
  induction n with
  | zero => simpa using h
  | succ n ih => exact power_tuple_with_unit_succ k hk ih

theorem localUnitSolvable_mono
    {K : Type*} [Field K] [NumberField K] (k : ℕ) (hk : 0<k)
    {s t : ℕ} {ν : 𝓞 K} (h : LocalUnitSolvable k s ν) (hst : s≤t) :
    LocalUnitSolvable k t ν :=
  fun v => power_tuple_with_unit_mono k hk (h v) hst

#print axioms map_mem_power_closure
#print axioms localUnitSolvable_mono
end WaringSiegel.WSL4

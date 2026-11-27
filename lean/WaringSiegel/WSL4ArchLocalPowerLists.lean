import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic

/-! # Actual finite lists of odd powers and shortening of partial sums -/
noncomputable section
open scoped BigOperators Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 800000
variable {R : Type*} [CommRing R]

def localPowerListSum (k : ℕ) (l : List R) : R := (l.map (fun x => x^k)).sum

@[simp] theorem localPowerListSum_nil (k : ℕ) : localPowerListSum (R:=R) k []=0 := rfl
@[simp] theorem localPowerListSum_cons (k : ℕ) (x : R) (l : List R) :
    localPowerListSum k (x::l)=x^k+localPowerListSum k l := rfl
@[simp] theorem localPowerListSum_append (k : ℕ) (l m : List R) :
    localPowerListSum k (l++m)=localPowerListSum k l+localPowerListSum k m := by
  simp only [localPowerListSum,List.map_append,List.sum_append]

theorem localPowerListSum_map_mul (k : ℕ) (a : R) (l : List R) :
    localPowerListSum k (l.map (a*·))=a^k*localPowerListSum k l := by
  simp only [localPowerListSum,List.map_map,Function.comp_def,mul_pow,List.sum_map_mul_left]

theorem localPowerListSum_map_neg (k : ℕ) (hk : Odd k) (l : List R) :
    localPowerListSum k (l.map Neg.neg)=-localPowerListSum k l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,localPowerListSum_cons,hk.neg_pow,ih,neg_add]

theorem exists_power_list_of_mem_odd_closure (k : ℕ) (hk : Odd k) (a : R)
    (ha : a∈AddSubgroup.closure (Set.range (fun x : R => x^k))) :
    ∃ l : List R,localPowerListSum k l=a := by
  let S : AddSubgroup R :=
    { carrier := {a | ∃l : List R,localPowerListSum k l=a}
      zero_mem' := ⟨[],rfl⟩
      add_mem' := by
        rintro a b ⟨l,rfl⟩ ⟨m,rfl⟩
        exact ⟨l++m,localPowerListSum_append k l m⟩
      neg_mem' := by
        rintro a ⟨l,rfl⟩
        exact ⟨l.map Neg.neg,localPowerListSum_map_neg k hk l⟩ }
  have hS : AddSubgroup.closure (Set.range (fun x : R => x^k))≤S :=
    (AddSubgroup.closure_le S).mpr (by
      rintro a ⟨x,rfl⟩
      exact ⟨[x],by simp⟩)
  exact hS ha

theorem localPowerListSum_take_add_drop (k : ℕ) (l : List R) (j : ℕ) :
    localPowerListSum k (l.take j)+localPowerListSum k (l.drop j)=localPowerListSum k l := by
  rw [← localPowerListSum_append,List.take_append_drop]

theorem exists_shortest_power_list (k : ℕ) (a : R) (h : ∃l : List R,localPowerListSum k l=a) :
    ∃ l : List R,localPowerListSum k l=a ∧
      ∀m : List R,localPowerListSum k m=a → l.length≤m.length := by
  have hn : ∃n : ℕ,∃l : List R,l.length=n ∧ localPowerListSum k l=a := by
    obtain ⟨l,hl⟩ := h
    exact ⟨l.length,l,rfl,hl⟩
  obtain ⟨l,hlen,hl⟩ := Nat.find_spec hn
  refine ⟨l,hl,fun m hm => ?_⟩
  rw [hlen]
  exact Nat.find_min' hn ⟨m,rfl,hm⟩

theorem shortest_power_list_prefix_ne_zero (k : ℕ) (l : List R)
    (hmin : ∀m : List R,localPowerListSum k m=localPowerListSum k l → l.length≤m.length)
    (j : ℕ) (hj : 0<j) (hjl : j≤l.length) : localPowerListSum k (l.take j)≠0 := by
  intro hz
  have he : localPowerListSum k (l.drop j)=localPowerListSum k l := by
    simpa only [hz,zero_add] using localPowerListSum_take_add_drop k l j
  have hh := hmin (l.drop j) he
  rw [List.length_drop] at hh
  omega

theorem shortest_power_list_no_scaled_prefix (k : ℕ) (l : List R)
    (hmin : ∀m : List R,localPowerListSum k m=localPowerListSum k l → l.length≤m.length)
    (i j : ℕ) (hij : i<j) (hjl : j≤l.length) (a : R) :
    localPowerListSum k (l.take j)≠a^k*localPowerListSum k (l.take i) := by
  intro he
  let m := (l.take i).map (a*·)++l.drop j
  have hm : localPowerListSum k m=localPowerListSum k l := by
    rw [localPowerListSum_append,localPowerListSum_map_mul,← he,localPowerListSum_take_add_drop]
  have hh := hmin m hm
  have hi : i≤l.length := (Nat.le_of_lt hij).trans hjl
  simp only [m,List.length_append,List.length_map,List.length_take,List.length_drop,Nat.min_eq_left hi] at hh
  omega

#print axioms exists_power_list_of_mem_odd_closure
#print axioms shortest_power_list_no_scaled_prefix
end WaringSiegel.WSL4

import WaringSiegel.WSL4ArchFiniteFieldFullSpan

/-! # A residue-degree criterion for full power span

The full-span theorem applies as soon as f>=n in a field of cardinal p^f.
In particular it applies to the large-degree branch f>=m=n*p^s.
-/
noncomputable section
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000

theorem square_pred_lt_two_pow (n : ℕ) (hn : 0<n) : (n-1)^2<2^n := by
  have hlarge : ∀j : ℕ,4≤j → (j-1)^2<2^j := by
    intro j hj
    induction j,hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      simp only [Nat.add_sub_cancel,pow_succ]
      have hsub : j-1+1=j := by omega
      have hmul := Nat.mul_le_mul_left j hj
      nlinarith
  by_cases h4 : 4≤n
  · exact hlarge n h4
  · interval_cases n <;> norm_num at *

theorem finiteField_card_large_of_residue_degree
    {F : Type*} [Field F] [Finite F]
    (p f n : ℕ) (hp : Nat.Prime p) (hn : 0<n)
    (hcard : Nat.card F=p^f) (hfn : n≤f) :
    (n-1)^2<Nat.card F := by
  rw [hcard]
  exact (square_pred_lt_two_pow n hn).trans_le
    ((Nat.pow_le_pow_left hp.two_le n).trans (Nat.pow_le_pow_right hp.pos hfn))

theorem finiteField_power_closure_of_residue_degree
    {F : Type*} [Field F] [Finite F]
    (p f n : ℕ) (hp : Nat.Prime p) (hn : 0<n)
    (hcard : Nat.card F=p^f) (hfn : n≤f) (a : F) :
    a∈AddSubgroup.closure (Set.range (fun x : F => x^n)) :=
  finiteField_mem_power_closure_of_card_large n hn
    (finiteField_card_large_of_residue_degree p f n hp hn hcard hfn) a

theorem finiteField_short_power_list_of_residue_degree
    {F : Type*} [Field F] [Finite F]
    (p f n : ℕ) (hp : Nat.Prime p) (hn : 0<n)
    (hcard : Nat.card F=p^f) (hfn : n≤f) (a : F) :
    ∃l : List F,l.length≤n ∧ localPowerListSum n l=a :=
  finiteField_short_power_list_of_card_large n hn
    (finiteField_card_large_of_residue_degree p f n hp hn hcard hfn) a

#print axioms square_pred_lt_two_pow
#print axioms finiteField_card_large_of_residue_degree
#print axioms finiteField_power_closure_of_residue_degree
#print axioms finiteField_short_power_list_of_residue_degree
end WaringSiegel.WSL4

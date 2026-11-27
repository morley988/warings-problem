import WaringLinear.BadFibreSelection
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.PSeries

/-! # Removing the coprimality cutoff by distinct proper divisor states -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear

private theorem primes_product_dvd_iff (s : Finset ℕ) (n : ℕ)
    (hp : ∀ p∈s,p.Prime) : (∏ p∈s,p)∣n ↔ ∀p∈s,p∣n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hs ih =>
    have hp0 := hp p (Finset.mem_insert_self ..)
    have hps (q) (hq:q∈s) := hp q (Finset.mem_insert_of_mem hq)
    have hco : p.Coprime (∏q∈s,q) :=
      Nat.coprime_prod_right_iff.mpr (fun q hq =>
        (Nat.coprime_primes hp0 (hps q hq)).mpr (fun h => hs (h ▸ hq)))
    rw [Finset.prod_insert hs,Finset.forall_mem_insert,←ih hps]
    exact ⟨fun h => ⟨(dvd_mul_right ..).trans h,(dvd_mul_left ..).trans h⟩,
      fun h => hco.mul_dvd_of_dvd_of_dvd h.1 h.2⟩

/-- A large exceptional Fourier sum has a large child attached to an
actual divisor d>1. It is counted once in the full set of possible d,
independently of how many selected marked products contain it. -/
theorem select_large_divisor {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ℕ) (root : α→ℕ) (f : α→ℂ) (hp : ∀p∈s,p.Prime)
    (hbad : 2*‖∑n∈Finset.univ.filter (fun n => ∀p∈s,¬p∣root n),f n‖ < ‖∑ n,f n‖) :
    ∃ t⊆s,t.Nonempty ∧ 1<(∏p∈t,p) ∧
      ‖∑n,f n‖≤2*(2:ℝ)^s.card*‖∑n∈Finset.univ.filter (fun n => (∏p∈t,p)∣root n),f n‖ := by
  classical
  let S (p : ℕ) := Finset.univ.filter (fun n => p∣root n)
  have hc : (s.biUnion S)ᶜ=Finset.univ.filter (fun n => ∀p∈s,¬p∣root n) := by
    ext n
    simp [S]
  rw [←hc] at hbad
  obtain ⟨t,ht,hne,h⟩ := bad_fibre_selection s S f hbad
  have hts := Finset.mem_powerset.mp ht
  have hprime (p) (hm:p∈t) := hp p (hts hm)
  have he : t.inf S=Finset.univ.filter (fun n => (∏ p∈t,p)∣root n) := by
    ext n
    simp [Finset.mem_inf,S,primes_product_dvd_iff _ _ hprime]
  obtain ⟨p,hp'⟩ := hne
  have hprod : 0<(∏q∈t,q) := Finset.prod_pos (fun i hi => (hprime i hi).pos)
  have hsize : 1<∏q∈t,q :=
    (hprime p hp').one_lt.trans_le (Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem (fun q => q) hp'))
  rw [he] at h
  exact ⟨t,hts,⟨p,hp'⟩,hsize,h⟩

/-- The sum of all possible reciprocal divisor powers is bounded by the
same convergent zeta series for every state and scale. -/
theorem distinct_divisor_mass (s : Finset ℕ) (a : ℝ) (ha : 1<a) :
    (∑d∈s, ((d:ℝ)^a)⁻¹)≤∑' n:ℕ,((n:ℝ)^a)⁻¹ := by
  have hs := Real.summable_nat_rpow_inv.mpr ha
  exact hs.sum_le_tsum _ (fun n _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg _) _))

#print axioms select_large_divisor
#print axioms distinct_divisor_mass
end WaringLinear

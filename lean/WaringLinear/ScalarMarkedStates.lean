import WaringLinear.ExceptionalDivisors
import Mathlib.Analysis.Fourier.AddCircle

/-! # Actual rational Weyl sums on divisor-selected states -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear

abbrev ScalarTorus := AddCircle (1:ℝ)

def scalarPowerSum (s : Finset ℕ) (k : ℕ) (θ : ScalarTorus) : ℂ :=
  ∑ n∈s,fourier ((n^k:ℕ):ℤ) θ

def dividedState (s : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (s.filter (fun n => d∣n)).image (fun n => n/d)

private theorem scalar_dilated_phase (n d k : ℕ) (h : d∣n) (θ : ScalarTorus) :
    fourier ((n^k:ℕ):ℤ) θ = fourier (((n/d)^k:ℕ):ℤ) (d^k • θ) := by
  simp only [fourier_apply,natCast_zsmul]
  congr 2
  rw [←mul_smul,←mul_pow,Nat.div_mul_cancel h]

/-- Divisibility gives precisely one shortened root per selected root,
and the only change to the circle variable is multiplication by d^k. -/
theorem scalar_divide_state (s : Finset ℕ) (d k : ℕ) (θ : ScalarTorus) :
    scalarPowerSum (s.filter (fun n => d∣n)) k θ =
      scalarPowerSum (dividedState s d) k (d^k • θ) := by
  classical
  simp only [scalarPowerSum,dividedState]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    exact scalar_dilated_phase _ _ _ (Finset.mem_filter.mp hn).2 _
  · intro x hx y hy h
    exact (Nat.div_mul_cancel (Finset.mem_filter.mp hx).2).symm.trans
      ((congrArg (fun t => t*d) h).trans (Nat.div_mul_cancel (Finset.mem_filter.mp hy).2))

/-- Full parent decomposition for any marking of its roots by divisors.
The index set is finite and no multiplicity is introduced by division. -/
theorem scalar_parent_states (s marks : Finset ℕ) (m : ℕ→ℕ) (k : ℕ)
    (hm : ∀ n∈s,m n∈marks) (hd : ∀n∈s,m n∣n) (θ : ScalarTorus) :
    scalarPowerSum s k θ = ∑d∈marks,scalarPowerSum
      (dividedState (s.filter (fun n => m n=d)) d) k (d^k • θ) := by
  let f (n:ℕ) := fourier ((n^k:ℕ):ℤ) θ
  change (∑n∈s,f n)=_
  rw [←Finset.sum_fiberwise_of_maps_to (s:=s) (t:=marks) (g:=m) hm f]
  apply Finset.sum_congr rfl
  intro d _
  rw [←scalar_divide_state]
  have he : (s.filter (fun n => m n=d)).filter (fun n => d∣n)=s.filter (fun n => m n=d) := by
    ext n
    simp only [Finset.mem_filter,and_iff_left_iff_imp]
    rintro ⟨hs,hd'⟩
    exact hd' ▸ hd _ hs
  rw [he]
  rfl

private theorem subtype_filter_sum (s:Finset ℕ) (f:ℕ→ℂ) (p:ℕ→Prop) [DecidablePred p] :
    (∑ n∈Finset.univ.filter (fun i:s => p i),f n) = ∑n∈s.filter p,f n := by
  rw [Finset.sum_filter,Finset.sum_filter]
  exact Finset.sum_coe_sort s (fun n => if p n then f n else 0)

/-- The exceptional inclusion--exclusion branch is a genuine shorter
positive-root Fourier sum at d^k times the original circle variable. -/
theorem scalar_exceptional_child (s P : Finset ℕ) (k : ℕ) (θ : ScalarTorus)
    (hp : ∀p∈P,p.Prime)
    (hbad : 2*‖scalarPowerSum (s.filter (fun n => ∀p∈P,¬p∣n)) k θ‖ < ‖scalarPowerSum s k θ‖) :
    ∃t⊆P,t.Nonempty ∧ 1<(∏p∈t,p) ∧
      ‖scalarPowerSum s k θ‖ ≤ 2*(2:ℝ)^P.card*
        ‖scalarPowerSum (dividedState s (∏p∈t,p)) k ((∏p∈t,p)^k • θ)‖ := by
  classical
  let f (n:ℕ) := fourier ((n^k:ℕ):ℤ) θ
  have hf : (∑n:s,f n)=scalarPowerSum s k θ := Finset.sum_coe_sort s _
  obtain ⟨t,ht,hne,hd,h⟩ := select_large_divisor P (fun n:s => n.val)
    (fun n => f n) hp (by
      change 2*‖∑ n∈Finset.univ.filter (fun i:s => ∀p∈P,¬p∣i.val),f n‖<‖∑n:s,f n‖
      rw [subtype_filter_sum s f (fun n => ∀p∈P,¬p∣n),hf]
      exact hbad)
  change ‖∑n:s,f n‖≤2*(2:ℝ)^P.card*‖∑n∈Finset.univ.filter (fun i:s => (∏p∈t,p)∣i.val),f n‖ at h
  rw [hf,subtype_filter_sum s f (fun n => (∏p∈t,p)∣n)] at h
  have he := scalar_divide_state s (∏p∈t,p) k θ
  change scalarPowerSum (s.filter _) k θ=_ at he
  refine ⟨t,ht,hne,hd,?_⟩
  rw [←he]
  exact h

#print axioms scalar_parent_states
#print axioms scalar_exceptional_child
end WaringLinear

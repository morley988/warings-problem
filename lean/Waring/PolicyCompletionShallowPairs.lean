import Waring.PolicyCompletionShallowArithmetic
import Waring.PolicyCompletionLinearRootSampling

/-!
# Weighted primitive power-congruence pairs

The genuine divided-difference residue bound is summed over the endpoint
gap. Gcd classes of that gap preserve the full real error taper and cost
only the explicit divisor and harmonic factors.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowPairs
open PolicyCompletionShallowArithmetic PolicyCompletionLinearRootSampling

def primitiveShiftSet (d q l N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n=>Nat.Coprime n (n+l) ∧ q∣(n+l)^d-n^d

theorem primitiveShiftSet_card_le {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀q N l : ℕ,0<q→0<l→l≤N→
      ((primitiveShiftSet d q l N).card : ℝ)≤
        C*((N*q : ℕ) : ℝ)^ε*((N : ℝ)*(q.gcd l : ℝ)/q+1) := by
  obtain ⟨C,hC,hfiber⟩ := power_difference_fiber_card_le_rpow hd hε
  refine ⟨C,hC,?_⟩
  intro q N l hq hl hlN
  let A := (Finset.Icc 1 N).filter fun n=>Nat.Coprime n (n+l)
  have hA : A⊆Finset.Icc 1 N := Finset.filter_subset _ _
  have hcop : ∀n∈A,Nat.Coprime n (n+l) := fun n hn=>(Finset.mem_filter.mp hn).2
  have hset : A.filter (fun n=>q∣(n+l)^d-n^d)=primitiveShiftSet d q l N := by
    ext n
    simp [A,primitiveShiftSet,and_assoc]
  have hb := hfiber q l N hq hl A hA hcop
  rw [hset] at hb
  have hg : 0<q.gcd l := Nat.gcd_pos_of_pos_left _ hq
  have hgR : (0 : ℝ)<q.gcd l := by exact_mod_cast hg
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hquot : ((q/q.gcd l : ℕ) : ℝ)=(q : ℝ)/(q.gcd l : ℝ) := by
    apply (eq_div_iff hgR.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left q l)
  have hid : (N : ℝ)/((q/q.gcd l : ℕ) : ℝ)=(N : ℝ)*(q.gcd l : ℝ)/q := by
    rw [hquot]
    field_simp
  have hsize : ((l*(q/q.gcd l) : ℕ) : ℝ)≤((N*q : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul hlN (Nat.div_le_self _ _)
  rw [hid] at hb
  calc
    _ ≤ C*((N : ℝ)*(q.gcd l : ℝ)/q+1)*((l*(q/q.gcd l) : ℕ) : ℝ)^ε := hb
    _ ≤ C*((N : ℝ)*(q.gcd l : ℝ)/q+1)*((N*q : ℕ) : ℝ)^ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hsize hε.le) (by positivity)
    _ = _ := by ring

theorem gcd_linear_sum (q N : ℕ) (hq : 0<q) (hN : 0<N) {B : ℝ} (hB : 0≤B) :
    (∑l∈Finset.Icc 1 N,(q.gcd l : ℝ)/(1+B*(l : ℝ)))≤
      (q.divisors.card : ℝ)*(N : ℝ)/(1+B*(N : ℝ))*(1+Real.log N) := by
  let weight : ℕ→ℕ→ℝ := fun u l=>if u∣l then (u : ℝ)/(1+B*(l : ℝ)) else 0
  have hw : ∀u l,0≤weight u l := by intro u l; dsimp [weight]; split_ifs <;> positivity
  have hp (l : ℕ) : (q.gcd l : ℝ)/(1+B*(l : ℝ))≤∑u∈q.divisors,weight u l := by
    have hu : q.gcd l∈q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hq.ne'⟩
    have hh := Finset.single_le_sum (fun u _=>hw u l) hu
    simpa only [weight,if_pos (Nat.gcd_dvd_right q l)] using hh
  have hc (u : ℕ) : (∑l∈Finset.Icc 1 N,weight u l)=linearClass N u 1 B 1 := by
    simp only [weight,← Finset.sum_filter,linearClass,Real.rpow_one]
  calc
    _ ≤ ∑l∈Finset.Icc 1 N,∑u∈q.divisors,weight u l := Finset.sum_le_sum fun l _=>hp l
    _ = ∑u∈q.divisors,linearClass N u 1 B 1 := by rw [Finset.sum_comm]; simp_rw [hc]
    _ ≤ ∑_u∈q.divisors,(N : ℝ)/(1+B*(N : ℝ))*(1+Real.log N) := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [Real.rpow_one] using
        linearClass_bound hN (Nat.pos_of_mem_divisors hu) (by norm_num : (0 : ℝ)<1)
          hB (by norm_num : (0 : ℝ)≤1) (by norm_num : (1 : ℝ)≤1)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The full positive-gap sum, with the source main term and its boundary
term, for actual primitive power-congruence solutions. -/
theorem primitive_pair_weighted_bound {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀q N : ℕ,0<q→0<N→∀B : ℝ,0≤B→
      (∑l∈Finset.Icc 1 N,((primitiveShiftSet d q l N).card : ℝ)/(1+B*(l : ℝ)))≤
        C*((N*q : ℕ) : ℝ)^ε*
          (((N : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log N))/(q*(1+B*(N : ℝ)))+N) := by
  obtain ⟨C,hC,hcount⟩ := primitiveShiftSet_card_le hd hε
  refine ⟨C,hC,?_⟩
  intro q N hq hN B hB
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hden (l : ℕ) : 0<1+B*(l : ℝ) := by positivity
  have htrivial : (∑l∈Finset.Icc 1 N,1/(1+B*(l : ℝ)))≤(N : ℝ) := by
    calc
      _ ≤ ∑_l∈Finset.Icc 1 N,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro l hl
        exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1)
          (le_add_of_nonneg_right (by positivity))).trans_eq (by norm_num)
      _ = _ := by simp
  have hmain := gcd_linear_sum q N hq hN hB
  calc
    _ ≤ ∑l∈Finset.Icc 1 N,
        (C*((N*q : ℕ) : ℝ)^ε*((N : ℝ)*(q.gcd l : ℝ)/q+1))/(1+B*(l : ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact div_le_div_of_nonneg_right
        (hcount q N l hq (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2) (hden l).le
    _ = C*((N*q : ℕ) : ℝ)^ε*
        ((N : ℝ)/q*(∑l∈Finset.Icc 1 N,(q.gcd l : ℝ)/(1+B*(l : ℝ)))+
          ∑l∈Finset.Icc 1 N,1/(1+B*(l : ℝ))) := by
      simp only [mul_add,Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ ≤ C*((N*q : ℕ) : ℝ)^ε*
        ((N : ℝ)/q*((q.divisors.card : ℝ)*(N : ℝ)/(1+B*(N : ℝ))*(1+Real.log N))+(N : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity)) htrivial)
        (by positivity)
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

#print axioms primitiveShiftSet_card_le
#print axioms primitive_pair_weighted_bound
end Waring.PolicyCompletionShallowPairs

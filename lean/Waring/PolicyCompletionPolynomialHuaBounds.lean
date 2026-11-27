import Waring.PolicyCompletionPolynomialRecursion
import Waring.PolicyCompletionPolynomialPrime

/-! # Uniform branch constants and real-power bounds for Hua recursion -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialHuaBounds
open Polynomial PolicyCompletionPolynomialRecursion PolicyCompletionPolynomialContent
  PolicyCompletionPolynomialResidues PolicyCompletionPolynomialPrime

def criticalResidues (p : ℕ) (D : Polynomial ℤ) : Finset ℕ :=
  (Finset.range p).filter (fun r : ℕ => (D.map (Int.castRingHom (ZMod p))).eval (r : ZMod p)=0)

def criticalMultiplicity (p : ℕ) (D : Polynomial ℤ) (r : ℕ) : ℕ :=
  (D.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)

theorem criticalMultiplicity_pos {p : ℕ} [Fact p.Prime]
    (D : Polynomial ℤ) (hD : PrimitiveAt p D) {r : ℕ} (hr : r ∈ criticalResidues p D) :
    0 < criticalMultiplicity p D r := by
  apply (Polynomial.rootMultiplicity_pos (primitiveAt_map_ne_zero hD)).mpr
  exact (Finset.mem_filter.mp hr).2

theorem criticalMultiplicity_sum_le {p : ℕ} [Fact p.Prime] (D : Polynomial ℤ) :
    (∑ r ∈ criticalResidues p D,criticalMultiplicity p D r) ≤
      (D.map (Int.castRingHom (ZMod p))).natDegree := by
  classical
  let E := D.map (Int.castRingHom (ZMod p))
  by_cases hE : E=0
  · simp [criticalMultiplicity,E,hE]
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) (criticalResidues p D) := by
    intro a ha b hb he
    have hal := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hbl := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt hal,ZMod.val_natCast_of_lt hbl] using hv
  have hsubset : (criticalResidues p D).image (fun r : ℕ => (r : ZMod p)) ⊆ E.roots.toFinset := by
    intro a ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ha
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hE).mpr
    exact (Finset.mem_filter.mp hr).2
  calc
    _ = ∑ a ∈ (criticalResidues p D).image (fun r : ℕ => (r : ZMod p)),E.rootMultiplicity a := by
      rw [Finset.sum_image hinj]
      rfl
    _ ≤ ∑ a ∈ E.roots.toFinset,E.rootMultiplicity a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)
    _ ≤ E.natDegree := sum_rootMultiplicity_le_degree E

theorem sum_pow_le_pow_sum {ι : Type*} (S : Finset ι) (ν : ι → ℕ)
    {K : ℝ} (hK : 2 ≤ K) (hν : ∀ x ∈ S,1 ≤ ν x) :
    (∑ x ∈ S,K^(ν x)) ≤ K^(∑ x ∈ S,ν x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hνa := hν a (Finset.mem_insert_self _ _)
      have hνS : ∀ x ∈ S,1 ≤ ν x := fun x hx => hν x (Finset.mem_insert_of_mem hx)
      by_cases hS : S=∅
      · simp [hS]
      have hsum : 1 ≤ ∑ x ∈ S,ν x := by
        obtain ⟨b,hb⟩ := Finset.nonempty_iff_ne_empty.mpr hS
        exact (hνS b hb).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
      have haK : 2 ≤ K^(ν a) := hK.trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ K) hνa)
      have hSK : 2 ≤ K^(∑ x ∈ S,ν x) := hK.trans (by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ K) hsum)
      rw [Finset.sum_insert ha,Finset.sum_insert ha,pow_add]
      have hIH := ih hνS
      nlinarith [mul_nonneg (sub_nonneg.mpr haK) (sub_nonneg.mpr hSK)]

theorem sum_branch_constants_le {ι : Type*} (S : Finset ι) (ν : ι → ℕ)
    {K : ℝ} (hK : 2 ≤ K) (hν : ∀ x ∈ S,1 ≤ ν x) {e : ℕ}
    (he : (∑ x ∈ S,ν x) ≤ e) :
    (∑ x ∈ S,K^(ν x+1)) ≤ K^(e+1) := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  exact (sum_pow_le_pow_sum S ν hK hν).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ K) he)

def huaExponent (m t e : ℕ) : ℝ :=
  (m : ℝ)-((m : ℝ)-(t : ℝ))/((e : ℝ)+1)

theorem norm_integerPolynomialSum_le (q : ℕ) [NeZero q] (f : Polynomial ℤ) :
    ‖integerPolynomialSum q f‖ ≤ q := by
  unfold integerPolynomialSum PolicyCompletionPolynomialStationary.completePolynomialSum
  calc
    _ ≤ ∑ _x : ZMod q,(1 : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro x hx
      simp [ZMod.stdAddChar_apply]
    _ = _ := by simp [ZMod.card]

theorem norm_residuePolynomialSum_le {p : ℕ} [Fact p.Prime]
    (m r : ℕ) (f : Polynomial ℤ) :
    ‖residuePolynomialSum p m r f‖ ≤ (p : ℝ)^(m-1) := by
  unfold residuePolynomialSum
  calc
    _ ≤ ∑ _y ∈ Finset.range (p^(m-1)),(1 : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      simp [ZMod.stdAddChar_apply]
    _ = _ := by simp

/-- The small-prime range is absorbed by a fixed degree constant, because
p^t and p are both at most D. -/
theorem small_prime_trivial_bound {p D m t e : ℕ} (hp : 1 ≤ p)
    (hpD : p ≤ D) (hpt : p^t ≤ D) (hm : m ≤ 2*t+1) :
    (p : ℝ)^m ≤ (huaConstant D)^(e+1)*(p : ℝ)^(huaExponent m t e) := by
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpp : 0 < (p : ℝ) := zero_lt_one.trans_le hpr
  have hden : (0 : ℝ) < (e : ℝ)+1 := by positivity
  have hfrac : ((m : ℝ)-(t : ℝ))/((e : ℝ)+1) ≤ (t : ℝ)+1 := by
    apply (div_le_iff₀ hden).mpr
    have hm' : (m : ℝ) ≤ 2*(t : ℝ)+1 := by exact_mod_cast hm
    nlinarith [Nat.cast_nonneg (α := ℝ) e,Nat.cast_nonneg (α := ℝ) t]
  have hsmall : (p : ℝ)^(((m : ℝ)-(t : ℝ))/((e : ℝ)+1)) ≤ huaConstant D := by
    calc
      _ ≤ (p : ℝ)^((t : ℝ)+1) := Real.rpow_le_rpow_of_exponent_le hpr hfrac
      _ = (p : ℝ)^t*(p : ℝ) := by rw [Real.rpow_add hpp,Real.rpow_natCast,Real.rpow_one]
      _ ≤ (D : ℝ)^2 := by
        have hpt' : (p : ℝ)^t ≤ D := by exact_mod_cast hpt
        have hpd' : (p : ℝ) ≤ D := by exact_mod_cast hpD
        nlinarith [mul_le_mul hpt' hpd' (Nat.cast_nonneg p) (Nat.cast_nonneg D)]
      _ ≤ _ := huaConstant_ge_degree_square D
  have hK := huaConstant_ge_two D
  have hKpow : huaConstant D ≤ (huaConstant D)^(e+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ huaConstant D)
      (show 1 ≤ e+1 by omega)
  calc
    _ = (p : ℝ)^(((m : ℝ)-(t : ℝ))/((e : ℝ)+1))*(p : ℝ)^(huaExponent m t e) := by
      rw [← Real.rpow_add hpp]
      have he : ((m : ℝ)-(t : ℝ))/((e : ℝ)+1)+huaExponent m t e=(m : ℝ) := by
        unfold huaExponent
        ring
      rw [he,Real.rpow_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hsmall.trans hKpow) (by positivity)

/-- The exponent comparison in one actual normalized branch. -/
theorem branch_exponent_le {m t σ τ ν e : ℕ} (hσ : σ ≤ m) (hσpos : 1 ≤ σ)
    (hcontent : σ+τ ≤ t+1+ν) (he : e ≤ ν) (hmt : τ ≤ m-σ) :
    ((σ-1 : ℕ) : ℝ)+huaExponent (m-σ) τ e ≤ huaExponent m t ν := by
  have hden : (0 : ℝ) < (e : ℝ)+1 := by positivity
  have hdenν : (0 : ℝ) < (ν : ℝ)+1 := by positivity
  have hmcast : ((m-σ : ℕ) : ℝ)=(m : ℝ)-(σ : ℝ) := Nat.cast_sub hσ
  have hσcast : ((σ-1 : ℕ) : ℝ)=(σ : ℝ)-1 := by
    rw [Nat.cast_sub hσpos,Nat.cast_one]
  have hcontent' : (σ : ℝ)+(τ : ℝ) ≤ (t : ℝ)+1+(ν : ℝ) := by exact_mod_cast hcontent
  have hnonneg : 0 ≤ ((m-σ : ℕ) : ℝ)-(τ : ℝ) := by
    have hh : (τ : ℝ) ≤ (m-σ : ℕ) := by exact_mod_cast hmt
    linarith
  have hdiv : (((m-σ : ℕ) : ℝ)-(τ : ℝ))/((ν : ℝ)+1) ≤
      (((m-σ : ℕ) : ℝ)-(τ : ℝ))/((e : ℝ)+1) :=
    div_le_div_of_nonneg_left hnonneg hden (by exact_mod_cast Nat.add_le_add_right he 1)
  have hh : ((m : ℝ)-(t : ℝ))/((ν : ℝ)+1) ≤
      1+((m : ℝ)-(σ : ℝ)-(τ : ℝ))/((ν : ℝ)+1) := by
    apply (div_le_iff₀ hdenν).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hdenν.ne']
    linarith
  unfold huaExponent
  rw [hmcast] at hdiv ⊢
  linarith

#print axioms sum_branch_constants_le
#print axioms small_prime_trivial_bound
end Waring.PolicyCompletionPolynomialHuaBounds

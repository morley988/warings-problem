import Waring.PolicyCompletionMultiplierHeight
import Waring.PolicyCompletionBinomialArithmetic

/-!
# The actual coprime divided-difference height sum

This composes the source rational-approximation argument with the proved
quotient residue count. Every finite divisibility fiber is discharged.
Only the displayed numerical box and separation ranges remain as premises.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBinomialHeight
open RationalHeight PolicyCompletionBinomialArithmetic PolicyCompletionMultiplierHeight

theorem natQuotient_real_bounds (d n l : ℕ) {M B : ℝ}
    (hM : 0≤M) (hMn : M≤(n : ℝ)) (hnB : ((n+l : ℕ) : ℝ)≤B) :
    (d : ℝ)*M^(d-1)≤(natQuotient d n l : ℝ) ∧
      (natQuotient d n l : ℝ)≤(d : ℝ)*B^(d-1) := by
  have hnat := natQuotient_bounds d n l
  constructor
  · calc
      _ ≤ (d : ℝ)*(n : ℝ)^(d-1) := by gcongr
      _ ≤ _ := by exact_mod_cast hnat.1
  · calc
      _ ≤ (d : ℝ)*((n+l : ℕ) : ℝ)^(d-1) := by exact_mod_cast hnat.2
      _ ≤ _ := by gcongr

/-- VW95 (4.7)--(4.10), as a finite actual divided-difference bound.
The arbitrary-small-power constant is uniform in the interval, shift,
phase, conductor, and every polynomial value. -/
theorem binomial_height_bound {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀l N : ℕ,0<l→∀A : Finset ℕ,
      A⊆Finset.Icc 1 N→(∀n∈A,Nat.Coprime n (n+l))→
      ∀V Z L U α a : ℝ,0<V→0<Z→0≤L→0<U→1≤V*U→0≤a→a≤1→
      (∀n∈A,L≤(natQuotient d n l : ℝ))→
      (∀n∈A,(natQuotient d n l : ℝ)≤U)→
      2*Z*Real.sqrt (V*U)/V<1→
      ∃r : ℚ,cost (V*U) α r=height (V*U) α ∧
        (∑n∈A,1/(height V (α*(natQuotient d n l : ℝ)))^a)≤
          (A.card : ℝ)/Z^a+
          2^a*C*((l*r.den : ℕ) : ℝ)^ε*(r.den.divisors.card : ℝ)*
            ((N : ℝ)/(sumCost (V*L) α r)^a+1) := by
  obtain ⟨C,hC,hfiber⟩ := natQuotient_fiber_card_le_rpow hd hε
  refine ⟨C,hC,?_⟩
  intro l N hl A hA hcop V Z L U α a hV hZ hL hU hVU ha ha1 hlo hup hsize
  obtain ⟨r,hr⟩ := exists_minimizer (mul_pos hV hU) α
  have hsmall := minimizer_small_cross hV hU hVU hZ.le r hr hsize
  let K := C*((l*r.den : ℕ) : ℝ)^ε
  have hK : 0≤K := by dsimp [K]; positivity
  have hcount : ∀q∈r.den.divisors,
      ((A.filter fun n=>q∣natQuotient d n l).card : ℝ)≤K*((N : ℝ)/q+1) := by
    intro q hq
    have hqpos := Nat.pos_of_mem_divisors hq
    have hqlt := Nat.le_of_dvd r.pos (Nat.dvd_of_mem_divisors hq)
    have hprod : ((l*q : ℕ) : ℝ)≤((l*r.den : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left l hqlt
    calc
      _ ≤ C*((N : ℝ)/q+1)*((l*q : ℕ) : ℝ)^ε := hfiber q l N hqpos hl A hA hcop
      _ ≤ C*((N : ℝ)/q+1)*((l*r.den : ℕ) : ℝ)^ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hprod hε.le) (by positivity)
      _ = K*((N : ℝ)/q+1) := by dsimp [K]; ring
  have hb := structured_reciprocal_bound A (fun n=>natQuotient d n l) r
    hV hZ hL ha ha1 (show (0 : ℝ)≤N by positivity) hK hlo hup hsmall hcount
  refine ⟨r,hr,?_⟩
  convert hb using 1 <;> dsimp [K] <;> ring

#print axioms binomial_height_bound
end Waring.PolicyCompletionBinomialHeight

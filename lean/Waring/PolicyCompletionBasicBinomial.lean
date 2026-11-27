import Waring.PolicyCompletionBasicGcd
import Waring.PolicyCompletionBinomialHeight
import Waring.DivisorBound

/-!
# The binomial stage on the original coefficient block

This places the exact gcd fibers on their physical ranges and discharges
the rational denominator and divisor losses uniformly. The sole size
condition is the displayed source separation inequality.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicBinomial
open RationalHeight PolicyCompletionBasicGcd PolicyCompletionBinomialArithmetic
open PolicyCompletionBinomialHeight

theorem nat_div_cast_le (N j : ℕ) (hj : 0<j) :
    ((N/j : ℕ) : ℝ)≤(N : ℝ)/j := by
  apply (le_div_iff₀ (by exact_mod_cast hj : (0 : ℝ)<j)).mpr
  exact_mod_cast Nat.div_mul_le_self N j

theorem weighted_divisor_loss {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : ℝ,1≤T→∀l q : ℕ,0<q→(l : ℝ)≤T→(q : ℝ)≤T→
      ((l*q : ℕ) : ℝ)^(ε/3)*(q.divisors.card : ℝ)≤C*T^ε := by
  obtain ⟨C,hC,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow (by linarith : 0<ε/3)
  refine ⟨C,hC,?_⟩
  intro T hT l q hq hl hqT
  have hprod : ((l*q : ℕ) : ℝ)≤T^2 := by
    push_cast
    nlinarith [mul_le_mul hl hqT (by positivity : (0 : ℝ)≤q) (by linarith : 0≤T)]
  calc
    _ ≤ (T^2)^(ε/3)*(C*T^(ε/3)) := by
      exact mul_le_mul (Real.rpow_le_rpow (by positivity) hprod (by linarith))
        (hdiv T hT q hq hqT) (by positivity) (by positivity)
    _ = C*T^ε := by
      rw [← Real.rpow_natCast_mul (by linarith : 0≤T)]
      rw [mul_left_comm,← Real.rpow_add (by linarith : 0<T)]
      congr 2
      norm_num
      ring

def denominatorScale (d N : ℕ) (V : ℝ) : ℝ := 2*d*V*(N : ℝ)^d

theorem denominatorScale_ge {d N : ℕ} (hd : 0<d) (hN : 0<N) {V : ℝ} (hV : 1≤V) :
    (1 : ℝ)≤denominatorScale d N V ∧ (N : ℝ)≤denominatorScale d N V := by
  have hdR : (1 : ℝ)≤d := by exact_mod_cast hd
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hp : (N : ℝ)≤(N : ℝ)^d := by
    calc
      _ = (N : ℝ)^1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hNR hd
  have hc : 1≤2*(d : ℝ)*V := by nlinarith
  have hlast : (N : ℝ)^d≤denominatorScale d N V := by
    exact le_mul_of_one_le_left (by positivity) hc
  exact ⟨hNR.trans (hp.trans hlast),hp.trans hlast⟩

/-- The actual gcd fiber after the first nontrivial source resummation.
Every finite residue count and every divisor factor has been proved. -/
theorem binomial_block_bound {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(A : Finset ℕ) (N : ℕ) (M V Y α : ℝ),
      0<N→0<M→1≤V→0<Y→(∀m∈A,M<(m : ℝ))→
      2*Y^3*Real.sqrt (V*((d : ℝ)*(N : ℝ)^(d-1)))/V<1→
      ∀j∈Finset.Icc 1 N,∀l∈Finset.Icc 1 (N/j),
      (∑n∈quotientDomain A N j l,
        1/(height V ((α*(j : ℝ)^d*l)*(natQuotient d n l : ℝ)))^(1/3 : ℝ))≤
      ((N : ℝ)/j)/Y+C*(denominatorScale d N V)^ε*
        (((N : ℝ)/j)/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1) := by
  obtain ⟨Cb,hCb,hbin⟩ := binomial_height_bound hd (by linarith : 0<ε/3)
  obtain ⟨Cd,hCd,hdiv⟩ := weighted_divisor_loss hε
  refine ⟨2^(1/3 : ℝ)*Cb*Cd,by positivity,?_⟩
  intro A N M V Y α hN hM hV hY hA hsize j hj l hl
  have hjB := Finset.mem_Icc.mp hj
  have hlB := Finset.mem_Icc.mp hl
  have hjp : 0<j := hjB.1
  have hlp : 0<l := hlB.1
  have hjR : (0 : ℝ)<j := by exact_mod_cast hjp
  have hjR1 : (1 : ℝ)≤j := by exact_mod_cast hjp
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hdR : (1 : ℝ)≤d := by exact_mod_cast hd
  have hVpos : 0<V := zero_lt_one.trans_le hV
  have hNj : 1≤(N : ℝ)/j := by
    apply (one_le_div hjR).mpr
    exact_mod_cast hjB.2
  have hNjN : (N : ℝ)/j≤N := div_le_self (by positivity) hjR1
  let L := (d : ℝ)*(M/j)^(d-1)
  let U := (d : ℝ)*((N : ℝ)/j)^(d-1)
  let B := quotientDomain A N j l
  have hL : 0<L := by dsimp [L]; positivity
  have hU1 : 1≤U := one_le_mul_of_one_le_of_one_le hdR (one_le_pow₀ hNj)
  have hU : 0<U := zero_lt_one.trans_le hU1
  have hVU : 1≤V*U := one_le_mul_of_one_le_of_one_le hV hU1
  have hB : B⊆Finset.Icc 1 (N/j) := Finset.filter_subset _ _
  have hcop : ∀n∈B,Nat.Coprime n (n+l) := fun _ hn=>(Finset.mem_filter.mp hn).2.1
  have hlohi (n : ℕ) (hn : n∈B) :
      L≤(natQuotient d n l : ℝ) ∧ (natQuotient d n l : ℝ)≤U := by
    have hh := quotientDomain_bounds hjp hA hn
    exact natQuotient_real_bounds d n l (by positivity) hh.1.le hh.2
  have hUupper : U≤(d : ℝ)*(N : ℝ)^(d-1) := by
    dsimp [U]
    gcongr
  have hsep : 2*Y^3*Real.sqrt (V*U)/V<1 := by
    apply lt_of_le_of_lt _ hsize
    apply div_le_div_of_nonneg_right _ hVpos.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hUupper hVpos.le)
  obtain ⟨r,hr,hbound⟩ := hbin l (N/j) hlp B hB hcop V (Y^3) L U
    (α*(j : ℝ)^d*l) (1/3) hVpos (by positivity) hL.le hU hVU
    (by norm_num) (by norm_num) (fun n hn=>(hlohi n hn).1)
    (fun n hn=>(hlohi n hn).2) hsep
  have hqVU : (r.den : ℝ)≤V*U := by
    calc
      _ ≤ cost (V*U) (α*(j : ℝ)^d*l) r := le_max_left _ _
      _ = height (V*U) (α*(j : ℝ)^d*l) := hr
      _ ≤ Real.sqrt (V*U) := height_le_sqrt hVU _
      _ ≤ V*U := by
        have hs := Real.sq_sqrt (mul_nonneg hVpos.le hU.le)
        have hs0 := Real.sqrt_nonneg (V*U)
        nlinarith [sq_nonneg (V*U-1)]
  have hT := denominatorScale_ge hd hN hV
  have hUT : V*U≤denominatorScale d N V := by
    have hpow : (N : ℝ)^(d-1)≤(N : ℝ)^d := pow_le_pow_right₀ hNR (by omega)
    calc
      _ ≤ V*((d : ℝ)*(N : ℝ)^(d-1)) := mul_le_mul_of_nonneg_left hUupper hVpos.le
      _ ≤ V*((d : ℝ)*(N : ℝ)^d) := by gcongr
      _ ≤ denominatorScale d N V := by
        have hp : 0≤V*((d : ℝ)*(N : ℝ)^d) := by positivity
        dsimp [denominatorScale]
        nlinarith
  have hlT : (l : ℝ)≤denominatorScale d N V := by
    have hlN : l≤N := hlB.2.trans (Nat.div_le_self N j)
    exact (show (l : ℝ)≤N by exact_mod_cast hlN).trans hT.2
  have hcoef := hdiv (denominatorScale d N V) hT.1 l r.den r.pos hlT (hqVU.trans hUT)
  have hTpos : 0<denominatorScale d N V := zero_lt_one.trans_le hT.1
  have hroot : (Y^3)^(1/3 : ℝ)=Y := by
    rw [← Real.rpow_natCast_mul hY.le]
    norm_num
  have hcard : (B.card : ℝ)≤(N : ℝ)/j := by
    have hh : B.card≤N/j := by simpa using Finset.card_le_card hB
    exact (show (B.card : ℝ)≤((N/j : ℕ) : ℝ) by exact_mod_cast hh).trans (nat_div_cast_le N j hjp)
  have hheight : height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l)≤
      sumCost (V*L) (α*(j : ℝ)^d*l) r := by
    apply (height_mono_conductor (mul_pos hVpos hL) ?_).trans
      ((height_le_cost _ _ r).trans (max_sum_cost_comparison (by positivity) _ r).1)
    dsimp [L]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (by positivity) hdR) hVpos.le
  have hsumPos : 0<sumCost (V*L) (α*(j : ℝ)^d*l) r := (height_pos _ _).trans_le hheight
  have hquot : ((N/j : ℕ) : ℝ)/(sumCost (V*L) (α*(j : ℝ)^d*l) r)^(1/3 : ℝ)+1≤
      ((N : ℝ)/j)/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1 := by
    apply add_le_add_right
    calc
      _ ≤ ((N : ℝ)/j)/(sumCost (V*L) (α*(j : ℝ)^d*l) r)^(1/3 : ℝ) :=
        div_le_div_of_nonneg_right (nat_div_cast_le N j hjp) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos (height_pos _ _) _)
        (Real.rpow_le_rpow (height_pos _ _).le hheight (by norm_num))
  rw [hroot] at hbound
  calc
    _ ≤ (B.card : ℝ)/Y+
      2^(1/3 : ℝ)*Cb*((l*r.den : ℕ) : ℝ)^(ε/3)*(r.den.divisors.card : ℝ)*
        (((N/j : ℕ) : ℝ)/(sumCost (V*L) (α*(j : ℝ)^d*l) r)^(1/3 : ℝ)+1) := hbound
    _ ≤ ((N : ℝ)/j)/Y+
      (2^(1/3 : ℝ)*Cb*(Cd*(denominatorScale d N V)^ε))*
        (((N : ℝ)/j)/(height (V*(M/j)^(d-1)) (α*(j : ℝ)^d*l))^(1/3 : ℝ)+1) := by
      apply add_le_add (div_le_div_of_nonneg_right hcard hY.le)
      apply mul_le_mul _ hquot (by positivity) (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcoef (show 0≤2^(1/3 : ℝ)*Cb by positivity)
    _ = _ := by ring

#print axioms binomial_block_bound
end Waring.PolicyCompletionBasicBinomial

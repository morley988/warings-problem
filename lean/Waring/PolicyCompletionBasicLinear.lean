import Waring.PolicyCompletionBasicBinomial
import Waring.PolicyCompletionLinearRootSampling

/-!
# The linear resummation on the source gcd ranges

The short part is handled directly when the gcd exceeds the height cutoff.
On the remaining range the source binomial separation condition already
implies the required linear separation. Integer rounding and the uniform
divisor loss are both included in the bound.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicLinear
open RationalHeight PolicyCompletionBasicBinomial PolicyCompletionLinearRootSampling

theorem separation_iff_square {V U Z : ℝ} (hV : 0<V) (hU : 0≤U) (hZ : 0≤Z) :
    2*Z*Real.sqrt (V*U)/V<1 ↔ 4*Z^2*U<V := by
  have hx : 0≤2*Z*Real.sqrt (V*U) := by positivity
  have hid : (2*Z*Real.sqrt (V*U))^2=V*(4*Z^2*U) := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hV.le hU)]
    ring
  rw [div_lt_one hV,← sq_lt_sq₀ hx hV.le,hid]
  simpa only [pow_two] using
    (mul_lt_mul_left hV : V*(4*Z^2*U)<V*V ↔ 4*Z^2*U<V)

theorem quotient_ceiling_bounds {N j : ℕ} (hj : 0<j) (hjN : j≤N) :
    (N : ℝ)/j<((N/j+1 : ℕ) : ℝ) ∧
      ((N/j+1 : ℕ) : ℝ)≤2*(N : ℝ)/j := by
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj
  have hNj : 1≤N/j := (Nat.le_div_iff_mul_le hj).mpr (by simpa using hjN)
  constructor
  · apply (div_lt_iff₀ hjR).mpr
    exact_mod_cast (by simpa [mul_comm] using Nat.lt_mul_div_succ N hj)
  · have hh : N/j+1≤2*(N/j) := by omega
    calc
      _ ≤ 2*((N/j : ℕ) : ℝ) := by exact_mod_cast hh
      _ ≤ 2*((N : ℝ)/j) := mul_le_mul_of_nonneg_left (nat_div_cast_le N j hj) (by norm_num)
      _ = _ := by ring

/-- The actual linear-shift sum needed after the binomial quotient stage. -/
theorem linear_block_bound {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀d N : ℕ,2≤d→0<N→∀M V Y α : ℝ,
      1≤M→M≤N→1≤V→0<Y→Y≤M→
      2*Y^3*Real.sqrt (V*((d : ℝ)*(N : ℝ)^(d-1)))/V<1→
      ∀j∈Finset.Icc 1 N,
      (∑l∈Finset.Icc 1 (N/j),
        1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ))≤
      2*(N : ℝ)/Y+C*(denominatorScale d N V)^ε*
        ((2*(N : ℝ)/j)/(height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))*
          (1+Real.log (2*(N : ℝ))) := by
  obtain ⟨C,hC,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hε
  refine ⟨2^(1/3 : ℝ)*C,by positivity,?_⟩
  intro d N hd hN M V Y α hM hMN hV hY hYM hsize j hj
  have hjB := Finset.mem_Icc.mp hj
  have hjp : 0<j := hjB.1
  have hjR : (0 : ℝ)<j := by exact_mod_cast hjp
  have hjR1 : (1 : ℝ)≤j := by exact_mod_cast hjp
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hdR : (1 : ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  have hMp : 0<M := zero_lt_one.trans_le hM
  have hVp : 0<V := zero_lt_one.trans_le hV
  have hscale := denominatorScale_ge (by omega : 0<d) hN hV
  have hscalep : 0<denominatorScale d N V := zero_lt_one.trans_le hscale.1
  have hlog : 0≤1+Real.log (2*(N : ℝ)) := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    linarith
  have hheightPos : 0<height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d) := height_pos _ _
  by_cases hjY : (j : ℝ)≤Y
  · let T := N/j+1
    let W := V*(M/j)^(d-1)
    let Z := (Y/(j : ℝ))^3
    have hTpos : 0<T := Nat.succ_pos _
    have hTR : (1 : ℝ)≤T := by exact_mod_cast hTpos
    have hround := quotient_ceiling_bounds hjp hjB.2
    have hTupper : (T : ℝ)≤2*(N : ℝ)/j := hround.2
    have hTupper' : (T : ℝ)≤2*(N : ℝ) := hTupper.trans (div_le_self (by positivity) hjR1)
    have hTlower : M/(j : ℝ)≤T :=
      (div_le_div_of_nonneg_right hMN hjR.le).trans hround.1.le
    have hMj : 1≤M/(j : ℝ) := (one_le_div hjR).mpr (hjY.trans hYM)
    have hWlarge : V≤W := le_mul_of_one_le_right hVp.le (one_le_pow₀ hMj)
    have hW : 0<W := hVp.trans_le hWlarge
    have hWT : 1≤W*T := one_le_mul_of_one_le_of_one_le (hV.trans hWlarge) hTR
    have hZ : 0<Z := by dsimp [Z]; positivity
    have hZupper : Z≤Y^3 := by
      exact pow_le_pow_left₀ (by positivity) (div_le_self hY.le hjR1) _
    have hNpower : (N : ℝ)≤(N : ℝ)^(d-1) := by
      calc
        _ = (N : ℝ)^1 := by ring
        _ ≤ _ := pow_le_pow_right₀ hNR (by omega)
    have hTsource : (T : ℝ)≤(d : ℝ)*(N : ℝ)^(d-1) := by
      calc
        _ ≤ 2*(N : ℝ) := hTupper'
        _ ≤ 2*(N : ℝ)^(d-1) := by gcongr
        _ ≤ _ := by gcongr; exact_mod_cast hd
    have hsep : 2*Z*Real.sqrt (W*T)/W<1 := by
      apply (separation_iff_square hW (by positivity) hZ.le).mpr
      calc
        _ ≤ 4*(Y^3)^2*((d : ℝ)*(N : ℝ)^(d-1)) := by gcongr
        _ < V := (separation_iff_square hVp (by positivity) (by positivity)).mp hsize
        _ ≤ W := hWlarge
    obtain ⟨r,hr,hbound⟩ := linear_reciprocal_root_bound T hTpos hW hWT hZ
      (by norm_num : (0 : ℝ)≤1/3) (by norm_num) (α := α*(j : ℝ)^d) hsep
    have hWupper : W≤V*(N : ℝ)^(d-1) := by
      dsimp [W]
      apply mul_le_mul_of_nonneg_left _ hVp.le
      exact pow_le_pow_left₀ (by positivity)
        ((div_le_self hMp.le hjR1).trans hMN) _
    have hWTscale : W*T≤denominatorScale d N V := by
      calc
        _ ≤ (V*(N : ℝ)^(d-1))*(2*(N : ℝ)) :=
          mul_le_mul hWupper hTupper' (by positivity) (by positivity)
        _ = 2*V*(N : ℝ)^d := by
          conv_rhs => rw [show d=(d-1)+1 by omega,pow_succ]
          ring
        _ ≤ denominatorScale d N V := by
          have hh := mul_le_mul_of_nonneg_right hdR (show 0≤2*V*(N : ℝ)^d by positivity)
          dsimp [denominatorScale]
          nlinarith only [hh]
    have hq : (r.den : ℝ)≤denominatorScale d N V := by
      calc
        _ ≤ cost (W*T) (α*(j : ℝ)^d) r := le_max_left _ _
        _ = height (W*T) (α*(j : ℝ)^d) := hr
        _ ≤ Real.sqrt (W*T) := height_le_sqrt hWT _
        _ ≤ W*T := by
          have hs := Real.sq_sqrt (show 0≤W*(T : ℝ) by positivity)
          have hs0 := Real.sqrt_nonneg (W*T)
          nlinarith [sq_nonneg (W*T-1)]
        _ ≤ _ := hWTscale
    have hdivisor := hdiv (denominatorScale d N V) hscale.1 r.den r.pos hq
    have hconductor : V*M^d/(j : ℝ)^d≤W*T := by
      calc
        _ = V*(M/j)^d := by rw [div_pow]; ring
        _ = V*(M/j)^(d-1)*(M/j) := by
          conv_lhs => rw [show d=(d-1)+1 by omega,pow_succ]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hTlower (by positivity)
    have hheight : height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d)≤
        height (W*T) (α*(j : ℝ)^d) :=
      height_mono_conductor (by positivity) hconductor
    have hroot : Z^(1/3 : ℝ)=Y/j := by
      dsimp [Z]
      rw [← Real.rpow_natCast_mul (by positivity : 0≤Y/(j : ℝ))]
      norm_num
    have hshort : (T : ℝ)/Z^(1/3 : ℝ)≤2*(N : ℝ)/Y := by
      rw [hroot]
      calc
        _ ≤ (2*(N : ℝ)/j)/(Y/j) := div_le_div_of_nonneg_right hTupper (by positivity)
        _ = _ := by field_simp
    have hquot : (T : ℝ)/(height (W*T) (α*(j : ℝ)^d))^(1/3 : ℝ)≤
        (2*(N : ℝ)/j)/(height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ) := by
      calc
        _ ≤ (2*(N : ℝ)/j)/(height (W*T) (α*(j : ℝ)^d))^(1/3 : ℝ) :=
          div_le_div_of_nonneg_right hTupper (Real.rpow_pos_of_pos (height_pos _ _) _).le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos hheightPos _) (Real.rpow_le_rpow hheightPos.le hheight (by norm_num))
    have hlogT : 0≤1+Real.log (T : ℝ) := by have := Real.log_nonneg hTR; linarith
    have hlogle : 1+Real.log (T : ℝ)≤1+Real.log (2*(N : ℝ)) := by
      exact add_le_add_left (Real.log_le_log (by positivity) hTupper') _
    calc
      _ ≤ ∑l∈Finset.Icc 1 T,1/(height W ((α*(j : ℝ)^d)*l))^(1/3 : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by dsimp [T]; omega))
        intro l _ _
        exact (one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)).le
      _ ≤ (T : ℝ)/Z^(1/3 : ℝ)+2^(1/3 : ℝ)*(r.den.divisors.card : ℝ)*
          ((T : ℝ)/(height (W*T) (α*(j : ℝ)^d))^(1/3 : ℝ))*(1+Real.log T) := hbound
      _ ≤ 2*(N : ℝ)/Y+(2^(1/3 : ℝ)*(C*(denominatorScale d N V)^ε))*
          ((2*(N : ℝ)/j)/(height (V*M^d/(j : ℝ)^d) (α*(j : ℝ)^d))^(1/3 : ℝ))*
            (1+Real.log (2*(N : ℝ))) := by
        apply add_le_add hshort
        apply mul_le_mul _ hlogle hlogT (by positivity)
        apply mul_le_mul _ hquot (by exact (div_nonneg (by positivity) (Real.rpow_pos_of_pos (height_pos _ _) _).le)) (by positivity)
        exact mul_le_mul_of_nonneg_left hdivisor (by positivity)
      _ = _ := by ring
  · have hjY' : Y≤(j : ℝ) := (lt_of_not_ge hjY).le
    have hpoint (l : ℕ) :
        1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ)≤1 := by
      have hh := Real.one_le_rpow
        (one_le_height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l)) (by norm_num : (0 : ℝ)≤1/3)
      simpa using one_div_le_one_div_of_le zero_lt_one hh
    have htrivial :
        (∑l∈Finset.Icc 1 (N/j),1/(height (V*(M/j)^(d-1)) ((α*(j : ℝ)^d)*l))^(1/3 : ℝ))≤
          2*(N : ℝ)/Y := by
      calc
        _ ≤ ∑_l∈Finset.Icc 1 (N/j),(1 : ℝ) := Finset.sum_le_sum fun l _=>hpoint l
        _ = ((N/j : ℕ) : ℝ) := by simp
        _ ≤ (N : ℝ)/j := nat_div_cast_le N j hjp
        _ ≤ (N : ℝ)/Y := div_le_div_of_nonneg_left (by positivity) hY hjY'
        _ ≤ 2*((N : ℝ)/Y) := by
          have := div_nonneg (show (0 : ℝ)≤N by positivity) hY.le
          linarith
        _ = _ := by ring
    exact htrivial.trans (le_add_of_nonneg_right (by positivity))

#print axioms linear_block_bound
end Waring.PolicyCompletionBasicLinear

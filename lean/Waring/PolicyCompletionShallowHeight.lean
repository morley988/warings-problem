import Waring.PolicyCompletionShallowUniformBlock
import Waring.PolicyCompletionShallowActual

/-!
# Full common-height bound for the divisible shallow coefficient kernel

The actual gcd blocks are summed, the joint cubic/power denominator
estimate is applied, and its common rational cost is compared to the
intrinsic height of the original coefficient phase.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowHeight
open RationalHeight PolicyCompletionShallowActual PolicyCompletionShallowBlock
open PolicyCompletionShallowUniformBlock PolicyCompletionShallowClasses

theorem sum_scaled_grid (N H : ℕ) (K A B : ℝ) (f : ℕ→ℕ→ℝ) :
    (∑g∈Finset.Icc 1 N,∑h∈Finset.Icc 1 H,K*(A*(1/(g : ℝ)^2)*f g h+B/(g : ℝ)))=
      K*(A*(∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*∑h∈Finset.Icc 1 H,f g h)+
        (H : ℝ)*B*(∑g∈Finset.Icc 1 N,1/(g : ℝ))) := by
  have hinner (g : ℕ) :
      (∑h∈Finset.Icc 1 H,K*(A*(1/(g : ℝ)^2)*f g h+B/(g : ℝ)))=
        K*(A*(1/(g : ℝ)^2)*(∑h∈Finset.Icc 1 H,f g h)+(H : ℝ)*B/(g : ℝ)) := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  congr 1
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    ring

set_option maxHeartbeats 800000 in
theorem divisible_positive_height_bound {k : ℕ} (hk : 3≤k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀A : Finset ℕ,∀H N J : ℕ,0<H→0<N→
      (A⊆Finset.Icc 1 N)→∀M : ℝ,0≤M→M≤N→(∀m∈A,M<(m : ℝ))→
      ∀r : ℚ,∀α : ℝ,2*((H^3*N^(2*k) : ℕ) : ℝ)*error α r≤1→
      divisiblePositiveKernel A k H J r α≤
        C*(J : ℝ)*(2*(N : ℝ)*r.den)^ε*
          (((N : ℝ)^2*(r.den.divisors.card : ℝ)^3*H*(1+Real.log (2*(N : ℝ)))*(1+Real.log H))/
            (height ((H : ℝ)^3*J*M^(2*k)) α)^(1/(k : ℝ))+
            (H : ℝ)*N*(1+Real.log N)) := by
  obtain ⟨C,hC,hblock⟩ := uniform_divisible_gcd_block (by omega : 0<k) hε
  refine ⟨2*C,by positivity,?_⟩
  intro A H N J hH hN hA M hM hMN hlow r α herr
  let B := (J : ℝ)*|α-(r : ℝ)| *M^(2*k)
  let V := (H : ℝ)^3*J*M^(2*k)
  let K := C*(J : ℝ)*(2*(N : ℝ)*r.den)^ε
  let A₀ := (N : ℝ)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ)))
  let f : ℕ→ℕ→ℝ := fun g h=>((r.den.gcd (h^3*g^(2*k)) : ℝ)/r.den)/(1+B*(h : ℝ)^3)
  have hB : 0≤B := by dsimp [B]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hK : 0≤K := by dsimp [K]; positivity
  have hlogN : 0≤1+Real.log N := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤N by exact_mod_cast hN)
    linarith
  have hlog2N : 0≤1+Real.log (2*(N : ℝ)) := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by exact_mod_cast (show 1≤2*N by omega))
    linarith
  have hlogH : 0≤1+Real.log H := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤H by exact_mod_cast hH)
    linarith
  have hA₀ : 0≤A₀ := by dsimp [A₀]; positivity
  have hcost : (r.den : ℝ)+B*(H : ℝ)^3*r.den=sumCost V α r := by
    have he : error α r=(r.den : ℝ)*|α-(r : ℝ)| := denominator_error α r
    change _=(r.den : ℝ)+V*error α r
    rw [he]
    dsimp [B,V]
    ring
  have hexp : 2/((2*k : ℕ) : ℝ)=1/(k : ℝ) := by push_cast; ring
  have hclass := gcd_cube_power_sum r.den H N (2*k) r.pos hH (by omega : 6≤2*k) hB
  rw [hcost,hexp] at hclass
  have hheight : height V α≤sumCost V α r :=
    (height_le_cost _ _ _).trans (max_sum_cost_comparison hV α r).1
  have hclass' :
      (∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*∑h∈Finset.Icc 1 H,f g h)≤
        2*(r.den.divisors.card : ℝ)^2*(H : ℝ)*(1+Real.log H)/(height V α)^(1/(k : ℝ)) := by
    apply hclass.trans
    apply div_le_div_of_nonneg_left (by positivity)
      (Real.rpow_pos_of_pos (height_pos V α) _)
    exact Real.rpow_le_rpow (height_pos V α).le hheight (by positivity)
  have hharmonic : (∑g∈Finset.Icc 1 N,1/(g : ℝ))≤1+Real.log N := by
    have he : (∑g∈Finset.Icc 1 N,1/(g : ℝ))=(harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      simp only [Rat.cast_inv,Rat.cast_natCast,one_div]
    rw [he]
    exact harmonic_le_one_add_log N
  have hsum : divisiblePositiveKernel A k H J r α≤
      K*(A₀*(∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*∑h∈Finset.Icc 1 H,f g h)+
        (H : ℝ)*N*(∑g∈Finset.Icc 1 N,1/(g : ℝ))) := by
    rw [← sum_scaled_grid,divisiblePositiveKernel_eq_gcd hA]
    apply Finset.sum_le_sum
    intro g hg
    apply Finset.sum_le_sum
    intro h hh
    have hb := hblock A H N J h g hA (Finset.mem_Icc.mp hh) (Finset.mem_Icc.mp hg)
      M hM hMN hlow r α herr
    convert hb using 1 <;>
      dsimp [K,A₀,f,B] <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  have hHN : 0≤(H : ℝ)*N := by positivity
  calc
    _ ≤ K*(A₀*(∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*∑h∈Finset.Icc 1 H,f g h)+
        (H : ℝ)*N*(∑g∈Finset.Icc 1 N,1/(g : ℝ))) := hsum
    _ ≤ K*(A₀*(2*(r.den.divisors.card : ℝ)^2*(H : ℝ)*(1+Real.log H)/
        (height V α)^(1/(k : ℝ)))+(H : ℝ)*N*(1+Real.log N)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hclass' hA₀)
          (mul_le_mul_of_nonneg_left hharmonic hHN)) hK
    _ ≤ (2*C)*(J : ℝ)*(2*(N : ℝ)*r.den)^ε*
        (((N : ℝ)^2*(r.den.divisors.card : ℝ)^3*H*(1+Real.log (2*(N : ℝ)))*(1+Real.log H))/
          (height ((H : ℝ)^3*J*M^(2*k)) α)^(1/(k : ℝ))+(H : ℝ)*N*(1+Real.log N)) := by
      have hboundary : 0≤K*((H : ℝ)*N*(1+Real.log N)) := by positivity
      apply sub_nonneg.mp
      convert hboundary using 1 <;> dsimp [K,A₀,V] <;> ring

#print axioms divisible_positive_height_bound
end Waring.PolicyCompletionShallowHeight

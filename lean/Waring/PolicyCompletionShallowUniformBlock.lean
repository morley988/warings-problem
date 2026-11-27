import Waring.PolicyCompletionShallowBlock
import Waring.PolicyCompletionShallowClasses

/-!
# A common majorant for the actual shallow gcd blocks

The padded integer ranges and reduced moduli are compared with the original
coefficient range and denominator. The taper keeps the full source scale
J*M^d*h^3, which is needed by the joint denominator-class estimate.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowUniformBlock
open RationalHeight PolicyCompletionShallowBlock PolicyCompletionBasicLinear

set_option maxHeartbeats 800000 in
theorem uniform_divisible_gcd_block {k : ℕ} (hk : 0<k) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀A : Finset ℕ,∀H N J h g : ℕ,
      (A⊆Finset.Icc 1 N)→(1≤h ∧ h≤H)→(1≤g ∧ g≤N)→
      ∀M : ℝ,0≤M→M≤N→(∀m∈A,M<(m : ℝ))→∀r : ℚ,∀α : ℝ,
      2*((H^3*N^(2*k) : ℕ) : ℝ)*error α r≤1→
      divisibleGcdBlock A (2*k) H N J h g r α≤
        C*(J : ℝ)*(2*(N : ℝ)*r.den)^ε*
          (((N : ℝ)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ)))*
            (r.den.gcd (h^3*g^(2*k)) : ℝ))/
              ((r.den : ℝ)*(g : ℝ)^2*(1+(J : ℝ)*|α-(r : ℝ)| *M^(2*k)*(h : ℝ)^3))+
            (N : ℝ)/g) := by
  obtain ⟨C,hC,hblock⟩ := divisible_gcd_block_bound hk hε
  refine ⟨8*C,by positivity,?_⟩
  intro A H N J h g hA hh hg M hM hMN hlow r α herr
  let L : ℕ := N/g+1
  let u : ℕ := r.den.gcd (h^3*g^(2*k))
  let q : ℕ := r.den/u
  let B := (J : ℝ)*|α-(r : ℝ)| *(h : ℝ)^3*g*M^(2*k-1)
  let D := 1+(J : ℝ)*|α-(r : ℝ)| *M^(2*k)*(h : ℝ)^3
  let F := ((N : ℝ)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ)))*(u : ℝ))/
    ((r.den : ℝ)*(g : ℝ)^2*D)
  have hN : 0<N := lt_of_lt_of_le (show 0<g from hg.1) hg.2
  have hgR : (0 : ℝ)<g := by exact_mod_cast hg.1
  have hg1 : (1 : ℝ)≤g := by exact_mod_cast hg.1
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hL : (0 : ℕ)<L := Nat.succ_pos _
  have hLpos : (0 : ℝ)<L := by exact_mod_cast hL
  have hu : 0<u := Nat.gcd_pos_of_pos_left _ r.pos
  have huR : (0 : ℝ)<u := by exact_mod_cast hu
  have hq : 0<q := Nat.div_pos (Nat.le_of_dvd r.pos (Nat.gcd_dvd_left _ _)) hu
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hdenR : (0 : ℝ)<r.den := by exact_mod_cast r.pos
  have hqden : q≤r.den := Nat.div_le_self _ _
  have hqcast : (q : ℝ)=(r.den : ℝ)/(u : ℝ) := by
    apply (eq_div_iff huR.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left r.den (h^3*g^(2*k)))
  have htau : (q.divisors.card : ℝ)≤r.den.divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd r.den_nz
      (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r.den (h^3*g^(2*k)))))
  have hceil := quotient_ceiling_bounds hg.1 hg.2
  have hLup : (L : ℝ)≤2*(N : ℝ)/g := hceil.2
  have hL2N : (L : ℝ)≤2*(N : ℝ) := hLup.trans (div_le_self (by positivity) hg1)
  have hB : 0≤B := by dsimp [B]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hlogL : 0≤1+Real.log L := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤L by exact_mod_cast hL)
    linarith
  have hlogN : 0≤1+Real.log (2*(N : ℝ)) := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    linarith
  have hlogs : 1+Real.log L≤1+Real.log (2*(N : ℝ)) :=
    add_le_add_left (Real.log_le_log hLpos hL2N) 1
  have hDle : D≤1+B*(L : ℝ) := by
    have hML : M≤(g : ℝ)*(L : ℝ) := by
      have hh' := (div_lt_iff₀ hgR).mp hceil.1
      nlinarith only [hMN,hh']
    have hp := mul_le_mul_of_nonneg_left hML
      (show 0≤(J : ℝ)*|α-(r : ℝ)| *(h : ℝ)^3*M^(2*k-1) by positivity)
    have hpow : M^(2*k-1)*M=M^(2*k) := by rw [← pow_succ,Nat.sub_add_cancel (by omega : 1≤2*k)]
    have hid : (J : ℝ)*|α-(r : ℝ)| *(h : ℝ)^3*M^(2*k-1)*M=
        (J : ℝ)*|α-(r : ℝ)| *M^(2*k)*(h : ℝ)^3 := by rw [mul_assoc _ (M^(2*k-1)) M,hpow]; ring
    rw [hid] at hp
    dsimp [D,B]
    nlinarith only [hp]
  have hscale : ((L*q : ℕ) : ℝ)^ε≤(2*(N : ℝ)*r.den)^ε := by
    apply Real.rpow_le_rpow (by positivity) _ hε.le
    rw [Nat.cast_mul]
    exact mul_le_mul hL2N (by exact_mod_cast hqden) (by positivity) (by positivity)
  have hmain :
      ((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))≤4*F := by
    have hnum : (L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L)≤
        4*((N : ℝ)/g)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ))) := by
      calc
        _ ≤ (2*(N : ℝ)/g)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ))) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ (4*((N : ℝ)/g)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ))))/
          (q*(1+B*(L : ℝ))) := div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (4*((N : ℝ)/g)^2*(r.den.divisors.card : ℝ)*(1+Real.log (2*(N : ℝ))))/(q*D) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hqR hD)
          (mul_le_mul_of_nonneg_left hDle hqR.le)
      _ = _ := by
        dsimp [F]
        rw [hqcast]
        field_simp
  have hbracket :
      ((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))+L≤
        4*(F+(N : ℝ)/g) := by
    have hNdiv : 0≤(N : ℝ)/g := by positivity
    have hLup' : (L : ℝ)≤2*((N : ℝ)/g) := by simpa only [mul_div_assoc] using hLup
    linarith only [hmain,hLup',hNdiv]
  have hF : 0≤F := by dsimp [F]; positivity
  have hb := hblock A H N J h g hA hh hg M hM hlow r α herr
  change divisibleGcdBlock A (2*k) H N J h g r α≤
    2*(J : ℝ)*C*((L*q : ℕ) : ℝ)^ε*
      (((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))+L) at hb
  calc
    _ ≤ 2*(J : ℝ)*C*((L*q : ℕ) : ℝ)^ε*
        (((L : ℝ)^2*(q.divisors.card : ℝ)*(1+Real.log L))/(q*(1+B*(L : ℝ)))+L) := hb
    _ ≤ 2*(J : ℝ)*C*(2*(N : ℝ)*r.den)^ε*(4*(F+(N : ℝ)/g)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hscale (by positivity)
      · exact hbracket
      · positivity
      · positivity
    _ = _ := by dsimp [F,D,u]; ring

#print axioms uniform_divisible_gcd_block
end Waring.PolicyCompletionShallowUniformBlock

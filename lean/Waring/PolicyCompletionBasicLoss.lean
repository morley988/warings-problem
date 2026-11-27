import Waring.PolicyCompletionBasicEstimate
import Waring.SampledQuadraticSecondAsymptotic

/-!
# Uniform absorption of the basic coefficient losses

The full finite estimate is placed on any fixed polynomial-size box. Its
actual denominator scale and all three logarithmic factors are absorbed
into an arbitrarily small power of the ambient parameter.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicLoss
open RationalHeight PolicyCompletionBasicMoment PolicyCompletionBasicBinomial
open PolicyCompletionBasicEstimate DyadicLogLoss

theorem one_add_log_le_logLoss {X : ℝ} (hX : 1≤X) : 1+Real.log X≤logLoss X := by
  have hlogX := Real.log_nonneg hX
  have hlog2p : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)
    linarith
  have hh : Real.log X≤Real.log X/Real.log 2 := by
    apply (le_div_iff₀ hlog2p).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlog2 hlogX]
  dsimp [logLoss]
  linarith

theorem polynomial_loss_bound {d : ℕ} (hd : 0<d) {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀P : ℝ,2≤P→∀N H : ℕ,0<N→0<H→
      (N : ℝ)≤P^B→(H : ℝ)≤P^B→∀V : ℝ,1≤V→V≤P^B→
      (denominatorScale d N V)^δ*(1+Real.log (2*(N : ℝ)))^2*(1+Real.log H)≤C*P^ε := by
  let E := B*((d : ℝ)+1)
  have hE : 0≤E := by dsimp [E]; positivity
  let δ := ε/(2*(E+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨Cl,hCl,hlog⟩ := logLoss_pow_le_rpow 3 (half_pos hε)
  let C := ((2*(d : ℝ))^δ)*(B+2)^3*Cl
  refine ⟨δ,C,hδ,by dsimp [C]; positivity,?_⟩
  intro P hP N H hN hH hNup hHup V hV hVup
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hNR1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hHR : (0 : ℝ)<H := by exact_mod_cast hH
  have hVp : 0<V := zero_lt_one.trans_le hV
  have hTpos : 0<denominatorScale d N V := by dsimp [denominatorScale]; positivity
  have hTupper : denominatorScale d N V≤(2*(d : ℝ))*P^E := by
    calc
      _ ≤ 2*(d : ℝ)*P^B*(P^B)^d := by dsimp [denominatorScale]; gcongr
      _ = (2*(d : ℝ))*P^E := by
        rw [← Real.rpow_mul_natCast hPp.le]
        rw [mul_assoc,← Real.rpow_add hPp]
        congr 2
        dsimp [E]
        ring
  have hEδ : E*δ≤ε/2 := by
    have hid : (E+1)*δ=ε/2 := by dsimp [δ]; field_simp <;> ring
    nlinarith only [hδ,hid]
  have hTpow : (denominatorScale d N V)^δ≤(2*(d : ℝ))^δ*P^(ε/2) := by
    calc
      _ ≤ ((2*(d : ℝ))*P^E)^δ := Real.rpow_le_rpow hTpos.le hTupper hδ.le
      _ = (2*(d : ℝ))^δ*P^(E*δ) := by
        rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hPp.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP1 hEδ) (by positivity)
  have h2N : 2*(N : ℝ)≤P^(B+1) := by
    calc
      _ ≤ P*P^B := mul_le_mul hP hNup (by positivity) hPp.le
      _ = _ := by rw [Real.rpow_add hPp,Real.rpow_one]; ring
  have hH' : (H : ℝ)≤P^(B+1) := hHup.trans
    (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
  let F := (B+2)*logLoss P
  have hF : 0≤F := mul_nonneg (by linarith) (logLoss_nonneg hP1)
  have hLN : 1+Real.log (2*(N : ℝ))≤F := by
    apply (one_add_log_le_logLoss (by linarith : 1≤2*(N : ℝ))).trans
    simpa only [add_assoc,show (1 : ℝ)+1=2 by norm_num] using
      SampledQuadraticSecondAsymptotic.logLoss_polynomial_range hP1 (by positivity)
        (show 0≤B+1 by linarith) h2N
  have hLH : 1+Real.log (H : ℝ)≤F := by
    apply (one_add_log_le_logLoss (by exact_mod_cast hH)).trans
    simpa only [add_assoc,show (1 : ℝ)+1=2 by norm_num] using
      SampledQuadraticSecondAsymptotic.logLoss_polynomial_range hP1 hHR
        (show 0≤B+1 by linarith) hH'
  have hLN0 : 0≤1+Real.log (2*(N : ℝ)) := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    linarith
  have hLH0 : 0≤1+Real.log (H : ℝ) := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤H by exact_mod_cast hH)
    linarith
  have hlogs : (1+Real.log (2*(N : ℝ)))^2*(1+Real.log H)≤(B+2)^3*Cl*P^(ε/2) := by
    calc
      _ ≤ F^2*F := mul_le_mul (pow_le_pow_left₀ hLN0 hLN _) hLH hLH0 (by positivity)
      _ = (B+2)^3*(logLoss P)^3 := by dsimp [F]; ring
      _ ≤ (B+2)^3*(Cl*P^(ε/2)) := mul_le_mul_of_nonneg_left (hlog P hP1) (by positivity)
      _ = _ := by ring
  calc
    _ = (denominatorScale d N V)^δ*((1+Real.log (2*(N : ℝ)))^2*(1+Real.log H)) := by ring
    _ ≤ ((2*(d : ℝ))^δ*P^(ε/2))*((B+2)^3*Cl*P^(ε/2)) :=
      mul_le_mul hTpow hlogs (by positivity) (by positivity)
    _ = C*(P^(ε/2)*P^(ε/2)) := by dsimp [C]; ring
    _ = C*P^ε := by rw [← Real.rpow_add hPp]; congr 2; ring

/-- The full actual basic moment with every auxiliary loss now expressed
as one uniform P^epsilon, on polynomial-size sampling and coefficient boxes. -/
theorem basic_moment_uniform_loss {d : ℕ} (hd : 6≤d) {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,2≤P→∀(A : Finset ℕ) (N H J : ℕ) (M Y α : ℝ) (σ : ℕ→ℝ),
      0<N→0<H→0<J→A⊆Finset.Icc 1 N→1≤M→M≤N→1≤Y→Y≤M→
      (∀m∈A,M<(m : ℝ))→(N : ℝ)≤P^B→(H : ℝ)≤P^B→(H : ℝ)^3*J≤P^B→
      16*(H : ℝ)^3*Y≤J→
      2*Y^3*Real.sqrt (((H : ℝ)^3*J)*((d : ℝ)*(N : ℝ)^(d-1)))/((H : ℝ)^3*J)<1→
      2*Y^d<Real.sqrt (((H : ℝ)^3*J)*M^d)→
      basicMoment A d H J α σ≤
        C*P^ε*(J : ℝ)*H*(N : ℝ)^2*
          (1/Y+1/(height (((H : ℝ)^3*J)*M^d) α)^(2/(d : ℝ))) := by
  obtain ⟨δ,Cl,hδ,hCl,hloss⟩ := polynomial_loss_bound (by omega : 0<d) hB hε
  obtain ⟨Cm,hCm,hmoment⟩ := basic_moment_height_bound hd hδ
  refine ⟨Cm*Cl,by positivity,?_⟩
  intro P hP A N H J M Y α σ hN hH hJ hA hM hMN hY hYM hAlower hNup hHup hVup hcubic hbin hpower
  have hV : 1≤(H : ℝ)^3*J := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (show (1 : ℝ)≤H by exact_mod_cast hH)) (by exact_mod_cast hJ)
  have hl := hloss P hP N H hN hH hNup hHup ((H : ℝ)^3*J) hV hVup
  have hm := hmoment A N H J M Y α σ hN hH hJ hA hM hMN hY hYM hAlower hcubic hbin hpower
  have hE : 0≤1/Y+1/(height (((H : ℝ)^3*J)*M^d) α)^(2/(d : ℝ)) := by
    exact add_nonneg (one_div_nonneg.mpr (zero_le_one.trans hY))
      (one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)).le
  calc
    _ ≤ _ := hm
    _ = (Cm*(J : ℝ)*H*(N : ℝ)^2*
        (1/Y+1/(height (((H : ℝ)^3*J)*M^d) α)^(2/(d : ℝ))))*
        ((denominatorScale d N ((H : ℝ)^3*J))^δ*(1+Real.log (2*(N : ℝ)))^2*(1+Real.log H)) := by ring
    _ ≤ (Cm*(J : ℝ)*H*(N : ℝ)^2*
        (1/Y+1/(height (((H : ℝ)^3*J)*M^d) α)^(2/(d : ℝ))))*(Cl*P^ε) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ = _ := by ring

#print axioms polynomial_loss_bound
#print axioms basic_moment_uniform_loss
end Waring.PolicyCompletionBasicLoss

import Waring.PolicyCompletionBasicLoss

/-!
# Uniform absorption of the shallow source losses

Actual divisor multiplicities, both harmonic factors, and the canonical
dyadic depth are bounded uniformly on arbitrary fixed polynomial ranges.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowLoss
open DyadicLogLoss PolicyCompletionBasicLoss

set_option maxHeartbeats 800000 in
theorem shallow_loss_bounds {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃δ D : ℝ,0<δ ∧ 0<D ∧ ∀P : ℝ,1≤P→∀N H T q : ℕ,
      0<N→0<H→0<T→0<q→
      (H : ℝ)≤P^B→(T : ℝ)≤P^B→(q : ℝ)≤P^B→2*(N : ℝ)*q≤P^B→
      (2*(N : ℝ)*q)^δ*(q.divisors.card : ℝ)^3*
          (1+Real.log (2*(N : ℝ)))*(1+Real.log H)≤D*P^ε ∧
      (2*(N : ℝ)*q)^δ*(1+Real.log N)≤D*P^ε ∧
      (T : ℝ)^δ*(Nat.clog 2 q+1 : ℕ)≤D*P^ε := by
  let δ := ε/(4*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨Cd,hCd,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow 3 hδ
  obtain ⟨Cl,hCl,hlog⟩ := logLoss_pow_le_rpow 2 (half_pos hε)
  obtain ⟨Cy,hCy,hyadic⟩ := clog_depth_pow_le_rpow 1 hδ
  let D₁ := Cd*(B+1)^2*Cl
  let D := D₁+Cy+1
  have hD₁ : 0<D₁ := by dsimp [D₁]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hBd : 2*B*δ≤ε/2 := by
    have hh : (B+1)*δ=ε/4 := by dsimp [δ]; field_simp <;> ring
    nlinarith only [hh,hδ]
  refine ⟨δ,D,hδ,hD,?_⟩
  intro P hP N H T q hN hH hT hq hHup hTup hqup hscale
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast hq
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hH1 : (1 : ℝ)≤H := by exact_mod_cast hH
  have hT1 : (1 : ℝ)≤T := by exact_mod_cast hT
  have h2Nup : 2*(N : ℝ)≤P^B :=
    (le_mul_of_one_le_right (by positivity) hq1).trans hscale
  have hpow (X : ℝ) (hX : 0≤X) (hXup : X≤P^B) : X^δ≤P^(B*δ) := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow hX hXup hδ.le
      _ = _ := (Real.rpow_mul hPp.le _ _).symm
  have hscalePow := hpow (2*(N : ℝ)*q) (by positivity) hscale
  have hqPow := hpow q (by positivity) hqup
  have hTPow := hpow T (by positivity) hTup
  have hdivq : (q.divisors.card : ℝ)^3≤Cd*P^(B*δ) :=
    (hdiv q hq).trans (mul_le_mul_of_nonneg_left hqPow hCd.le)
  let F := (B+1)*logLoss P
  have hF : 0≤F := by dsimp [F]; exact mul_nonneg (by positivity) (logLoss_nonneg hP)
  have hLN : 1+Real.log (2*(N : ℝ))≤F := by
    apply (one_add_log_le_logLoss (by linarith : 1≤2*(N : ℝ))).trans
    exact SampledQuadraticSecondAsymptotic.logLoss_polynomial_range hP (by positivity) hB h2Nup
  have hLH : 1+Real.log H≤F :=
    (one_add_log_le_logLoss hH1).trans
      (SampledQuadraticSecondAsymptotic.logLoss_polynomial_range hP (by positivity) hB hHup)
  have hLN0 : 0≤1+Real.log (2*(N : ℝ)) := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    linarith
  have hLH0 : 0≤1+Real.log H := by have hh := Real.log_nonneg hH1; linarith
  have hlogs : (1+Real.log (2*(N : ℝ)))*(1+Real.log H)≤(B+1)^2*Cl*P^(ε/2) := by
    calc
      _ ≤ F*F := mul_le_mul hLN hLH hLH0 hF
      _ = (B+1)^2*(logLoss P)^2 := by dsimp [F]; ring
      _ ≤ (B+1)^2*(Cl*P^(ε/2)) := mul_le_mul_of_nonneg_left (hlog P hP) (by positivity)
      _ = _ := by ring
  have hmain : (2*(N : ℝ)*q)^δ*(q.divisors.card : ℝ)^3*
      (1+Real.log (2*(N : ℝ)))*(1+Real.log H)≤D₁*P^ε := by
    calc
      _ = ((2*(N : ℝ)*q)^δ*(q.divisors.card : ℝ)^3)*
          ((1+Real.log (2*(N : ℝ)))*(1+Real.log H)) := by ring
      _ ≤ (P^(B*δ)*(Cd*P^(B*δ)))*((B+1)^2*Cl*P^(ε/2)) := by
        apply mul_le_mul
        · exact mul_le_mul hscalePow hdivq (by positivity) (by positivity)
        · exact hlogs
        · exact mul_nonneg hLN0 hLH0
        · positivity
      _ = D₁*P^(2*B*δ+ε/2) := by
        have hp : P^(B*δ)*P^(B*δ)*P^(ε/2)=P^(2*B*δ+ε/2) := by
          rw [← Real.rpow_add hPp,← Real.rpow_add hPp]
          congr 1
          ring
        calc
          _ = D₁*(P^(B*δ)*P^(B*δ)*P^(ε/2)) := by dsimp [D₁]; ring
          _ = _ := by rw [hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith only [hBd])) hD₁.le
  have hD₁D : D₁≤D := by dsimp [D]; linarith
  have hmainD := hmain.trans (mul_le_mul_of_nonneg_right hD₁D (Real.rpow_nonneg hPp.le _))
  refine ⟨hmainD,?_,?_⟩
  · have htau : (1 : ℝ)≤(q.divisors.card : ℝ)^3 := by
      have hc : 1≤q.divisors.card := Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr hq.ne'⟩
      exact one_le_pow₀ (by exact_mod_cast hc)
    have hLH1 : (1 : ℝ)≤1+Real.log H := by have hh := Real.log_nonneg hH1; linarith
    have hlogle : 1+Real.log N≤1+Real.log (2*(N : ℝ)) :=
      add_le_add_left (Real.log_le_log (by positivity) (by linarith)) 1
    apply le_trans _ hmainD
    calc
      _ ≤ (2*(N : ℝ)*q)^δ*(1+Real.log (2*(N : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = (2*(N : ℝ)*q)^δ*1*(1+Real.log (2*(N : ℝ)))*1 := by ring
      _ ≤ _ := by gcongr
  · have hy : (Nat.clog 2 q+1 : ℕ)≤Cy*P^(B*δ) := by
      have hh : ((Nat.clog 2 q+1 : ℕ) : ℝ)≤Cy*(q : ℝ)^δ := by
        simpa only [pow_one] using hyadic q hq
      exact hh.trans (mul_le_mul_of_nonneg_left hqPow hCy.le)
    calc
      _ ≤ P^(B*δ)*(Cy*P^(B*δ)) := mul_le_mul hTPow hy (by positivity) (by positivity)
      _ = Cy*(P^(B*δ)*P^(B*δ)) := by ring
      _ = Cy*P^(2*B*δ) := by rw [← Real.rpow_add hPp]; congr 2; ring
      _ ≤ Cy*P^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith only [hBd,hε])) hCy.le
      _ ≤ D*P^ε := mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (by positivity)

#print axioms shallow_loss_bounds
end Waring.PolicyCompletionShallowLoss

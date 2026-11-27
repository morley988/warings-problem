import Waring.CubicSamplingCutoff
import Waring.DivisorBound
import Waring.DyadicLogLoss

/-!
# Uniform epsilon form of the refined coefficient-sampling estimate

The divisor and logarithmic factors in the finite proof are absorbed into an
arbitrarily small power of the conductor. A polynomial-size wrapper converts
this to the usual ambient `P^epsilon` convention. No sampling, divisor, or
transference estimate remains an assumption.
-/

noncomputable section

namespace Waring.CubicCoefficientSampling
open Waring.RationalHeight Waring.SampledLinearSecondMoment

def samplingShape (H N J : ℕ) (α : ℝ) : ℝ :=
  1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+
    (H:ℝ)^2/height ((H:ℝ)^3*((N:ℝ)*J)) α

theorem samplingShape_nonneg (H N J : ℕ) (α : ℝ) : 0 ≤ samplingShape H N J α := by
  have hL := (height_pos ((H:ℝ)^3*((N:ℝ)*J)) α).le
  unfold samplingShape
  positivity

theorem cubic_sampling_epsilon_conductor {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H N J : ℕ, 0 < H → 0 < N → 0 < J →
      ∀ (α : ℝ) (c : ℕ → ℂ) (σ : ℕ → ℝ),
        cubicSecondMoment α H N J c σ ≤
          C * (((H:ℝ)^3*((N:ℝ)*J))^ε) * (H:ℝ)*((N:ℝ)*J)*
            coefficientEnergy N c * samplingShape H N J α := by
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cd,hCd,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  obtain ⟨Cw,hCw,hlog⟩ := DyadicLogLoss.logLoss_pow_le_rpow 1 hδ
  refine ⟨8192*Cw*Cd, by positivity, ?_⟩
  intro H N J hH hN hJ α c σ
  let V : ℝ := (H:ℝ)^3*((N:ℝ)*J)
  let W : ℝ := 2+Real.log (J:ℝ)/Real.log 2
  have hH1 : (1:ℝ)≤H := by exact_mod_cast hH
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hJ1 : (1:ℝ)≤J := by exact_mod_cast hJ
  have hH3 : (1:ℝ)≤(H:ℝ)^3 := one_le_pow₀ hH1
  have hU1 : (1:ℝ)≤(N:ℝ)*J := one_le_mul_of_one_le_of_one_le hN1 hJ1
  have hV1 : 1 ≤ V := one_le_mul_of_one_le_of_one_le hH3 hU1
  have hVp : 0 < V := zero_lt_one.trans_le hV1
  have hJp : (0:ℝ)<J := zero_lt_one.trans_le hJ1
  have hJV : (J:ℝ) ≤ V := by
    have hh := one_le_mul_of_one_le_of_one_le hH3 hN1
    have hm := mul_le_mul_of_nonneg_right hh hJp.le
    dsimp [V]
    nlinarith
  have hsqrt : Real.sqrt V ≤ V := by
    have hs := Real.sq_sqrt hVp.le
    have hsn := Real.sqrt_nonneg V
    nlinarith [sq_nonneg (V-1)]
  obtain ⟨r,hr,hb⟩ := cubic_sampling_explicit α H N J c σ hH hN hJ
  let D : ℝ := r.den.divisors.card
  have hD1 : 1 ≤ D := by
    have hh : 0 < r.den.divisors.card :=
      Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr r.den_nz⟩
    have hh' : 1 ≤ r.den.divisors.card := hh
    change (1:ℝ) ≤ (r.den.divisors.card:ℝ)
    exact_mod_cast hh'
  have htV : (r.den:ℝ) ≤ V := by
    have hcost : cost V α r ≤ Real.sqrt V := hr ▸ height_le_sqrt hV1 α
    exact ((le_max_left _ _).trans hcost).trans hsqrt
  have hD : D ≤ Cd*V^δ := hdiv V hV1 r.den r.pos htV
  have hW0 : 0 ≤ W := DyadicLogLoss.logLoss_nonneg hJ1
  have hW : W ≤ Cw*V^δ := by
    have hm : W ≤ DyadicLogLoss.logLoss V := by
      unfold W DyadicLogLoss.logLoss
      apply add_le_add_left
      exact div_le_div_of_nonneg_right (Real.log_le_log hJp hJV) (Real.log_pos (by norm_num)).le
    exact hm.trans (by simpa only [pow_one] using hlog V hV1)
  have hWD : W*D ≤ Cw*Cd*V^ε := by
    calc
      W*D ≤ (Cw*V^δ)*(Cd*V^δ) := mul_le_mul hW hD (zero_le_one.trans hD1) (by positivity)
      _ = Cw*Cd*(V^δ*V^δ) := by ring
      _ = Cw*Cd*V^ε := by
        rw [← Real.rpow_add hVp]
        congr 2
        dsimp [δ]
        ring
  have hshape : 1/(N:ℝ)+1/(J:ℝ)+4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+
      D*(H:ℝ)^2/height V α ≤ 4*D*samplingShape H N J α := by
    have ha : 0 ≤ 1/(N:ℝ) := by positivity
    have hb : 0 ≤ 1/(J:ℝ) := by positivity
    have hc : 0 ≤ Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) := by positivity
    have hd : 0 ≤ (H:ℝ)^2/height V α := by have := height_pos V α; positivity
    have hA : 1/(N:ℝ)+1/(J:ℝ)+4*(Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)) ≤
        4*(1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hD1
      (show 0 ≤ 4*(1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)) by positivity)
    have hDpos : 0 ≤ D := zero_le_one.trans hD1
    have hlast := mul_nonneg hDpos hd
    dsimp [samplingShape]
    change 1/(N:ℝ)+1/(J:ℝ)+4*Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+
      D*(H:ℝ)^2/height V α ≤
      4*D*(1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+(H:ℝ)^2/height V α)
    simp only [mul_div_assoc] at hA hmul hlast ⊢
    nlinarith only [hA,hmul,hlast]
  have henergy := coefficientEnergy_nonneg N c
  have hshapen := samplingShape_nonneg H N J α
  calc
    cubicSecondMoment α H N J c σ ≤
        2048*W*coefficientEnergy N c*(H:ℝ)*((N:ℝ)*J)*
          (4*D*samplingShape H N J α) :=
      hb.trans (mul_le_mul_of_nonneg_left hshape (by positivity))
    _ = 8192*(W*D)*(H:ℝ)*((N:ℝ)*J)*coefficientEnergy N c*samplingShape H N J α := by ring
    _ ≤ 8192*(Cw*Cd*V^ε)*(H:ℝ)*((N:ℝ)*J)*coefficientEnergy N c*samplingShape H N J α := by
      gcongr
    _ = _ := by dsimp [V]; ring

/-- Uniform ambient-parameter form. This is the refined coefficient bound
with `P^epsilon` loss for any fixed polynomial conductor range. -/
theorem cubic_sampling_epsilon {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H N J : ℕ,
      0 < H → 0 < N → 0 < J → (H:ℝ)^3*((N:ℝ)*J) ≤ P^B →
      ∀ (α : ℝ) (c : ℕ → ℂ) (σ : ℕ → ℝ),
        cubicSecondMoment α H N J c σ ≤
          C*P^ε*(H:ℝ)*((N:ℝ)*J)*coefficientEnergy N c*samplingShape H N J α := by
  let δ := ε/(B+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hBδ : B*δ ≤ ε := by
    have heq : δ*(B+1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  obtain ⟨C,hC,hbound⟩ := cubic_sampling_epsilon_conductor hδ
  refine ⟨C,hC,?_⟩
  intro P hP H N J hH hN hJ hV α c σ
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hpow : ((H:ℝ)^3*((N:ℝ)*J))^δ ≤ P^ε := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow (by positivity) hV hδ.le
      _ = P^(B*δ) := (Real.rpow_mul hP0 B δ).symm
      _ ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP hBδ
  apply (hbound H N J hH hN hJ α c σ).trans
  have henergy := coefficientEnergy_nonneg N c
  have hshape := samplingShape_nonneg H N J α
  gcongr

#print axioms cubic_sampling_epsilon_conductor
#print axioms cubic_sampling_epsilon

end Waring.CubicCoefficientSampling

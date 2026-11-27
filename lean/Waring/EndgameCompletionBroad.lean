import Waring.EndgameCompletionQuadrature
import Waring.EndgameCompletionHarmonic

/-!
# Elementary broad major-arc approximation

This assembles actual finite Fourier completion, the composite twisted
three-quarters estimate, discrete first-derivative cancellation, uniform
zero-frequency quadrature, and gcd-weighted harmonic summation. There is
no imported Weil or published major-arc estimate among its hypotheses.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion
open QuadraticModulation

/-- The broad rational approximation with the elementary Davenport--
Heilbronn exponent. All arithmetic and analytic inputs are proved above. -/
theorem ordinary_broad_major_approximation (k : ℕ) (hk : 2≤k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : ℕ) (P β : ℝ),
      Nat.Coprime a q → 0≤P → |β| *(k : ℝ)*P^(k-1)≤1/(2*(q : ℝ)) →
      ‖ordinaryWeyl k P ((a : ℝ)/q+β)-
        (completeMonomialSumMod q k (a : ZMod q)/(q : ℂ))*monomialIntegral k P β‖ ≤
        C*(q : ℝ)^(3/4+ε : ℝ) := by
  let K : ℝ := 1+Real.pi/4
  let C₀ : ℝ := 5+Real.pi/2
  have hK : 0≤K := by dsimp [K]; positivity
  have hC₀ : 0<C₀ := by dsimp [C₀]; positivity
  have hε2 : 0<ε/2 := by positivity
  obtain ⟨Cs,hCs,hsum⟩ := norm_twistedMonomialSumMod_le_rpow k hk hε2
  obtain ⟨Cw,hCw,hweight⟩ := completedFrequencyWeight_normalized_le_rpow hK hε2
  refine ⟨C₀+Cs*Cw,by positivity,?_⟩
  intro q _ a P β ha hP hβ
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hq1 : (1 : ℝ)≤q := by exact_mod_cast hq
  have hβsmall : |β| *(k : ℝ)*P^(k-1)≤1/2 := hβ.trans (by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*q)).mpr
    nlinarith)
  have hquad := ordinary_monomial_quadrature k (by omega) hP hβsmall
  have hcomplete : ‖completeMonomialSumMod q k (a : ZMod q)‖/(q : ℝ)≤1 := by
    apply (div_le_one hqR).mpr
    simpa only [twistedMonomialSumMod_zero] using
      norm_twistedMonomialSumMod_le q k (a : ZMod q) 0
  let A := (Finset.univ : Finset (ZMod q)).erase 0
  let w : ℕ → ℂ := fun n=>e (β*(n : ℝ)^k)
  have hlinear (b : ZMod q) (hb : b∈A) :
      ‖completedLinearSum q (ordinaryNumbers P) w b‖≤
        2+K*(q : ℝ)/(min b.val (q-b.val) : ℕ) :=
    completedLinearSum_broad_bound q k hP b (Finset.mem_erase.mp hb).1 hβ
  have htwisted (b : ZMod q) : ‖twistedMonomialSumMod q k (a : ZMod q) b‖≤
      Cs*(q : ℝ)^(3/4+ε/2 : ℝ)*Nat.gcd b.val q := by
    simpa only [ZMod.natCast_zmod_val] using hsum q a b.val ha
  have hnonzero : (q : ℝ)⁻¹*∑ b∈A,
      ‖twistedMonomialSumMod q k (a : ZMod q) b‖*‖completedLinearSum q (ordinaryNumbers P) w b‖ ≤
      (Cs*Cw)*(q : ℝ)^(3/4+ε : ℝ) := by
    have hsumBound : (∑ b∈A,
        ‖twistedMonomialSumMod q k (a : ZMod q) b‖*‖completedLinearSum q (ordinaryNumbers P) w b‖) ≤
        (Cs*(q : ℝ)^(3/4+ε/2 : ℝ))*completedFrequencyWeight q K := by
      rw [completedFrequencyWeight,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      apply (mul_le_mul (htwisted b) (hlinear b hb) (norm_nonneg _) (by positivity)).trans_eq
      ring
    calc
      _ ≤ (q : ℝ)⁻¹*((Cs*(q : ℝ)^(3/4+ε/2 : ℝ))*completedFrequencyWeight q K) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
      _ = (Cs*(q : ℝ)^(3/4+ε/2 : ℝ))*((q : ℝ)⁻¹*completedFrequencyWeight q K) := by ring
      _ ≤ (Cs*(q : ℝ)^(3/4+ε/2 : ℝ))*(Cw*(q : ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_left (hweight q) (by positivity)
      _ = _ := by
        have hpow : (q : ℝ)^(3/4+ε : ℝ)=(q : ℝ)^(3/4+ε/2 : ℝ)*(q : ℝ)^(ε/2) := by
          rw [← Real.rpow_add hqR]
          congr 1
          ring
        rw [hpow]
        ring
  have hdecomp := rationalWeightedSum_main_error_le q k (a : ZMod q)
    (ordinaryNumbers P) w (monomialIntegral k P β)
  have hord : ordinaryWeyl k P ((a : ℝ)/q+β)=
      rationalWeightedSum q k (a : ZMod q) (ordinaryNumbers P) w := by
    simpa only [Int.cast_natCast] using ordinaryWeyl_eq_rationalWeightedSum q k (a : ℤ) P β
  rw [← hord] at hdecomp
  apply hdecomp.trans
  have hzero : (‖completeMonomialSumMod q k (a : ZMod q)‖/q)*
      ‖(∑ n∈ordinaryNumbers P,w n)-monomialIntegral k P β‖≤C₀ := by
    exact (mul_le_mul hcomplete hquad (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)).trans_eq (one_mul _)
  apply (add_le_add hzero hnonzero).trans
  have hqpow : (1 : ℝ)≤(q : ℝ)^(3/4+ε : ℝ) := Real.one_le_rpow hq1 (by positivity)
  have hc := mul_le_mul_of_nonneg_left hqpow hC₀.le
  nlinarith

#print axioms ordinary_broad_major_approximation

end Waring.EndgameCompletion

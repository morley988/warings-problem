import Waring.PolicyCompletionSourceMajor
import Waring.PolicyCompletionMajorAverage

/-! # Actual single-phase auxiliary majorant with its height gcd -/

noncomputable section
namespace Waring.PolicyCompletionSourceMajorNorm
open Polynomial QuadraticModulation EndgameCompletion IntegerDifferencePolynomial
open PolicyCompletionPositivePhase PolicyCompletionPhaseContent PolicyCompletionPolynomialBroad
open PolicyCompletionPolynomialResidues PolicyCompletionPolynomialComplete PolicyCompletionPolynomialGcd
open PolicyCompletionPolynomialCalculus PolicyCompletionPolynomialDecay PolicyCompletionSourceMajor

theorem complete_sum_le_height_gcd (D K : ℕ) (hD : 1≤D) (hK : 1≤K)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ) (f : Polynomial ℤ) (H : ℤ),
      IsCoprime (q:ℤ) a → f.natDegree≤D → f.coeff D=(K:ℤ)*H →
      ‖integerPolynomialSum q (C a*f)‖ ≤
        C₀*(q:ℝ)^(1-1/(D:ℝ)+ε)*(Nat.gcd q H.natAbs:ℝ)^(1/(D:ℝ)) := by
  obtain ⟨C₀,hC₀,hcomplete⟩ := integerPolynomialSum_le_rpow D hD hε
  refine ⟨C₀*(K:ℝ), by positivity, ?_⟩
  intro q _ a f H ha hf hlead
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hbase := coefficientDivisorBoundAt_coefficient q f D (by omega)
  rw [hlead, Int.natAbs_mul, Int.natAbs_natCast] at hbase
  have hcoeff := coefficientDivisorBoundAt_unit_mul hbase ha
  have hbound := hcomplete q (C a*f) ((Polynomial.natDegree_C_mul_le a f).trans hf)
    (K*H.natAbs) hcoeff
  have hDreal : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have hK1 : (1:ℝ)≤K := by exact_mod_cast hK
  have hweight : (Nat.gcd q (K*H.natAbs):ℝ)^(1/(D:ℝ)) ≤
      (K:ℝ)*(Nat.gcd q H.natAbs:ℝ)^(1/(D:ℝ)) := by
    calc
      _ ≤ ((K:ℝ)*(Nat.gcd q H.natAbs:ℝ))^(1/(D:ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast gcd_mul_bound q K H.natAbs (by omega) hq)
          (by positivity)
      _ = (K:ℝ)^(1/(D:ℝ))*(Nat.gcd q H.natAbs:ℝ)^(1/(D:ℝ)) :=
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le hK1 ((div_le_one hDreal).mpr hD1)) (by positivity)
  apply hbound.trans
  exact (mul_le_mul_of_nonneg_left hweight (by positivity)).trans_eq (by ring)

theorem heightProduct_pos (params : List (ℤ × ℤ))
    (hparams : ∀ hm ∈ params, 0<hm.1) : 0<heightProduct params := by
  induction params with
  | nil => norm_num [heightProduct]
  | cons p rest ih =>
    exact mul_pos (hparams p (List.mem_cons_self ..))
      (ih (fun q hq => hparams q (List.mem_cons_of_mem _ hq)))

theorem source_single_phase_majorant (k j : ℕ) (hj : j+2≤k) {ε : ℝ} (hε : 0<ε) :
    ∃ C₀ : ℝ, 0<C₀ ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ)
      (params : List (ℤ × ℤ)) (P β : ℝ),
      IsCoprime (q:ℤ) a → params.length=j →
      (∀ hm ∈ params, 0<hm.1 ∧ 0<hm.2) → 0<P →
      |β| *((powerPolynomial k params).map (Int.castRingHom ℝ)).derivative.eval P≤1/(2*(q:ℝ)) →
      ‖integerPolynomialWeyl (powerPolynomial k params) P ((a:ℝ)/q+β)‖ ≤
        C₀*(P*(q:ℝ)^(-1/((k-j:ℕ):ℝ)+ε)*
          (Nat.gcd q (heightProduct params).natAbs:ℝ)^(1/((k-j:ℕ):ℝ))*
          (1+|β| *(heightProduct params:ℝ)*P^(k-j))^(-1/((k-j:ℕ):ℝ))+
          (q:ℝ)^(1-1/((k-j:ℕ):ℝ)+ε)) := by
  have hD : 2≤k-j := by omega
  have hK : 1≤leadingMultiplier k j := by
    unfold leadingMultiplier
    exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.descFactorial_pos.mpr (by omega))
  obtain ⟨Ce,hCe,herror⟩ := source_broad_major_approximation k j hj hε
  obtain ⟨Cs,hCs,hsum⟩ := complete_sum_le_height_gcd (k-j) (leadingMultiplier k j) (by omega) hK hε
  refine ⟨Ce+4*Cs, by positivity, ?_⟩
  intro q _ a params P β ha hlen hparams hP hβ
  let f := powerPolynomial k params
  let g := f.map (Int.castRingHom ℝ)
  let H : ℝ := (heightProduct params:ℝ)
  let θ : ℝ := 1/((k-j:ℕ):ℝ)
  have hqR : (0:ℝ)<q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hnonzero : ∀ hm ∈ params, hm.1≠0 ∧ hm.2≠0 :=
    fun hm hhm => ⟨(hparams hm hhm).1.ne', (hparams hm hhm).2.ne'⟩
  have hlenk : params.length≤k := by omega
  have hdeg : f.natDegree=k-j := by rw [powerPolynomial_natDegree k params hnonzero hlenk, hlen]
  have hlead : f.coeff (k-j)=(leadingMultiplier k j:ℤ)*heightProduct params := by
    rw [← hdeg, Polynomial.coeff_natDegree, powerPolynomial_leadingCoeff k params hnonzero hlenk, hlen]
  have hH : 0<H := by dsimp [H]; exact_mod_cast heightProduct_pos params (fun p hp => (hparams p hp).1)
  have hKreal : (1:ℝ)≤leadingMultiplier k j := by exact_mod_cast hK
  have hcoeff : H≤g.coeff (k-j) := by
    rw [Polynomial.coeff_map, hlead, map_mul, map_natCast]
    change H≤((leadingMultiplier k j:ℝ)*H)
    nlinarith
  have hpos := powerPolynomial_real_nonnegative k params
    (fun p hp => ⟨(hparams p hp).1.le, (hparams p hp).2⟩)
  have hintegral := norm_polynomialIntegral_weight g hpos (β := β) (by omega : 1≤k-j) hH hcoeff hP
  have hintegral' : ‖polynomialIntegral g P β‖ ≤ 4*P*(1+|β| *H*P^(k-j))^(-θ) := by
    simpa only [θ, one_div] using hintegral
  have hcomplete := hsum q a f (heightProduct params) ha hdeg.le hlead
  have herr := herror q a params P β hlen hparams hP.le hβ
  let model : ℂ := (integerPolynomialSum q (C a*f)/(q:ℂ))*polynomialIntegral g P β
  have hmodel : ‖model‖ ≤ (4*Cs)*(P*(q:ℝ)^(-θ+ε)*
      (Nat.gcd q (heightProduct params).natAbs:ℝ)^θ*(1+|β| *H*P^(k-j))^(-θ)) := by
    dsimp [model]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    apply (mul_le_mul (div_le_div_of_nonneg_right hcomplete hqR.le) hintegral'
      (norm_nonneg _) (by positivity)).trans_eq
    have hp : (q:ℝ)^(1-θ+ε)=(q:ℝ)*(q:ℝ)^(-θ+ε) := by
      conv_rhs => lhs; rw [← Real.rpow_one (q:ℝ)]
      rw [← Real.rpow_add hqR]
      congr 1
      ring
    change Cs*(q:ℝ)^(1-θ+ε)*(Nat.gcd q (heightProduct params).natAbs:ℝ)^θ/(q:ℝ)*
      (4*P*(1+|β| *H*P^(k-j))^(-θ)) = _
    rw [hp]
    field_simp
  have hnorm := norm_le_norm_sub_add (integerPolynomialWeyl f P ((a:ℝ)/q+β)) model
  apply (hnorm.trans (add_le_add herr hmodel)).trans
  change Ce*(q:ℝ)^(1-θ+ε)+(4*Cs)*(P*(q:ℝ)^(-θ+ε)*
      (Nat.gcd q (heightProduct params).natAbs:ℝ)^θ*(1+|β| *H*P^(k-j))^(-θ)) ≤ _
  dsimp [θ, H]
  simp only [neg_div, one_div]
  have hH0 : 0≤(heightProduct params:ℝ) := hH.le
  let U : ℝ := P*(q:ℝ)^(-((k-j:ℕ):ℝ)⁻¹+ε)*
    (Nat.gcd q (heightProduct params).natAbs:ℝ)^(((k-j:ℕ):ℝ)⁻¹)*
    (1+|β| *(heightProduct params:ℝ)*P^(k-j))^(-((k-j:ℕ):ℝ)⁻¹)
  let V : ℝ := (q:ℝ)^(1-((k-j:ℕ):ℝ)⁻¹+ε)
  have hU : 0≤U := by dsimp [U]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  change Ce*V+4*Cs*U≤(Ce+4*Cs)*(U+V)
  nlinarith only [mul_nonneg hCe.le hU, mul_nonneg (show 0≤4*Cs by positivity) hV]


#print axioms complete_sum_le_height_gcd
#print axioms source_single_phase_majorant
end Waring.PolicyCompletionSourceMajorNorm

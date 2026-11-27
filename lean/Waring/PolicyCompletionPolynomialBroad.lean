import Waring.PolicyCompletionPolynomialFourier
import Waring.PolicyCompletionPhaseContent

/-!
# Broad major-arc approximation for the actual auxiliary polynomial

The complete-sum estimate, the nonzero-frequency cancellation, the
gcd-weighted harmonic sum and the uniform quadrature are all proved inputs.
Only a finite coefficient identity and the literal derivative-size
condition occur in the conclusion's hypotheses.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionPolynomialBroad
open Polynomial QuadraticModulation EndgameCompletion
open PolicyCompletionPolynomialFourier PolicyCompletionPolynomialResidues
open PolicyCompletionPolynomialComplete PolicyCompletionPolynomialGcd
open PolicyCompletionPolynomialDiscrete PolicyCompletionPolynomialCalculus
open PolicyCompletionPolynomialQuadrature PolicyCompletionPhaseContent

theorem gcd_mul_bound (q K b : ℕ) (hK : 0<K) (hq : 0<q) :
    Nat.gcd q (K*b) ≤ K*Nat.gcd q b := by
  apply Nat.le_of_dvd (Nat.mul_pos hK (Nat.gcd_pos_of_pos_left b hq))
  have hh : Nat.gcd q (K*b) ∣ Nat.gcd (K*q) (K*b) := Nat.dvd_gcd
    ((Nat.gcd_dvd_left q (K*b)).trans (dvd_mul_left q K)) (Nat.gcd_dvd_right q (K*b))
  simpa only [Nat.gcd_mul_left] using hh

theorem twistedPolynomialSum_bound (D K : ℕ) (hD : 2≤D) (hK : 1≤K)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (f : Polynomial ℤ) (L : ℤ),
      f.natDegree≤D → (K:ℤ)*f.coeff 1=f.coeff D*L → ∀ b : ZMod q,
      ‖twistedPolynomialSum q f b‖ ≤
        C*(q:ℝ)^(1-1/(D:ℝ)+ε)*(Nat.gcd b.val q:ℝ) := by
  obtain ⟨C,hC,hcomplete⟩ := integerPolynomialSum_le_rpow D (by omega) hε
  refine ⟨C*(K:ℝ), by positivity, ?_⟩
  intro q _ f L hf hrel b
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hgcd : 1≤Nat.gcd q (K*b.val) := Nat.gcd_pos_of_pos_left _ hq
  have hDreal : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hD1 : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hdeg : (f+Polynomial.C (b.val:ℤ)*X).natDegree≤D := by
    apply Polynomial.natDegree_add_le_of_degree_le hf
    exact (Polynomial.natDegree_C_mul_le (b.val:ℤ) (X:Polynomial ℤ)).trans
      (by simpa only [Polynomial.natDegree_X] using (show 1≤D by omega))
  have hcoeff := coefficientDivisorBoundAt_linear_twist q D hD f (K:ℤ) L (b.val:ℤ) hrel
  rw [twistedPolynomialSum_eq_integerPolynomialSum]
  have h := hcomplete q (f+Polynomial.C (b.val:ℤ)*X) hdeg ((K:ℤ)*(b.val:ℤ)).natAbs hcoeff
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
  have hweight : (Nat.gcd q (K*b.val):ℝ)^(1/(D:ℝ)) ≤ (K:ℝ)*(Nat.gcd b.val q:ℝ) := by
    calc
      _ ≤ (Nat.gcd q (K*b.val):ℝ) := Real.rpow_le_self_of_one_le
        (by exact_mod_cast hgcd) (by simpa only [one_div] using (inv_le_one₀ hDreal).mpr hD1)
      _ ≤ _ := by
        have hh := gcd_mul_bound q K b.val (by omega) hq
        rw [Nat.gcd_comm q b.val] at hh
        exact_mod_cast hh
  apply h.trans
  exact (mul_le_mul_of_nonneg_left hweight (by positivity)).trans_eq (by ring)

theorem polynomial_broad_major_approximation (D K : ℕ) (hD : 2≤D) (hK : 1≤K)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) [NeZero q] (f : Polynomial ℤ)
      (g : Polynomial ℝ) (L : ℤ) (P β : ℝ),
      f.natDegree≤D → (K:ℤ)*f.coeff 1=f.coeff D*L →
      NonnegativeCoefficients g → 0≤P → |β| *g.derivative.eval P≤1/(2*(q:ℝ)) →
      ‖rationalPolynomialWeightedSum q f (ordinaryNumbers P)
          (fun n => e (β*g.eval (n:ℝ)))-
        (integerPolynomialSum q f/(q:ℂ))*polynomialIntegral g P β‖ ≤
        C*(q:ℝ)^(1-1/(D:ℝ)+ε) := by
  let J : ℝ := 1+Real.pi/4
  let C₀ : ℝ := 5+Real.pi/2
  have hJ : 0≤J := by dsimp [J]; positivity
  have hC₀ : 0<C₀ := by dsimp [C₀]; positivity
  have hε2 : 0<ε/2 := by positivity
  obtain ⟨Cs,hCs,hsum⟩ := twistedPolynomialSum_bound D K hD hK hε2
  obtain ⟨Cw,hCw,hweight⟩ := completedFrequencyWeight_normalized_le_rpow hJ hε2
  refine ⟨C₀+Cs*Cw, by positivity, ?_⟩
  intro q _ f g L P β hf hrel hg hP hβ
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hβsmall : |β| *g.derivative.eval P≤1/2 := hβ.trans (by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*q)).mpr
    nlinarith)
  have hquad := polynomial_quadrature g hg hP hβsmall
  have hcomplete : ‖integerPolynomialSum q f‖/(q:ℝ)≤1 := by
    apply (div_le_one hqR).mpr
    exact PolicyCompletionPolynomialHuaBounds.norm_integerPolynomialSum_le q f
  let A := (Finset.univ : Finset (ZMod q)).erase 0
  let w : ℕ → ℂ := fun n => e (β*g.eval (n:ℝ))
  have hlinear (b : ZMod q) (hb : b∈A) :
      ‖completedLinearSum q (ordinaryNumbers P) w b‖ ≤
        2+J*(q:ℝ)/(min b.val (q-b.val):ℕ) :=
    completedLinearSum_polynomial_bound q g hg hP b (Finset.mem_erase.mp hb).1 hβ
  have htwisted (b : ZMod q) : ‖twistedPolynomialSum q f b‖ ≤
      Cs*(q:ℝ)^(1-1/(D:ℝ)+ε/2)*(Nat.gcd b.val q:ℝ) := hsum q f L hf hrel b
  have hnonzero : (q:ℝ)⁻¹*∑ b ∈ A,
      ‖twistedPolynomialSum q f b‖*‖completedLinearSum q (ordinaryNumbers P) w b‖ ≤
      (Cs*Cw)*(q:ℝ)^(1-1/(D:ℝ)+ε) := by
    have hsumBound : (∑ b ∈ A,
        ‖twistedPolynomialSum q f b‖*‖completedLinearSum q (ordinaryNumbers P) w b‖) ≤
        (Cs*(q:ℝ)^(1-1/(D:ℝ)+ε/2))*completedFrequencyWeight q J := by
      rw [completedFrequencyWeight, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b hb
      apply (mul_le_mul (htwisted b) (hlinear b hb) (norm_nonneg _) (by positivity)).trans_eq
      ring
    calc
      _ ≤ (q:ℝ)⁻¹*((Cs*(q:ℝ)^(1-1/(D:ℝ)+ε/2))*completedFrequencyWeight q J) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
      _ = (Cs*(q:ℝ)^(1-1/(D:ℝ)+ε/2))*((q:ℝ)⁻¹*completedFrequencyWeight q J) := by ring
      _ ≤ (Cs*(q:ℝ)^(1-1/(D:ℝ)+ε/2))*(Cw*(q:ℝ)^(ε/2)) :=
        mul_le_mul_of_nonneg_left (hweight q) (by positivity)
      _ = _ := by
        have hpow : (q:ℝ)^(1-1/(D:ℝ)+ε)=(q:ℝ)^(1-1/(D:ℝ)+ε/2)*(q:ℝ)^(ε/2) := by
          rw [← Real.rpow_add hqR]
          congr 1
          ring
        rw [hpow]
        ring
  have hdecomp := rationalPolynomialWeightedSum_main_error_le q f (ordinaryNumbers P) w
    (polynomialIntegral g P β)
  apply hdecomp.trans
  have hzero : (‖integerPolynomialSum q f‖/q)*
      ‖(∑ n ∈ ordinaryNumbers P, w n)-polynomialIntegral g P β‖≤C₀ :=
    (mul_le_mul hcomplete hquad (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  apply (add_le_add hzero hnonzero).trans
  have hDreal : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  have hD1 : (1:ℝ)≤D := by exact_mod_cast (show 1≤D by omega)
  have hinv : 1/(D:ℝ)≤1 := (div_le_one hDreal).mpr hD1
  have hqpow : (1:ℝ)≤(q:ℝ)^(1-1/(D:ℝ)+ε) := Real.one_le_rpow hq1 (by linarith)
  have hc := mul_le_mul_of_nonneg_left hqpow hC₀.le
  nlinarith

#print axioms twistedPolynomialSum_bound
#print axioms polynomial_broad_major_approximation
end Waring.PolicyCompletionPolynomialBroad

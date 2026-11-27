import Waring.SeedCompletionAbsorbedFundamental

/-!
# Uniform normalized efficient differencing after bad-branch absorption

The diagonal supply is proved from integer product boxes at any fixed
positive smoothness power. Every epsilon loss in the finite induction is
included explicitly. There is no assumed efficient-differencing estimate.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionFundamentalScale
open SmoothMoments PolicyCompletionGoodBranch SeedCompletionDiagonalCounts
open SeedCompletionAbsorbedFundamental

theorem fundamental_absorbed_scale {κ : Type*} [DecidableEq κ] (k s : ℕ)
    {B η ε : ℝ} (hB : 0 ≤ B) (hη : 0 < η) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (C : Finset κ) (Z : Finset ℤ) (F : κ → Polynomial ℤ),
      (∀ c ∈ C, (F c).natDegree ≤ k) →
      (∀ c ∈ C, Set.InjOn (F c).eval Z) →
      ∀ P Q R M : ℝ, 1 ≤ M → M ≤ Q → Q ≤ P → P^η ≤ R →
      (∀ a ∈ C ×ˢ Z, derivativeMagnitude F a ≠ 0 ∧
        (derivativeMagnitude F a : ℝ) ≤ P^B) →
      mixedMoment k (s+1) C Z F Q R ≤ K*P^ε*
        ((C.card : ℝ)^2*(Z.card : ℝ)*(M*R)^(2*(s+1))*
            smoothMoment k (2*(s+1)) (Q/M) R+
          (C.card : ℝ)*(M*R)^(2*(s+1)-1)*commonTotal k (s+1) C Z F Q R M) := by
  let δ : ℝ := ε/(2*((s : ℝ)+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*(2*((s : ℝ)+1))=ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by positivity)
  obtain ⟨K,hK,hfinite⟩ := fundamental_absorption_finite (κ := κ) k s hB hδ
  obtain ⟨D,hD,hdensity⟩ := short_smooth_card_absorption hη hδ
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hDp : 0 < D := zero_lt_one.trans_le hD
  refine ⟨(2*K*D)^(s+1),by positivity,?_⟩
  intro C Z F hdeg hinj P Q R M hM hMQ hQP hR hder
  have hQ : 1 ≤ Q := hM.trans hMQ
  have hP : 1 ≤ P := hQ.trans hQP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hR1 : 1 ≤ R := (Real.one_le_rpow hP hη.le).trans hR
  have hRp : 0 < R := zero_lt_one.trans_le hR1
  have hMM : M ≤ M*R := le_mul_of_one_le_right hMp.le hR1
  let b : ℝ := ((smoothNumbers (Q/M) R).card : ℝ)
  let ρ : ℝ := D*P^δ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hρ : 1 ≤ ρ := one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow hP hδ.le)
  have hd : Q ≤ ρ*M*b := by
    have hc : ((smoothNumbers (Q/M) (P^η)).card : ℝ) ≤ b := by
      change ((smoothNumbers (Q/M) (P^η)).card : ℝ) ≤ ((smoothNumbers (Q/M) R).card : ℝ)
      exact_mod_cast Finset.card_le_card (smoothNumbers_mono_cutoff (P := Q/M) hR)
    have hh := hdensity P Q M hM hMQ hQP
    calc
      Q ≤ D*M*P^δ*((smoothNumbers (Q/M) (P^η)).card : ℝ) := hh
      _ ≤ D*M*P^δ*b := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by dsimp [ρ]; ring
  have hf := hfinite C Z F hdeg hinj P Q R M hQ hQP hM hR1 hder ρ hρ hd
  have hpowε : (P^δ)^(2*(s+1))=P^ε := by
    rw [← Real.rpow_mul_natCast hPp.le]
    congr 1
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hδε
  have hdiag : b^(s+1) ≤ smoothMoment k (2*(s+1)) (Q/M) R := by
    rw [smoothMoment_even_eq_frequency]
    exact card_pow_le_frequencyEvenMoment ..
  have hfactor : (K*P^δ*(ρ*M^2*b))^(s+1) =
      (K*D)^(s+1)*P^ε*M^(2*(s+1))*b^(s+1) := by
    have he : K*P^δ*(ρ*M^2*b)=(K*D)*(P^δ)^2*M^2*b := by dsimp [ρ]; ring
    rw [he,mul_pow,mul_pow,mul_pow,← pow_mul,← pow_mul,hpowε]
  have hfactor' : (2*K*P^δ*ρ)^(s+1)=(2*K*D)^(s+1)*P^ε := by
    have he : 2*K*P^δ*ρ=(2*K*D)*(P^δ)^2 := by dsimp [ρ]; ring
    rw [he,mul_pow,← pow_mul,hpowε]
  have hMQ' : M*Q ≤ ρ*M^2*b := by
    have hh := mul_le_mul_of_nonneg_left hd hMp.le
    nlinarith
  have hconst : (K*D)^(s+1) ≤ (2*K*D)^(s+1) := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hfirst : (K*P^δ*(M*Q))^(s+1)*((C.card : ℝ)^2*(Z.card : ℝ)) ≤
      ((2*K*D)^(s+1)*P^ε)*((C.card : ℝ)^2*(Z.card : ℝ)*(M*R)^(2*(s+1))*
        smoothMoment k (2*(s+1)) (Q/M) R) := by
    calc
      _ ≤ (K*P^δ*(ρ*M^2*b))^(s+1)*((C.card : ℝ)^2*(Z.card : ℝ)) := by gcongr
      _ = ((K*D)^(s+1)*P^ε*M^(2*(s+1))*b^(s+1))*
          ((C.card : ℝ)^2*(Z.card : ℝ)) := by rw [hfactor]
      _ ≤ ((2*K*D)^(s+1)*P^ε*(M*R)^(2*(s+1))*
          smoothMoment k (2*(s+1)) (Q/M) R)*((C.card : ℝ)^2*(Z.card : ℝ)) := by
            gcongr
      _ = _ := by ring
  apply hf.trans
  rw [hfactor']
  calc
    _ ≤ ((2*K*D)^(s+1)*P^ε)*((C.card : ℝ)^2*(Z.card : ℝ)*(M*R)^(2*(s+1))*
      smoothMoment k (2*(s+1)) (Q/M) R)+
      ((2*K*D)^(s+1)*P^ε)*(C.card : ℝ)*(M*R)^(2*(s+1)-1)*
        commonTotal k (s+1) C Z F Q R M := add_le_add_right hfirst _
    _ = _ := by ring

#print axioms fundamental_absorbed_scale

open SeedCompletionSharpBackward PolicyCompletionFundamental IntegerDifferencePolynomial

/-- The actual source phase after both the exceptional-branch absorption
and the sharp backward identity. Its two terms have precisely the source
parameter multiplicities, with no loss from summing labels separately. -/
theorem fundamental_sharp_absorbed {κ : Type*} [DecidableEq κ] (k s : ℕ)
    {B η ε : ℝ} (hB : 0 ≤ B) (hη : 0 < η) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C : Finset κ) (params : κ → List (ℤ × ℤ)),
      (∀ c ∈ C, ∀ hm ∈ params c, hm.2 ≠ 0) →
      ∀ (N : ℤ) (Z : Finset ℤ), Z ⊆ Finset.Icc 1 N →
      (∀ c ∈ C, Set.InjOn (powerPolynomial k (params c)).eval Z) →
      ∀ P Q R M : ℝ, 1 ≤ M → M ≤ Q → Q ≤ P → P^η ≤ R →
      (∀ a ∈ C ×ˢ Z,
        derivativeMagnitude (fun c => powerPolynomial k (params c)) a ≠ 0 ∧
        (derivativeMagnitude (fun c => powerPolynomial k (params c)) a : ℝ) ≤ P^B) →
      sourceMixedMoment k (s+1) C params Z Q R ≤
        K*P^ε*(C.card : ℝ)*(M*R)^(2*(s+1)-1)*
          ((C.card : ℝ)*(M*R)*(Z.card : ℝ)*smoothMoment k (2*(s+1)) (Q/M) R+
            nextSmoothCrossIntegral k (s+1) C params
              (CoefficientPower.coefficientBlock Q R M) N (Q/M) R) := by
  obtain ⟨K,hK,hbound⟩ := fundamental_absorbed_scale (κ := κ) k s hB hη hε
  refine ⟨2*K,by positivity,?_⟩
  intro C params hm N Z hZ hinj P Q R M hM hMQ hQP hR hder
  let F := fun c => powerPolynomial k (params c)
  have hdeg : ∀ c ∈ C, (F c).natDegree ≤ k := by
    intro c hc
    exact (powerPolynomial_natDegree_le k (params c) (hm c hc)).trans (Nat.sub_le _ _)
  have hP : 1 ≤ P := (hM.trans hMQ).trans hQP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hR1 : 1 ≤ R := (Real.one_le_rpow hP hη.le).trans hR
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hR0 : 0 ≤ R := zero_le_one.trans hR1
  let W := CoefficientPower.coefficientBlock Q R M
  have hw : ∀ w ∈ W,0 < w := by
    intro w hw
    exact (mem_smoothNumbers.mp (Finset.mem_filter.mp hw).1).1.1
  have hT := commonModulus_sum_le_crossIntegral k (s+1) C params W N Z (Q/M) R hm hw hZ
  have hW := FirstStageTransport.coefficientBlock_card_le (P := Q) (mul_nonneg hM0 hR0)
  have hU : 0 ≤ smoothMoment k (2*(s+1)) (Q/M) R := smoothMoment_nonneg ..
  have hcross := nextSmoothCrossIntegral_nonneg k (s+1) C params W N (Q/M) R
  have hT' : commonTotal k (s+1) C Z F Q R M ≤
      (C.card : ℝ)*(M*R)*(Z.card : ℝ)*smoothMoment k (2*(s+1)) (Q/M) R+
        2*nextSmoothCrossIntegral k (s+1) C params W N (Q/M) R := by
    apply hT.trans
    gcongr
  have hf := hbound C Z F hdeg hinj P Q R M hM hMQ hQP hR hder
  apply hf.trans
  calc
    _ ≤ K*P^ε*((C.card : ℝ)^2*(Z.card : ℝ)*(M*R)^(2*(s+1))*
      smoothMoment k (2*(s+1)) (Q/M) R+
      (C.card : ℝ)*(M*R)^(2*(s+1)-1)*
        ((C.card : ℝ)*(M*R)*(Z.card : ℝ)*smoothMoment k (2*(s+1)) (Q/M) R+
          2*nextSmoothCrossIntegral k (s+1) C params W N (Q/M) R)) := by
            gcongr
    _ = _ := by
      have he : 2*(s+1)=(2*(s+1)-1)+1 := by omega
      have hp : (M*R)^(2*(s+1))=(M*R)^(2*(s+1)-1)*(M*R) :=
        (congrArg (fun n : ℕ => (M*R)^n) he).trans (pow_succ _ _)
      rw [hp]
      dsimp only [W]
      ring

#print axioms fundamental_sharp_absorbed
end Waring.SeedCompletionFundamentalScale

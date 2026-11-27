import Waring.SeedCompletionFundamental
import Waring.SeedCompletionSharpBackward
import Waring.SeedCompletionBadAbsorption
import Waring.SeedCompletionSmoothDensity
import Waring.FirstStageRecurrence

/-!
# The fundamental recurrence after genuine exceptional-branch absorption

The source parameter family and common-modulus solutions remain literal
finite sets throughout. Nonvanishing of the derivative removes its zero
branch. The remaining bad branch is absorbed by induction on the number
of smooth variables using the proved diagonal embedding and uniform
smooth-number density.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionAbsorbedFundamental
open SmoothMoments AuxiliaryL2Grouping PolicyCompletionHolder
open PolicyCompletionGoodBranch PolicyCompletionEndpointPartition
open SeedCompletionFundamental SeedCompletionDiagonalCounts
open SeedCompletionBadAbsorption

def mixedMoment {κ : Type*} (k s : ℕ) (C : Finset κ) (Z : Finset ℤ)
    (F : κ → Polynomial ℤ) (Q R : ℝ) : ℝ :=
  mixedFrequencyEvenMoment (C ×ˢ Z) (polynomialValue F) 1
    (smoothNumbers Q R) (fun n => ((n^k : ℕ) : ℤ)) s

def commonTotal {κ : Type*} [DecidableEq κ] (k s : ℕ)
    (C : Finset κ) (Z : Finset ℤ) (F : κ → Polynomial ℤ)
    (Q R M : ℝ) : ℝ :=
  ∑ w ∈ CoefficientPower.coefficientBlock Q R M,
    ((commonModulusSolutions (C ×ˢ Z) (smoothNumbers (Q/M) R) F s k w).card : ℝ)

theorem mixedMoment_nonneg {κ : Type*} (k s : ℕ) (C : Finset κ) (Z : Finset ℤ)
    (F : κ → Polynomial ℤ) (Q R : ℝ) : 0 ≤ mixedMoment k s C Z F Q R := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  positivity

theorem commonTotal_nonneg {κ : Type*} [DecidableEq κ] (k s : ℕ)
    (C : Finset κ) (Z : Finset ℤ) (F : κ → Polynomial ℤ) (Q R M : ℝ) :
    0 ≤ commonTotal k s C Z F Q R M := Finset.sum_nonneg (fun _ _ => by positivity)

theorem zeroSmoothEndpoints_empty {α : Type*} (s : ℕ) (A : Finset α)
    (Q R : ℝ) (D : α → ℕ) (hD : ∀ a ∈ A, D a ≠ 0) :
    zeroSmoothEndpoints s A Q R D = ∅ := by
  classical
  have hz : A.filter (fun a => D a=0)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    exact hD
  simp only [zeroSmoothEndpoints,hz,Finset.empty_product]

theorem mixedMoment_zero_bound {κ : Type*} (k : ℕ) (C : Finset κ) (Z : Finset ℤ)
    (F : κ → Polynomial ℤ) (Q R : ℝ)
    (hinj : ∀ c ∈ C, Set.InjOn (F c).eval Z) :
    mixedMoment k 0 C Z F Q R ≤ (C.card : ℝ)^2*(Z.card : ℝ) := by
  unfold mixedMoment mixedFrequencyEvenMoment
  simp only [mul_zero,pow_zero,mul_one]
  rw [interval_integral_sq_norm_eq_collision_count]
  exact_mod_cast parameter_center_collision_card_le C Z (polynomialValue F) hinj

/-- The original finite branch estimate with the actual nonzero derivative
condition discharged. Its constants are uniform over all parameter boxes. -/
theorem fundamental_nonzero {κ : Type*} [DecidableEq κ] (k : ℕ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∃ Cg : ℝ, 0 < Cg ∧
      ∀ (C : Finset κ) (Z : Finset ℤ) (F : κ → Polynomial ℤ),
      (∀ c ∈ C, (F c).natDegree ≤ k) →
      ∀ P Q R M : ℝ, 1 ≤ Q → Q ≤ P → 1 ≤ M →
      (∀ a ∈ C ×ˢ Z, derivativeMagnitude F a ≠ 0 ∧
        (derivativeMagnitude F a : ℝ) ≤ P^B) → ∀ s : ℕ,
      mixedMoment k (s+1) C Z F Q R ≤ ((s : ℝ)+3)*
        (((s : ℝ)+1)*(Cb*M*Q*P^ε*mixedMoment k s C Z F Q R)+
          Cg*(C.card : ℝ)*Q^ε*
            ((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*(s+1)-1)*
              commonTotal k (s+1) C Z F Q R M) := by
  classical
  obtain ⟨Cb,hCb,hfund⟩ := fundamental_energy_bound hB hε
  obtain ⟨Cg,hCg,hgood⟩ := goodSmooth_count_le_common_modulus (κ := κ) k k hε
  refine ⟨Cb,hCb,Cg,hCg,?_⟩
  intro C Z F hdeg P Q R M hQ hQP hM hD s
  have hf := hfund P Q R M hQ hQP hM (κ × ℤ) (C ×ˢ Z)
    (polynomialValue F) (derivativeMagnitude F) (fun a ha => (hD a ha).2) k s
  rw [zeroSmoothEndpoints_empty (s+1) (C ×ˢ Z) Q R (derivativeMagnitude F)
    (fun a ha => (hD a ha).1)] at hf
  simp only [collisionPairs,Finset.empty_product,Finset.filter_empty,Finset.card_empty,
    Nat.cast_zero,zero_add] at hf
  have hdegree : ∀ c ∈ (C ×ˢ Z).image Prod.fst,(F c).natDegree ≤ k := by
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact hdeg a.1 (Finset.mem_product.mp ha).1
  have hg := hgood (C ×ˢ Z) F hdegree (s+1) (by omega) Q R M hQ hM
  have hcard : (((C ×ˢ Z).image Prod.fst).card : ℝ) ≤ (C.card : ℝ) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_product.mp ha).1
  apply hf.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_left
  apply hg.trans
  change Cg*(((C ×ˢ Z).image Prod.fst).card : ℝ)*Q^ε*
    ((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*(s+1)-1)*
      commonTotal k (s+1) C Z F Q R M ≤ _
  gcongr
  exact commonTotal_nonneg ..

#print axioms fundamental_nonzero

/-- The finite absorption conclusion before converting its powers into an
ambient epsilon. The displayed density inequality is subsequently supplied
by `short_smooth_card_absorption`, not assumed as a source estimate. -/
theorem fundamental_absorption_finite {κ : Type*} [DecidableEq κ] (k s : ℕ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (C : Finset κ) (Z : Finset ℤ) (F : κ → Polynomial ℤ),
      (∀ c ∈ C, (F c).natDegree ≤ k) →
      (∀ c ∈ C, Set.InjOn (F c).eval Z) →
      ∀ P Q R M : ℝ, 1 ≤ Q → Q ≤ P → 1 ≤ M → 1 ≤ R →
      (∀ a ∈ C ×ˢ Z, derivativeMagnitude F a ≠ 0 ∧
        (derivativeMagnitude F a : ℝ) ≤ P^B) →
      ∀ ρ : ℝ, 1 ≤ ρ →
      Q ≤ ρ*M*((smoothNumbers (Q/M) R).card : ℝ) →
      mixedMoment k (s+1) C Z F Q R ≤
        (K*P^δ*(M*Q))^(s+1)*((C.card : ℝ)^2*(Z.card : ℝ))+
          (2*K*P^δ*ρ)^(s+1)*(C.card : ℝ)*(M*R)^(2*(s+1)-1)*
            commonTotal k (s+1) C Z F Q R M := by
  obtain ⟨Cb,hCb,Cg,hCg,hrec⟩ := fundamental_nonzero (κ := κ) k hB hδ
  let K : ℝ := ((s : ℝ)+3)^2*(Cb+Cg)+1
  have hK : 1 ≤ K := by
    dsimp [K]
    have hh : 0 ≤ ((s : ℝ)+3)^2*(Cb+Cg) := by positivity
    linarith
  refine ⟨K,hK,?_⟩
  intro C Z F hdeg hinj P Q R M hQ hQP hM hR hD ρ hρ hdensity
  have hP : 1 ≤ P := hQ.trans hQP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have hρ0 : 0 ≤ ρ := zero_le_one.trans hρ
  have hPδ : 1 ≤ P^δ := Real.one_le_rpow hP hδ.le
  have hKP : 1 ≤ K*P^δ := one_le_mul_of_one_le_of_one_le hK hPδ
  have hQδ : Q^δ ≤ P^δ := Real.rpow_le_rpow hQ0 hQP hδ.le
  have hW := FirstStageTransport.coefficientBlock_card_le (P := Q) (mul_nonneg hM0 hR0)
  let E : ℕ → ℝ := fun n => mixedMoment k n C Z F Q R
  let T : ℕ → ℝ := fun n => commonTotal k n C Z F Q R M
  let J : ℕ → ℝ := fun n => (M*R)^(2*n-1)*T n
  have hE (n : ℕ) : 0 ≤ E n := mixedMoment_nonneg ..
  have hT (n : ℕ) : 0 ≤ T n := commonTotal_nonneg ..
  have hJ (n : ℕ) : 0 ≤ J n := mul_nonneg (by positivity) (hT n)
  have hstep (i : ℕ) (hi : i ≤ s) :
      E (i+1) ≤ (K*P^δ)*((M*Q)*E i+(C.card : ℝ)*J (i+1)) := by
    have hiR : (i : ℝ) ≤ s := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hprod : ((i : ℝ)+3)*((i : ℝ)+1) ≤ ((s : ℝ)+3)^2 := by
      nlinarith
    have ha : ((i : ℝ)+3)*((i : ℝ)+1)*Cb ≤ K := by
      have h := mul_le_mul_of_nonneg_right hprod hCb.le
      dsimp [K]
      nlinarith [sq_nonneg ((s : ℝ)+3)]
    have hb : ((i : ℝ)+3)*Cg ≤ K := by
      have hbase : (i : ℝ)+3 ≤ ((s : ℝ)+3)^2 := by nlinarith
      have h := mul_le_mul_of_nonneg_right hbase hCg.le
      dsimp [K]
      nlinarith [sq_nonneg ((s : ℝ)+3)]
    have hf := hrec C Z F hdeg P Q R M hQ hQP hM hD i
    apply hf.trans
    calc
      _ = (((i : ℝ)+3)*((i : ℝ)+1)*Cb)*P^δ*(M*Q*E i)+
        (((i : ℝ)+3)*Cg)*Q^δ*(C.card : ℝ)*
          ((CoefficientPower.coefficientBlock Q R M).card : ℝ)^(2*(i+1)-1)*T (i+1) := by
            dsimp only [E,T]
            ring
      _ ≤ K*P^δ*(M*Q*E i)+K*P^δ*(C.card : ℝ)*(M*R)^(2*(i+1)-1)*T (i+1) := by
        gcongr
        · exact mul_nonneg (mul_nonneg hM0 hQ0) (hE i)
        · exact hT (i+1)
      _ = _ := by dsimp only [J]; ring
  have hden : M*Q ≤ ρ*(M*R)^2*((smoothNumbers (Q/M) R).card : ℝ) := by
    have hMM : M ≤ M*R := le_mul_of_one_le_right hM0 hR
    calc
      M*Q ≤ M*(ρ*M*((smoothNumbers (Q/M) R).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hdensity hM0
      _ = ρ*M^2*((smoothNumbers (Q/M) R).card : ℝ) := by ring
      _ ≤ _ := by gcongr
  have hdiag (n : ℕ) : ((smoothNumbers (Q/M) R).card : ℝ)*T n ≤ T (n+1) :=
    commonModulus_sum_mul_le (C ×ˢ Z) (smoothNumbers (Q/M) R) F
      (CoefficientPower.coefficientBlock Q R M) n k
  have hgrowth (n : ℕ) : (M*Q)*J (n+1) ≤ ρ*J (n+2) :=
    weighted_count_growth T (mul_nonneg hM0 hR0) (by positivity) hρ0 hT hden hdiag n
  have habs := absorb_sequence E J hKP (mul_nonneg hM0 hQ0) (by positivity) hρ
    hE hJ s hstep (fun n _ => hgrowth n)
  have hzero := mixedMoment_zero_bound k C Z F Q R hinj
  apply habs.trans
  change (K*P^δ*(M*Q))^(s+1)*E 0+(2*(K*P^δ)*ρ)^(s+1)*(C.card : ℝ)*J (s+1) ≤ _
  calc
    _ ≤ (K*P^δ*(M*Q))^(s+1)*((C.card : ℝ)^2*(Z.card : ℝ))+
      (2*(K*P^δ)*ρ)^(s+1)*(C.card : ℝ)*J (s+1) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hzero (by positivity)) _
    _ = _ := by dsimp only [J]; ring

#print axioms fundamental_absorption_finite
end Waring.SeedCompletionAbsorbedFundamental

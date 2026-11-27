import Waring.RestrictedSmoothScaleChoice
import Waring.EndgameCompletionBroadArcs

/-! # Actual wrapped major regions and the optimized small-scale estimate -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization EndgameCompletion

theorem periodicMajorRegion_smooth_integral_le (k s : ℕ) (S : Finset ℕ+) (P R δ : ℝ) :
    (∫ x in periodicMajorRegion S δ,‖smoothWeyl k P R x‖^s) ≤ smoothMoment k s P R := by
  have hF := (continuous_smoothWeyl k P R).norm.pow s
  calc
    _ ≤ ∫ x in Set.Ioc (0 : ℝ) 1,‖smoothWeyl k P R x‖^s :=
      setIntegral_mono_set hF.integrableOn_Ioc (Filter.Eventually.of_forall (fun x => by positivity))
        (Filter.Eventually.of_forall (fun x hx => periodicMajorRegion_subset S δ hx))
    _ = _ := by rw [smoothMoment,intervalIntegral.integral_of_le zero_le_one]

theorem restricted_smooth_small_scale {k s : ℕ} (hs : 1 ≤ s) {lam B ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ S : Finset ℕ+,∀ Q T R L : ℝ,
      1 ≤ Q → Q ≤ P^B → 1 ≤ T → T^k=4*Q^2 →
      1 ≤ R → R ≤ P^η → T*R^2 ≤ P →
      0 ≤ L → (s : ℝ)+(lam-(s : ℝ)+(k : ℝ)) ≤ L →
      (∀ q ∈ S,(q : ℝ) ≤ Q) →
      (∫ x in periodicMajorRegion S (Q/P^k),‖smoothWeyl k P R x‖^s) ≤
        C*P^((s : ℝ)-(k : ℝ)+ε)*T^(lam-(s : ℝ)+(k : ℝ))*R^L := by
  obtain ⟨η,hη,A,hA,hbound⟩ := smooth_arcs_admissible_unoptimized hs hadm hlam hB hε
  refine ⟨η,hη,4*A,by positivity,?_⟩
  intro P hP S Q T R L hQ hQP hT hTpow hR hRP hsmall hL0 hL hSQ
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hδ : 0 ≤ Q/P^k := by positivity
  obtain ⟨hRM,hM,hMR⟩ := optimizedScale_bounds hP hT hR hsmall
  have hsep : ∀ b ∈ orderedBlocks (optimizedScale P T R) R,
      4*Q*((b.2 : ℝ)^k*(Q/P^k)) ≤ 1 := by
    intro b hb
    exact optimizedScale_separation k hPp hTp hRp (Nat.cast_nonneg b.2) hTpow
      (orderedBlocks_bounds hM hR hb).2.2.1
  have hb := hbound P hP S Q (Q/P^k) R (optimizedScale P T R)
    hQ hδ hR hRP hM hMR hSQ (fun q hq => (hSQ q hq).trans hQP) hsep
  have hper : Function.Periodic (fun x => ‖smoothWeyl k P R x‖^s) 1 := by
    intro x
    dsimp only
    rw [periodic_smoothWeyl k P R x]
  calc
    _ ≤ 2*∑ q ∈ S,rationalArcSum (q : ℕ) (fun x => ‖smoothWeyl k P R x‖^s) (Q/P^k) :=
      periodicMajorRegion_integral_le S hδ ((continuous_smoothWeyl k P R).norm.pow s)
        hper (fun x => by positivity)
    _ ≤ 2*(A*P^ε*(Q*(Q/P^k)*(optimizedScale P T R)^s+
        (optimizedScale P T R*R)^s*(P/optimizedScale P T R)^lam/(optimizedScale P T R)^k)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 2*(A*P^ε*(2*P^((s : ℝ)-(k : ℝ))*T^(lam-(s : ℝ)+(k : ℝ))*R^L)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (optimizedScale_total k s hP hT hR hlam hTpow hL0 hL) (by positivity))
        (by norm_num)
    _ = _ := by rw [Real.rpow_add hPp]; ring

#print axioms restricted_smooth_small_scale
end Waring.RestrictedSmoothArcs

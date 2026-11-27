import Waring.RestrictedSmoothRegion

/-! # Uniform restricted smooth mean from an actual admissible exponent

The arithmetic decomposition, Holder estimates, arc scaling, shorter
moments, and both cutoff regimes are proved in the imported development.
The explicit numeric conditions on the full exponent are sufficient for
the frozen auxiliary moments used in this project.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments EndgameCompletion

theorem restricted_smooth_mean_scale {k s : ℕ} (hs : 1 ≤ s) {lam B ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam)
    (hDelta : 0 ≤ lam-(s : ℝ)+(k : ℝ)) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ S : Finset ℕ+,∀ Q T R : ℝ,
      1 ≤ Q → Q ≤ P^B → 1 ≤ T → T^k=4*Q^2 → 1 ≤ R → R ≤ P^η →
      (∀ q ∈ S,(q : ℝ) ≤ Q) →
      (∫ x in periodicMajorRegion S (Q/P^k),‖smoothWeyl k P R x‖^s) ≤
        C*P^((s : ℝ)-(k : ℝ)+ε)*T^(lam-(s : ℝ)+(k : ℝ)) := by
  obtain ⟨η₁,hη₁,A,hA,hsmall⟩ := restricted_smooth_small_scale hs hadm hlam hB (half_pos hε)
  obtain ⟨η₂,hη₂,C₂,hC₂,hfull⟩ := admissibleExponent_uniform_shorter hadm (half_pos hε)
  let D := lam-(s : ℝ)+(k : ℝ)
  let L := (s : ℝ)+2*D+1
  have hLp : 0 < L := by dsimp [L,D]; have := Nat.cast_nonneg (α := ℝ) s; linarith
  let η := min η₁ (min η₂ (ε/(2*L)))
  have hη : 0 < η := lt_min hη₁ (lt_min hη₂ (div_pos hε (by positivity)))
  have hηa : η ≤ η₁ := min_le_left _ _
  have hηb : η ≤ η₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hηL : η ≤ ε/(2*L) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,hη,A+C₂,add_pos hA hC₂,?_⟩
  intro P hP S Q T R hQ hQP hT hTpow hR hRP hSQ
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hRP₁ : R ≤ P^η₁ := hRP.trans (Real.rpow_le_rpow_of_exponent_le hP hηa)
  have hRP₂ : R ≤ P^η₂ := hRP.trans (Real.rpow_le_rpow_of_exponent_le hP hηb)
  have hRloss : R^L ≤ P^(ε/2) := smoothness_loss_absorption hP
    (zero_le_one.trans hR) hRP hLp hηL
  have habsorb : P^((s : ℝ)-(k : ℝ)+ε/2)*R^L ≤ P^((s : ℝ)-(k : ℝ)+ε) := by
    calc
      _ ≤ P^((s : ℝ)-(k : ℝ)+ε/2)*P^(ε/2) :=
        mul_le_mul_of_nonneg_left hRloss (by positivity)
      _ = _ := by rw [← Real.rpow_add hPp]; congr 1; ring
  have hX0 : 0 ≤ P^((s : ℝ)-(k : ℝ)+ε)*T^D := by positivity
  by_cases hsmallScale : T*R^2 ≤ P
  · have hL : (s : ℝ)+D ≤ L := by dsimp [L,D]; linarith
    have h := hsmall P hP S Q T R L hQ hQP hT hTpow hR hRP₁ hsmallScale hLp.le hL hSQ
    calc
      _ ≤ A*P^((s : ℝ)-(k : ℝ)+ε/2)*T^D*R^L := h
      _ = A*T^D*(P^((s : ℝ)-(k : ℝ)+ε/2)*R^L) := by ring
      _ ≤ A*T^D*P^((s : ℝ)-(k : ℝ)+ε) := mul_le_mul_of_nonneg_left habsorb (by positivity)
      _ = A*(P^((s : ℝ)-(k : ℝ)+ε)*T^D) := by ring
      _ ≤ (A+C₂)*(P^((s : ℝ)-(k : ℝ)+ε)*T^D) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) hX0
      _ = _ := by ring
  · have hL : 2*D ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) s; linarith
    have hpD : P^D ≤ T^D*R^L := by
      apply (large_scale_power hPp.le hTp.le (zero_le_one.trans hR) hDelta hsmallScale).trans
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR hL) (by positivity)
    have hPlam : P^lam=P^((s : ℝ)-(k : ℝ))*P^D := by
      rw [← Real.rpow_add hPp]
      congr 1
      dsimp [D]
      ring
    calc
      _ ≤ smoothMoment k s P R := periodicMajorRegion_smooth_integral_le k s S P R (Q/P^k)
      _ ≤ C₂*P^(ε/2)*P^lam := hfull P hP R hR hRP₂ P hP le_rfl
      _ = C₂*P^(ε/2)*(P^((s : ℝ)-(k : ℝ))*P^D) := by rw [hPlam]
      _ ≤ C₂*P^(ε/2)*(P^((s : ℝ)-(k : ℝ))*(T^D*R^L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpD (by positivity)) (by positivity)
      _ = C₂*T^D*(P^((s : ℝ)-(k : ℝ)+ε/2)*R^L) := by rw [Real.rpow_add hPp]; ring
      _ ≤ C₂*T^D*P^((s : ℝ)-(k : ℝ)+ε) := mul_le_mul_of_nonneg_left habsorb (by positivity)
      _ = C₂*(P^((s : ℝ)-(k : ℝ)+ε)*T^D) := by ring
      _ ≤ (A+C₂)*(P^((s : ℝ)-(k : ℝ)+ε)*T^D) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) hX0
      _ = _ := by ring

/-- The actual restricted mean has the Brudern--Wooley exponent
`s-k+epsilon` in P and `2*(lam-s+k)/k` in the arc cutoff Q.
One positive smoothness power works uniformly in every displayed parameter. -/
theorem restricted_smooth_major_mean {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s)
    {lam B ε : ℝ} (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam)
    (hDelta : 0 ≤ lam-(s : ℝ)+(k : ℝ)) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ S : Finset ℕ+,∀ Q R : ℝ,1 ≤ Q → Q ≤ P^B → 1 ≤ R → R ≤ P^η →
      (∀ q ∈ S,(q : ℝ) ≤ Q) →
      (∫ x in periodicMajorRegion S (Q/P^k),‖smoothWeyl k P R x‖^s) ≤
        C*P^((s : ℝ)-(k : ℝ)+ε)*Q^(2*(lam-(s : ℝ)+(k : ℝ))/(k : ℝ)) := by
  obtain ⟨η,hη,A,hA,hbound⟩ := restricted_smooth_mean_scale hs hadm hlam hDelta hB hε
  let e := 2*(lam-(s : ℝ)+(k : ℝ))/(k : ℝ)
  refine ⟨η,hη,A*(2 : ℝ)^e,by positivity,?_⟩
  intro P hP S Q R hQ hQP hR hRP hSQ
  have h := hbound P hP S Q (arcRootScale k Q) R hQ hQP
    (arcRootScale_one_le k hQ) (arcRootScale_pow hk hQ) hR hRP hSQ
  rw [arcRootScale_rpow k hQ] at h
  calc
    _ ≤ A*P^((s : ℝ)-(k : ℝ)+ε)*((2 : ℝ)^e*Q^e) := h
    _ = _ := by ring

#print axioms restricted_smooth_major_mean
end Waring.RestrictedSmoothArcs

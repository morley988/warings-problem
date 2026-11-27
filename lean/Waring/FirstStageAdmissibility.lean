import Waring.FirstStageEndpoint

/-!
# From the actual first-stage recurrence to admissible exponents

The epsilon and smoothness choices are simultaneous. This file keeps the
literal cross integral in the hypotheses of its general composition rule,
then supplies its endpoint estimate without any analytic assumption.
-/

noncomputable section
namespace Waring.FirstStageTransport
open SmoothMoments

def CrossExponent (k s : ℕ) (φ χ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧
    ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
    ∀ R : ℝ, 1 ≤ R → R ≤ P^η → firstCross k s P R (P^φ) ≤ C*P^(χ+ε)

theorem rpow_quotient_scale {P : ℝ} (hP : 0 < P) (φ lam : ℝ) :
    (P/P^φ)^lam = P^((1-φ)*lam) := by
  have he : P/P^φ=P^(1-φ) := by rw [Real.rpow_sub hP,Real.rpow_one]
  rw [he,← Real.rpow_mul hP.le]

theorem first_stage_admissible {k s : ℕ} (hk : 0 < k) {lam φ χ θ : ℝ}
    (hlam : AdmissibleExponent k (2*(s+1)) lam)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1)
    (hcross : CrossExponent k (s+1) φ χ)
    (hbad : 1+φ+lam ≤ θ)
    (hdiag : 1+lam+(2*((s : ℝ)+1)-lam)*φ ≤ θ)
    (hnext : (2*(s : ℝ)+1)*φ+χ ≤ θ) :
    AdmissibleExponent k (2*(s+2)) θ := by
  intro ε hε
  let δ : ℝ := ε/(2*(s : ℝ)+4)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ*(2*(s : ℝ)+4)=ε := by
    dsimp [δ]
    exact div_mul_cancel₀ ε (by positivity)
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h2δε : 2*δ ≤ ε := by nlinarith
  obtain ⟨C₀,hC₀,P₀,hP₀,hrec⟩ := first_stage_recurrence k s hk hδ
  obtain ⟨η₁,hη₁,C₁,hC₁,hbound⟩ := admissibleExponent_uniform_shorter hlam hδ
  obtain ⟨η₂,hη₂,C₂,hC₂,P₂,hP₂,hX⟩ := hcross δ hδ
  let η : ℝ := min η₁ (min η₂ δ)
  have hη : 0 < η := lt_min hη₁ (lt_min hη₂ hδ)
  refine ⟨η,hη,C₀*(2*C₁+C₂),by positivity,max P₀ P₂,
    hP₀.trans (le_max_left _ _),?_⟩
  intro P hPP R hR hRP
  have hPP₀ := (le_max_left P₀ P₂).trans hPP
  have hPP₂ := (le_max_right P₀ P₂).trans hPP
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hR₁ : R ≤ P^η₁ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hR₂ : R ≤ P^η₂ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_left _ _)))
  have hRδ : R ≤ P^δ := hRP.trans
    (Real.rpow_le_rpow_of_exponent_le hP ((min_le_right _ _).trans (min_le_right _ _)))
  have hM : 1 ≤ P^φ := Real.one_le_rpow hP hφ0
  have hMP : P^φ ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hφ1
  have hMpos : 0 < P^φ := Real.rpow_pos_of_pos hPpos _
  have hY : 1 ≤ P/P^φ := (one_le_div hMpos).mpr hMP
  have hYP : P/P^φ ≤ P := div_le_self hPpos.le hM
  have hJ := hbound P hP R hR hR₁ P hP le_rfl
  have hJ' := hbound P hP R hR hR₁ (P/P^φ) hY hYP
  have hcross' := hX P hPP₂ R hR hR₂
  have h₁ : P^φ*P^(1+δ)*smoothMoment k (2*(s+1)) P R ≤ C₁*P^(θ+ε) := by
    calc
      _ ≤ P^φ*P^(1+δ)*(C₁*P^δ*P^lam) := by gcongr
      _ = C₁*P^(φ+(1+δ)+δ+lam) := by
        calc
          _ = C₁*(P^φ*P^(1+δ)*P^δ*P^lam) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₁*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC₁.le
  have h₂ : P^(1+δ)*(P^φ*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/P^φ) R ≤
      C₁*P^(θ+ε) := by
    calc
      _ ≤ P^(1+δ)*(P^φ*P^δ)^(2*(s+1))*(C₁*P^δ*(P/P^φ)^lam) := by
        gcongr
        exact smoothMoment_nonneg ..
      _ = C₁*P^((1+δ)+(φ+δ)*(2*((s : ℝ)+1))+δ+(1-φ)*lam) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le,
          rpow_quotient_scale hPpos]
        push_cast
        calc
          _ = C₁*(P^(1+δ)*P^((φ+δ)*(2*((s : ℝ)+1)))*P^δ*P^((1-φ)*lam)) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₁*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)) hC₁.le
  have h₃ : P^δ*(P^φ*R)^(2*s+1)*firstCross k (s+1) P R (P^φ) ≤ C₂*P^(θ+ε) := by
    calc
      _ ≤ P^δ*(P^φ*P^δ)^(2*s+1)*(C₂*P^(χ+δ)) := by
        gcongr
        exact firstCross_nonneg ..
      _ = C₂*P^(δ+(φ+δ)*(2*(s : ℝ)+1)+(χ+δ)) := by
        rw [← Real.rpow_add hPpos,← Real.rpow_mul_natCast hPpos.le]
        push_cast
        calc
          _ = C₂*(P^δ*P^((φ+δ)*(2*(s : ℝ)+1))*P^(χ+δ)) := by ring
          _ = _ := by rw [← Real.rpow_add hPpos,← Real.rpow_add hPpos]
      _ ≤ C₂*P^(θ+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by
          have he : δ+(φ+δ)*(2*(s : ℝ)+1)+(χ+δ) =
              ((2*(s : ℝ)+1)*φ+χ)+ε-δ := by rw [← hδε]; ring
          rw [he]
          linarith)) hC₂.le
  calc
    _ ≤ C₀*(P^φ*P^(1+δ)*smoothMoment k (2*(s+1)) P R+
        P^(1+δ)*(P^φ*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/P^φ) R+
        P^δ*(P^φ*R)^(2*s+1)*firstCross k (s+1) P R (P^φ)) :=
      hrec P hPP₀ R (P^φ) hR hM
    _ ≤ C₀*(C₁*P^(θ+ε)+C₁*P^(θ+ε)+C₂*P^(θ+ε)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add h₁ h₂) h₃) hC₀.le
    _ = _ := by ring

/-- At the endpoint, the actual cross integral vanishes. Any real
exponent is therefore available for this term. -/
theorem crossExponent_endpoint {k : ℕ} (hk : 0 < k) (s : ℕ)
    {φ : ℝ} (hφ : 0 ≤ φ) (hφk : 1 ≤ φ*(k : ℝ)) (χ : ℝ) :
    CrossExponent k s φ χ := by
  intro ε hε
  refine ⟨1,by norm_num,1,by norm_num,1,le_rfl,?_⟩
  intro P hP R hR hRP
  have hM := Real.one_le_rpow hP hφ
  have hMk : P ≤ (P^φ)^k := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hP)]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hφk
  rw [firstCross_eq_zero hk s hP hM hMk]
  positivity

/-- A genuine endpoint update for every degree, using only an already
admissible lower moment and the empty next-height range. -/
theorem endpoint_admissible {k s : ℕ} (hk : 0 < k) {lam : ℝ}
    (hlam : AdmissibleExponent k (2*(s+1)) lam)
    (hlamupper : lam ≤ 2*(s : ℝ)+1) :
    AdmissibleExponent k (2*(s+2))
      (1+lam+(2*((s : ℝ)+1)-lam)/(k : ℝ)) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  let φ : ℝ := 1/(k : ℝ)
  let θ : ℝ := 1+lam+(2*((s : ℝ)+1)-lam)/(k : ℝ)
  have hφ0 : 0 ≤ φ := by dsimp [φ]; positivity
  have hφ1 : φ ≤ 1 := by dsimp [φ]; exact (div_le_one hkpos).mpr hk1
  have hφk : 1 ≤ φ*(k : ℝ) := by dsimp [φ]; rw [div_mul_cancel₀ _ hkpos.ne']
  apply first_stage_admissible hk hlam hφ0 hφ1
    (crossExponent_endpoint hk (s+1) hφ0 hφk (θ-(2*(s : ℝ)+1)*φ))
  · dsimp only [φ,θ]
    have h := div_le_div_of_nonneg_right (show 1 ≤ 2*((s : ℝ)+1)-lam by linarith) hkpos.le
    linarith
  · dsimp only [φ,θ]
    apply le_of_eq
    ring
  · dsimp only [θ]
    linarith

theorem admissible_six_endpoint {k : ℕ} (hk : 2 ≤ k) :
    AdmissibleExponent k 6 (3+2/(k : ℝ)) := by
  have H := endpoint_admissible (s := 1) (by omega : 0 < k)
    (FourthMomentSeed.admissibleExponent_four hk) (by norm_num)
  norm_num at H ⊢
  exact H

theorem admissible_eight_endpoint {k : ℕ} (hk : 2 ≤ k) :
    AdmissibleExponent k 8 (4+2/(k : ℝ)+(3-2/(k : ℝ))/(k : ℝ)) := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk2 : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hratio : 2/(k : ℝ) ≤ 1 := (div_le_one hkpos).mpr hk2
  have H := endpoint_admissible (s := 2) (by omega : 0 < k)
    (admissible_six_endpoint hk) (by norm_num; linarith)
  convert H using 1 <;> push_cast <;> ring

#print axioms first_stage_admissible
#print axioms endpoint_admissible
#print axioms admissible_six_endpoint
#print axioms admissible_eight_endpoint
end Waring.FirstStageTransport

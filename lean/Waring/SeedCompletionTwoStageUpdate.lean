import Waring.SeedCompletionSecondRecurrence
import Waring.SeedCompletionSecondHolder
import Waring.SeedCompletionSourceAdmissibility

/-! # Two-stage admissible-exponent updates from proved actual moments -/
noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionInitialMixed
open FirstStageTransport

theorem first_cross_power {k s u t : ℕ} {φ lam κ : ℝ}
    (hφ : 0 ≤ φ) (hφ1 : φ ≤ 1) (hsplit : u+t=2*s)
    (hF : SourcePowerBound (firstMixed k u φ) κ)
    (hU : AdmissibleExponent k (2*t) lam) :
    SourcePowerBound (fun P R => firstCross k s P R (P^φ))
      ((κ+(1-φ)*lam)/2) := by
  have hq0 : 0 ≤ 1-φ := by linarith
  have hq1 : 1-φ ≤ 1 := by linarith
  have hUs : SourcePowerBound (fun P R => smoothMoment k (2*t) (P^(1-φ)) R) ((1-φ)*lam) := by
    simpa only [one_mul] using admissible_shorter_source_bound hU (le_refl (1 : ℝ)) hq0 hq1
  have hG := (hF.rpow (by norm_num : (0 : ℝ) ≤ 1/2)
      (fun P R _ _ => firstMixed_nonneg ..)).mul
    (hUs.rpow (by norm_num : (0 : ℝ) ≤ 1/2) (fun P R _ _ => smoothMoment_nonneg ..))
  have hG' : SourcePowerBound
      (fun P R => (firstMixed k u φ P R)^(1/2 : ℝ)*
        (smoothMoment k (2*t) (P^(1-φ)) R)^(1/2 : ℝ)) ((κ+(1-φ)*lam)/2) := by
    convert hG using 1 <;> ring
  apply hG'.of_eventually_le
  intro η hη
  obtain ⟨P₀,hP₀,hbound⟩ := fixed_power_eventually_two hη
  refine ⟨P₀,hP₀,?_⟩
  intro P hPP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have H := firstCross_le_source_mixed k s u t hsplit hP (Real.one_le_rpow hP hφ) (hbound P hPP)
  have hQ : P/P^φ=P^(1-φ) := by rw [Real.rpow_sub hPp,Real.rpow_one]
  rw [power_height hPp,hQ] at H
  rw [abs_of_nonneg (firstCross_nonneg ..)]
  exact H.trans (le_abs_self _)

/-- A numerical two-stage witness becomes a genuine admissible exponent.
The three available smooth moments may include the current target moment;
finite iteration can improve them without assuming a limiting exponent. -/
theorem two_stage_admissible {k s u t : ℕ} {φ₁ φ₂ lams lamu lamt χ γ θ : ℝ}
    (hk : 2 ≤ k)
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/(k : ℝ))
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/(k : ℝ))
    (hsplit : (u+1)+t=2*(s+1))
    (hS : AdmissibleExponent k (2*(s+1)) lams)
    (hU : AdmissibleExponent k (2*(u+1)) lamu)
    (hT : AdmissibleExponent k (2*t) lamt)
    (hX : SourcePowerBound (secondCross k (u+1) φ₁ φ₂) χ)
    (hinnerdiag : 2+(1-(k : ℝ))*φ₁+φ₂+(1-φ₁-φ₂)*lamu ≤ γ)
    (hinnernext : χ ≤ γ)
    (hbad : 1+φ₁+lams ≤ θ)
    (hdiag : 1+lams+(2*((s : ℝ)+1)-lams)*φ₁ ≤ θ)
    (hnext : (2*(s : ℝ)+1)*φ₁+
      (1+(1-(k : ℝ))*φ₁+(2*((u : ℝ)+1)-1)*φ₂+γ+(1-φ₁)*lamt)/2 ≤ θ) :
    AdmissibleExponent k (2*(s+2)) θ := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hφ₁one : φ₁ ≤ 1 := hφ₁k.trans ((div_le_one hkpos).mpr hk1)
  have hF := first_mixed_power hk hφ₁ hφ₁k hφ₂ hφ₂k hU hX hinnerdiag hinnernext
  have hC := first_cross_power hφ₁ hφ₁one hsplit hF hT
  exact first_stage_admissible_source (by omega) hS hφ₁ hφ₁one hC hbad hdiag hnext

#print axioms first_cross_power
#print axioms two_stage_admissible
end Waring.SeedCompletionSecondScales

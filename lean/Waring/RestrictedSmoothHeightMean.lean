import Waring.RestrictedSmoothHeight

/-! # Actual intrinsic-height restricted means, uniform in every cutoff -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.RestrictedSmoothArcs
open SmoothMoments EndgameCompletion

theorem height_sublevel_smooth_integral_le (k s : ℕ) (P R V Q : ℝ) :
    (∫ x in Set.Ioc (0 : ℝ) 1 ∩ {x | RationalHeight.height V x ≤ Q},
      ‖smoothWeyl k P R x‖^s) ≤ smoothMoment k s P R := by
  have hF := (continuous_smoothWeyl k P R).norm.pow s
  calc
    _ ≤ ∫ x in Set.Ioc (0 : ℝ) 1,‖smoothWeyl k P R x‖^s :=
      setIntegral_mono_set hF.integrableOn_Ioc (Filter.Eventually.of_forall (fun x => by positivity))
        (Filter.Eventually.of_forall (fun _ hx => hx.1))
    _ = _ := by rw [smoothMoment,intervalIntegral.integral_of_le zero_le_one]

/-- No upper restriction on the height cutoff is needed: above the
polynomial range, the full admissible moment gives the displayed estimate. -/
theorem restricted_smooth_height_mean {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s)
    {lam ε : ℝ} (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam)
    (hDelta : 0 ≤ lam-(s : ℝ)+(k : ℝ)) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ Q R : ℝ,1 ≤ Q → 1 ≤ R → R ≤ P^η →
      (∫ x in Set.Ioc (0 : ℝ) 1 ∩ {x | RationalHeight.height (P^k) x ≤ Q},
        ‖smoothWeyl k P R x‖^s) ≤
        C*P^((s : ℝ)-(k : ℝ)+ε)*Q^(2*(lam-(s : ℝ)+(k : ℝ))/(k : ℝ)) := by
  obtain ⟨η₁,hη₁,A,hA,hmajor⟩ := restricted_smooth_major_mean hk hs hadm hlam hDelta
    (B := (k : ℝ)) (by positivity) hε
  obtain ⟨η₂,hη₂,D,hD,hfull⟩ := admissibleExponent_uniform_shorter hadm hε
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,A+D,add_pos hA hD,?_⟩
  intro P hP Q R hQ hR hRP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hRP₁ : R ≤ P^η₁ := hRP.trans (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _))
  have hRP₂ : R ≤ P^η₂ := hRP.trans (Real.rpow_le_rpow_of_exponent_le hP (min_le_right _ _))
  let delta := lam-(s : ℝ)+(k : ℝ)
  let e := 2*delta/(k : ℝ)
  have he : 0 ≤ e := div_nonneg (mul_nonneg (by norm_num) hDelta) (Nat.cast_nonneg _)
  have hprod : 0 ≤ P^((s : ℝ)-(k : ℝ)+ε)*Q^e := by positivity
  by_cases hQP : Q ≤ P^(k : ℝ)
  · have hb := hmajor P hP (broadDenominators Q) Q R hQ hQP hR hRP₁
      (fun q hq => (mem_broadDenominators Q q).mp hq)
    have hsubset := height_sublevel_subset_periodicMajorRegion (pow_pos hPp k) hQ
    have hF := (continuous_smoothWeyl k P R).norm.pow s
    calc
      _ ≤ ∫ x in periodicMajorRegion (broadDenominators Q) (Q/P^k),‖smoothWeyl k P R x‖^s :=
        setIntegral_mono_set
          (hF.integrableOn_Icc.mono_set
            ((periodicMajorRegion_subset _ _).trans Set.Ioc_subset_Icc_self))
          (Filter.Eventually.of_forall (fun x => by positivity))
          (Filter.Eventually.of_forall (fun x hx => hsubset hx))
      _ ≤ A*P^((s : ℝ)-(k : ℝ)+ε)*Q^e := hb
      _ ≤ (A+D)*P^((s : ℝ)-(k : ℝ)+ε)*Q^e := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hD.le : A ≤ A+D) hprod
  · have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hke : (k : ℝ)*e=2*delta := by dsimp [e]; field_simp
    have hPQ : P^delta ≤ Q^e := by
      calc
        _ ≤ P^((k : ℝ)*e) := Real.rpow_le_rpow_of_exponent_le hP (by rw [hke]; linarith)
        _ = (P^(k : ℝ))^e := Real.rpow_mul hPp.le _ _
        _ ≤ Q^e := Real.rpow_le_rpow (by positivity) (le_of_not_ge hQP) he
    have hsplit : P^ε*P^lam=P^((s : ℝ)-(k : ℝ)+ε)*P^delta := by
      rw [← Real.rpow_add hPp,← Real.rpow_add hPp]
      congr 1
      dsimp [delta]
      ring
    calc
      _ ≤ smoothMoment k s P R := height_sublevel_smooth_integral_le k s P R (P^k) Q
      _ ≤ D*P^ε*P^lam := hfull P hP R hR hRP₂ P hP le_rfl
      _ = D*(P^((s : ℝ)-(k : ℝ)+ε)*P^delta) := by rw [mul_assoc,hsplit]
      _ ≤ D*(P^((s : ℝ)-(k : ℝ)+ε)*Q^e) := by gcongr
      _ ≤ (A+D)*(P^((s : ℝ)-(k : ℝ)+ε)*Q^e) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) hprod
      _ = _ := by ring

/-- The exact measure and nonnegative integrand used by the terminal
integration theorem, with constants chosen before every length and cutoff. -/
theorem restricted_smooth_height_lintegral {k s : ℕ} (hk : 1 ≤ k) (hs : 1 ≤ s)
    {lam ε : ℝ} (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam)
    (hDelta : 0 ≤ lam-(s : ℝ)+(k : ℝ)) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ Q R : ℝ,1 ≤ Q → 1 ≤ R → R ≤ P^η →
      (∫⁻ x in {x | RationalHeight.height (P^k) x ≤ Q},
        ENNReal.ofReal (‖smoothWeyl k P R x‖^s) ∂(volume.restrict (Set.Ioc 0 1))) ≤
        ENNReal.ofReal (C*P^((s : ℝ)-(k : ℝ)+ε))*
          ENNReal.ofReal (Q^(2*(lam-(s : ℝ)+(k : ℝ))/(k : ℝ))) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := restricted_smooth_height_mean hk hs hadm hlam hDelta hε
  refine ⟨η,hη,C,hC,?_⟩
  intro P hP Q R hQ hR hRP
  have hPp := zero_lt_one.trans_le hP
  have hF := (continuous_smoothWeyl k P R).norm.pow s
  rw [Measure.restrict_restrict (RationalHeight.measurableSet_height_le (pow_pos hPp k)),
    Set.inter_comm,
    ← ofReal_integral_eq_lintegral_ofReal
      (hF.integrableOn_Icc.mono_set
        (Set.inter_subset_left.trans Set.Ioc_subset_Icc_self))
      (Filter.Eventually.of_forall (fun x => pow_nonneg (norm_nonneg _) s)),
    ← ENNReal.ofReal_mul (mul_nonneg hC.le (by positivity))]
  exact ENNReal.ofReal_le_ofReal (hbound P hP Q R hQ hR hRP)

#print axioms restricted_smooth_height_mean
#print axioms restricted_smooth_height_lintegral
end Waring.RestrictedSmoothArcs

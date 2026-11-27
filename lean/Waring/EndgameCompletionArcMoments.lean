import Waring.EndgameCompletionBroad
import Waring.EndgameCompletionMajorMoment
import Waring.RestrictedSmoothArcOperations

/-!
# Actual ordinary moments on the broad rational arcs

The elementary approximation is integrated on the literal reduced-residue
bands. The complete arithmetic series and the oscillatory integral are
already proved summable; the error has a strict power saving at both
ordinary moments required by the Waring endgame.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Waring.EndgameCompletion
open MixedEndgame RestrictedSmoothArcs

def broadArcWidth (k : ℕ) (P : ℝ) : ℝ := (2*(k : ℝ)*P^(k-1))⁻¹

theorem broadArcWidth_pos {k : ℕ} (hk : 1≤k) {P : ℝ} (hP : 0<P) :
    0<broadArcWidth k P := by
  unfold broadArcWidth
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  positivity

theorem broadArcWidth_derivative {k : ℕ} (hk : 1≤k) {P : ℝ} (hP : 0<P) :
    broadArcWidth k P*(k : ℝ)*P^(k-1)=1/2 := by
  have hkR : (k : ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  unfold broadArcWidth
  field_simp

theorem broad_band_derivative {k : ℕ} (hk : 1≤k) {P : ℝ} (hP : 0<P)
    (q : ℕ) [NeZero q] {β : ℝ}
    (hβ : β∈Set.Icc (-(broadArcWidth k P/(q : ℝ))) (broadArcWidth k P/(q : ℝ))) :
    |β| *(k : ℝ)*P^(k-1)≤1/(2*(q : ℝ)) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hb : |β|≤broadArcWidth k P/(q : ℝ) := abs_le.mpr hβ
  calc
    _ ≤ (broadArcWidth k P/(q : ℝ))*(k : ℝ)*P^(k-1) := by gcongr
    _ = (broadArcWidth k P*(k : ℝ)*P^(k-1))/(q : ℝ) := by ring
    _ = _ := by rw [broadArcWidth_derivative hk hP]; ring

theorem norm_pow_le_of_sub_le (s : ℕ) {z w : ℂ} {E : ℝ} (hE : 0≤E)
    (h : ‖z-w‖≤E) : ‖z‖^s≤(2 : ℝ)^(s-1)*(‖w‖^s+E^s) := by
  have ht : ‖z‖≤‖w‖+E := by
    have hh := norm_add_le (z-w) w
    rw [sub_add_cancel] at hh
    linarith
  exact (pow_le_pow_left₀ (norm_nonneg z) ht s).trans (add_pow_le (norm_nonneg w) hE s)

theorem continuous_ordinaryMajorModel (q : ℕ) [NeZero q] (k : ℕ)
    (P : ℝ) (a : ZMod q) : Continuous (ordinaryMajorModel q k P a) :=
  continuous_const.mul (continuous_monomialIntegral k P)

theorem ordinaryMajorModel_integrable (q : ℕ) [NeZero q] (k s : ℕ)
    (hk : 1≤k) (hks : k<s) {P : ℝ} (hP : 0≤P) (a : ZMod q) :
    Integrable (fun β=>‖ordinaryMajorModel q k P a β‖^s) := by
  simp_rw [ordinaryMajorModel_norm_pow]
  exact (integrable_monomial_moment k s hk hks hP).const_mul _

theorem ordinary_rational_arc_moment_le (k s : ℕ) (hk : 2≤k) (hks : k<s)
    {C : ℝ} (hC : 0<C)
    (happrox : ∀ (q : ℕ) [NeZero q] (a : ℕ) (P β : ℝ),
      Nat.Coprime a q → 0≤P → |β| *(k : ℝ)*P^(k-1)≤1/(2*(q : ℝ)) →
      ‖ordinaryWeyl k P ((a : ℝ)/q+β)-
        (completeMonomialSumMod q k (a : ZMod q)/(q : ℂ))*monomialIntegral k P β‖ ≤
        C*(q : ℝ)^(49/64 : ℝ))
    {P : ℝ} (hP : 1≤P) (q : ℕ) [NeZero q] (hqP : (q : ℝ)≤P) :
    rationalArcSum q (fun α=>‖ordinaryWeyl k P α‖^s) (broadArcWidth k P) ≤
      (2 : ℝ)^(s-1)*(ordinaryMajorModelMoment q k s P Set.univ+
        rationalArcSum q (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) := by
  have hPpos : 0<P := zero_lt_one.trans_le hP
  have hδ : 0≤broadArcWidth k P := (broadArcWidth_pos (by omega) hPpos).le
  have hend : -(broadArcWidth k P/(q : ℝ))≤broadArcWidth k P/(q : ℝ) := by
    have := div_nonneg hδ (Nat.cast_nonneg q)
    linarith
  let E : ℝ := C*P^(49/64 : ℝ)
  have hE : 0≤E := by dsimp [E]; positivity
  have hpoint (a : (ZMod q)ˣ) {β : ℝ}
      (hβ : β∈Set.Icc (-(broadArcWidth k P/(q : ℝ))) (broadArcWidth k P/(q : ℝ))) :
      ‖ordinaryWeyl k P (((a : ZMod q).val : ℝ)/q+β)‖^s ≤
        (2 : ℝ)^(s-1)*(‖ordinaryMajorModel q k P a β‖^s+E^s) := by
    apply norm_pow_le_of_sub_le s hE
    have hh := happrox q (a : ZMod q).val P β (ZMod.val_coe_unit_coprime a) hPpos.le
      (broad_band_derivative (by omega) hPpos q hβ)
    simp only [ZMod.natCast_zmod_val] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg q) hqP (by norm_num)) hC.le)
  have hint (a : (ZMod q)ˣ) :
      (∫ β in -(broadArcWidth k P/(q : ℝ))..broadArcWidth k P/(q : ℝ),
        ‖ordinaryWeyl k P (((a : ZMod q).val : ℝ)/q+β)‖^s) ≤
      (2 : ℝ)^(s-1)*((∫ β : ℝ, ‖ordinaryMajorModel q k P a β‖^s)+
        ∫ β in -(broadArcWidth k P/(q : ℝ))..broadArcWidth k P/(q : ℝ), E^s) := by
    have hf : Continuous (fun β=>‖ordinaryWeyl k P (((a : ZMod q).val : ℝ)/q+β)‖^s) :=
      (((continuous_ordinary k P).comp (continuous_const.add continuous_id)).norm.pow s)
    have hm := (continuous_ordinaryMajorModel q k P a).norm.pow s
    have hb := intervalIntegral.integral_mono_on (μ := volume) hend (hf.intervalIntegrable _ _)
      ((continuous_const.mul (hm.add continuous_const)).intervalIntegrable _ _) (fun β hβ=>hpoint a hβ)
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      (hm.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add_right
    rw [intervalIntegral.integral_of_le hend]
    exact setIntegral_le_integral (ordinaryMajorModel_integrable q k s (by omega) hks hPpos.le a)
      (Filter.Eventually.of_forall (fun β=>pow_nonneg (norm_nonneg _) s))
  unfold rationalArcSum ordinaryMajorModelMoment
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  simp only [setIntegral_univ]
  exact Finset.sum_le_sum (fun a _=>hint a)

theorem sum_primitiveCompleteMoment_le (S : Finset ℕ+) (k s : ℕ)
    (hsum : Summable (completeCoefficient k s)) :
    (∑ q∈S,primitiveCompleteMoment (q : ℕ) k s)≤∑' q : ℕ,completeCoefficient k s q := by
  have hh := hsum.sum_le_tsum (S.image (fun q : ℕ+ => (q : ℕ)))
    (fun q _=>completeCoefficient_nonneg k s q)
  rw [Finset.sum_image (g := fun q : ℕ+ => (q : ℕ)) (f := completeCoefficient k s)
    (fun (q : ℕ+) _ (r : ℕ+) _ h=>Subtype.ext h)] at hh
  simpa only [completeCoefficient_nezero] using hh

theorem broad_error_mass_identity (k s : ℕ) (hk : 1≤k) {P : ℝ} (hP : 0<P) (C : ℝ) :
    2*P*broadArcWidth k P*(C*P^(49/64 : ℝ))^s =
      (C^s/(k : ℝ))*P^((49/64 : ℝ)*s+2-k) := by
  have hkR : (k : ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have hp : P^((49/64 : ℝ)*s+2-k)*P^(k-1)=P^((49/64 : ℝ)*s)*P := by
    calc
      _ = P^(((49/64 : ℝ)*s+2-k)+(k-1 : ℕ)) := by
        rw [Real.rpow_add hP,Real.rpow_natCast]
      _ = P^((49/64 : ℝ)*s+1) := by
        congr 1
        rw [Nat.cast_sub hk]
        push_cast
        ring
      _ = _ := by rw [Real.rpow_add hP,Real.rpow_one]
  unfold broadArcWidth
  rw [mul_pow,← Real.rpow_mul_natCast hP.le]
  calc
    _ = (C^s/(k : ℝ))*((P^((49/64 : ℝ)*s)*P)/P^(k-1)) := by
      field_simp
    _ = _ := by rw [← hp,mul_div_cancel_right₀ _ (pow_ne_zero _ hP.ne')]

theorem broad_error_mass_le (k s : ℕ) (hk : 1≤k) (hs : 11≤s)
    {P C : ℝ} (hP : 1≤P) (hC : 0≤C) :
    2*P*broadArcWidth k P*(C*P^(49/64 : ℝ))^s ≤
      C^s*P^((s : ℝ)-k-1/2) := by
  have hPpos := zero_lt_one.trans_le hP
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hsR : (11 : ℝ)≤s := by exact_mod_cast hs
  rw [broad_error_mass_identity k s hk hPpos C]
  apply mul_le_mul
  · exact div_le_self (pow_nonneg hC _) hkR
  · exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  · positivity
  · positivity

/-- A full finite family of ordinary broad-arc moments, with a uniform
half-power saving for its approximation error. -/
theorem ordinary_broad_arc_sum_bound (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k<s) (hsum : Summable (completeCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ S : Finset ℕ+,
      (∀ q∈S,(q : ℝ)≤P) →
      (∑ q∈S,rationalArcSum (q : ℕ) (fun α=>‖ordinaryWeyl k P α‖^s) (broadArcWidth k P)) ≤
        (2 : ℝ)^(s-1)*(ordinaryMajorMomentConstant k s*P^(s-k)+C^s*P^((s : ℝ)-k-1/2)) := by
  obtain ⟨C,hC,happrox⟩ := ordinary_broad_major_approximation k hk (ε := (1/64 : ℝ)) (by norm_num)
  norm_num only [show (3/4 : ℝ)+1/64=49/64 by norm_num] at happrox
  refine ⟨C,hC,?_⟩
  intro P hP S hSP
  have hPpos := zero_lt_one.trans_le hP
  have hδ := (broadArcWidth_pos (by omega : 1≤k) hPpos).le
  have hmodels : (∑ q∈S,ordinaryMajorModelMoment (q : ℕ) k s P Set.univ) ≤
      ordinaryMajorMomentConstant k s*P^(s-k) := by
    simp_rw [ordinaryMajorModelMoment_factorization,setIntegral_univ]
    rw [← Finset.sum_mul]
    calc
      _ ≤ (∑' q : ℕ,completeCoefficient k s q)*(∫ β : ℝ,‖monomialIntegral k P β‖^s) :=
        mul_le_mul_of_nonneg_right (sum_primitiveCompleteMoment_le S k s hsum)
          (integral_nonneg (fun β=>pow_nonneg (norm_nonneg _) s))
      _ ≤ _ := by
        rw [← ordinaryMajorModel_total_factorization k s P hsum]
        exact ordinaryMajorModel_total_le k s (by omega) hks hPpos hsum
  have herr : (∑ q∈S,rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) ≤
      C^s*P^((s : ℝ)-k-1/2) := by
    exact (sum_constant_arc_integrals_le S hPpos.le hSP hδ (by positivity)).trans
      (broad_error_mass_le k s (by omega) hs hP hC.le)
  calc
    _ ≤ ∑ q∈S,(2 : ℝ)^(s-1)*(ordinaryMajorModelMoment (q : ℕ) k s P Set.univ+
        rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) :=
      Finset.sum_le_sum (fun q hq=>ordinary_rational_arc_moment_le k s hk hks hC happrox hP
        (q : ℕ) (hSP q hq))
    _ = (2 : ℝ)^(s-1)*((∑ q∈S,ordinaryMajorModelMoment (q : ℕ) k s P Set.univ)+
        ∑ q∈S,rationalArcSum (q : ℕ) (fun _=>(C*P^(49/64 : ℝ))^s) (broadArcWidth k P)) := by
      rw [← Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hmodels herr) (by positivity)

#print axioms ordinary_rational_arc_moment_le
#print axioms ordinary_broad_arc_sum_bound

end Waring.EndgameCompletion

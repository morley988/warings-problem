import Waring.PolicyCompletionRestrictedMean
import Waring.RationalHeightScale

/-! # Actual restricted smooth means at the source's fixed dilated length -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.PolicyCompletionRestrictedDilated
open SmoothMoments RationalHeight PolicyCompletionRestrictedMean

theorem even_excess_height_lintegral_dilated {k r : ℕ}
    (hk : 1≤k) (hr : 1≤r) {Δ q D ε : ℝ} (hq : 0<q) (hD : 1≤D)
    (hadm : AdmissibleExcess k (2*r) Δ) (hε : 0<ε) :
    ∃η : ℝ,0<η ∧ ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→
      ∀Z R : ℝ,1≤Z→1≤R→R≤P^η→
      (∫⁻ x in {x | height (P^((k:ℝ)*q)) x≤Z},
        ENNReal.ofReal (‖smoothWeyl k (D*P^q) R x‖^(2*r))
          ∂(volume.restrict (Set.Ioc 0 1)))≤
        ENNReal.ofReal (C*P^(((((2*r:ℕ):ℝ)-(k:ℝ))*q)+ε))*
          ENNReal.ofReal (Z^(2*Δ/(k:ℝ))) := by
  obtain ⟨η,hη,C,hC,hbound⟩ := even_excess_height_lintegral hk hr hadm (div_pos hε hq)
  let a : ℝ := ((2*r:ℕ):ℝ)-(k:ℝ)+ε/q
  let b : ℝ := 2*Δ/(k:ℝ)
  have hDp : 0<D := zero_lt_one.trans_le hD
  refine ⟨q*η,mul_pos hq hη,C*D^a*(D^k)^b,by positivity,?_⟩
  intro P hP Z R hZ hR hRP
  have hPp : 0<P := zero_lt_one.trans_le hP
  have hQ : 1≤D*P^q := one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow hP hq.le)
  have hscale : (D*P^q)^k=D^k*P^((k:ℝ)*q) := by
    rw [mul_pow,← Real.rpow_mul_natCast hPp.le,mul_comm q (k:ℝ)]
  have hDK : 1≤D^k := one_le_pow₀ hD
  have hRQ : R≤(D*P^q)^η := by
    calc
      _ ≤ P^(q*η) := hRP
      _ = (P^q)^η := Real.rpow_mul hPp.le q η
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le _)
        (le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) hD) hη.le
  have hZ' : 1≤D^k*Z := one_le_mul_of_one_le_of_one_le hDK hZ
  have hh := hbound (D*P^q) hQ (D^k*Z) R hZ' hR hRQ
  have hsub : {x | height (P^((k:ℝ)*q)) x≤Z} ⊆
      {x | height ((D*P^q)^k) x≤D^k*Z} := by
    intro x hx
    have hV : 0<P^((k:ℝ)*q) := Real.rpow_pos_of_pos hPp _
    have hVW : P^((k:ℝ)*q)≤D^k*P^((k:ℝ)*q) :=
      le_mul_of_one_le_left hV.le hDK
    rw [hscale]
    have he := height_conductor_scale_upper (α:=x) hV hVW
    rw [mul_div_cancel_right₀ _ hV.ne'] at he
    exact he.trans (mul_le_mul_of_nonneg_left hx (pow_nonneg hDp.le k))
  have hi := lintegral_mono' (Measure.restrict_mono_set (volume.restrict (Set.Ioc 0 1)) hsub)
    (le_refl (fun x => ENNReal.ofReal (‖smoothWeyl k (D*P^q) R x‖^(2*r))))
  apply hi.trans
  apply hh.trans_eq
  have hpow : (D*P^q)^a=D^a*P^(((((2*r:ℕ):ℝ)-(k:ℝ))*q)+ε) := by
    rw [Real.mul_rpow hDp.le (Real.rpow_nonneg hPp.le _),← Real.rpow_mul hPp.le]
    congr 1
    congr 1
    dsimp [a]
    field_simp
    <;> ring
  change ENNReal.ofReal (C*(D*P^q)^a)*ENNReal.ofReal ((D^k*Z)^b)=_
  rw [hpow,Real.mul_rpow (pow_nonneg hDp.le k) (zero_le_one.trans hZ)]
  repeat' rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

#print axioms even_excess_height_lintegral_dilated
end Waring.PolicyCompletionRestrictedDilated

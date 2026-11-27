import Waring.PolicyCompletionMomentLower

/-! # Necessary lower bounds for genuinely admissible smooth exponents

Almost-linear smooth cardinality on integer product scales, the diagonal
moment count, and finite Cauchy imply lambda >= r and lambda >= 2r-k.
Consequently the excess of every actual admissible even moment is
nonnegative. No numerical table premise is used.
-/

noncomputable section
namespace Waring.SmoothMoments
open PolicyCompletionMomentLower

/-- Product-scale lower estimates are incompatible with a smaller
uniform admissible exponent. -/
theorem admissibleExponent_ge_of_product_scale_lower {k p : ℕ} {lam v : ℝ}
    (hadm : AdmissibleExponent k p lam)
    (hlower : ∀ ε : ℝ,0 < ε → ∀ L : ℕ,∃ c : ℝ,0 < c ∧
      ∀ M : ℕ,1 ≤ M →
        c*((M : ℝ)^L)^(v-ε) ≤ smoothMoment k p ((M : ℝ)^L) M) :
    v ≤ lam := by
  by_contra hv
  have hgap : 0 < v-lam := sub_pos.mpr (lt_of_not_ge hv)
  let δ := (v-lam)/3
  have hδ : 0 < δ := div_pos hgap (by norm_num)
  obtain ⟨η,hη,C,hC,P₀,hP₀,hbound⟩ := hadm δ hδ
  obtain ⟨L,hL⟩ := exists_nat_gt (max (1 : ℝ) (1/η))
  have hL1real : (1 : ℝ) ≤ L := (le_max_left _ _).trans hL.le
  have hLη : 1 ≤ (L : ℝ)*η :=
    (div_le_iff₀ hη).mp ((le_max_right _ _).trans hL.le)
  obtain ⟨c,hc,hlow⟩ := hlower δ hδ L
  obtain ⟨M,hM⟩ := exists_nat_gt
    (max (1 : ℝ) (max P₀ ((2*C/c)^(1/δ))))
  have hMreal : (1 : ℝ) ≤ M := (le_max_left _ _).trans hM.le
  have hM1 : 1 ≤ M := by exact_mod_cast hMreal
  let P := (M : ℝ)^L
  have hMP : (M : ℝ) ≤ P := by
    calc
      _ = (M : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (M : ℝ)^(L : ℝ) := Real.rpow_le_rpow_of_exponent_le hMreal hL1real
      _ = _ := Real.rpow_natCast _ _
  have hP1 : 1 ≤ P := hMreal.trans hMP
  have hPp : 0 < P := zero_lt_one.trans_le hP1
  have hPP₀ : P₀ ≤ P :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hM.le)).trans hMP
  have hlarge : 2*C/c ≤ P^δ := NormalizedCoefficient.fixed_constant_rpow_bound
    (by positivity) hδ
    (((le_max_right _ _).trans ((le_max_right _ _).trans hM.le)).trans hMP)
  have hu := hbound P hPP₀ M hMreal (product_scale_smoothness hM1 hLη)
  have hb : c*P^(v-δ) ≤ C*P^(lam+δ) := (hlow M hM1).trans hu
  have hexp : v-δ=(lam+δ)+δ := by dsimp [δ]; ring
  have hsmall : c*P^δ ≤ C := by
    apply (mul_le_mul_right (Real.rpow_pos_of_pos hPp (lam+δ))).mp
    calc
      _ = c*P^(v-δ) := by rw [hexp,Real.rpow_add hPp (lam+δ) δ]; ring
      _ ≤ _ := hb
  have hlarge' : 2*C ≤ c*P^δ := by
    have h := (div_le_iff₀ hc).mp hlarge
    simpa only [mul_comm] using h
  linarith

/-- Raising the actual smooth-count lower bound preserves an arbitrarily
small loss, uniformly along every integer product scale. -/
theorem smooth_card_power_lower_product_scale (L p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ,0 < c ∧ ∀ M : ℕ,1 ≤ M →
      c*((M : ℝ)^L)^((p : ℝ)-ε) ≤
        ((smoothNumbers ((M : ℝ)^L) M).card : ℝ)^p := by
  let δ := ε/((p : ℝ)+1)
  have hp1 : 0 < (p : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hp1
  obtain ⟨c,hc,hcard⟩ := smooth_card_lower_product_scale L hδ
  refine ⟨c^p,pow_pos hc p,?_⟩
  intro M hM
  have hP1 : (1 : ℝ) ≤ (M : ℝ)^L := one_le_pow₀ (by exact_mod_cast hM)
  have hPp : 0 < (M : ℝ)^L := zero_lt_one.trans_le hP1
  have hrel : δ*((p : ℝ)+1)=ε := div_mul_cancel₀ ε hp1.ne'
  have hexp : (p : ℝ)-ε ≤ (1-δ)*(p : ℝ) := by nlinarith
  calc
    _ ≤ c^p*((M : ℝ)^L)^((1-δ)*(p : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 hexp)
        (pow_nonneg hc.le p)
    _ = (c*((M : ℝ)^L)^(1-δ))^p := by
      rw [Real.rpow_mul_natCast hPp.le,mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (hcard M hM) p

/-- Diagonal smooth tuples force the half-order lower bound. -/
theorem admissibleExponent_even_ge_halfOrder {k r : ℕ} {lam : ℝ}
    (hadm : AdmissibleExponent k (2*r) lam) : (r : ℝ) ≤ lam := by
  apply admissibleExponent_ge_of_product_scale_lower hadm
  intro ε hε L
  obtain ⟨c,hc,hcbd⟩ := smooth_card_power_lower_product_scale L r hε
  refine ⟨c,hc,?_⟩
  intro M hM
  exact (hcbd M hM).trans (smooth_card_pow_le_moment k r _ _)

/-- The range of a sum of r kth powers forces lambda >= 2r-k. -/
theorem admissibleExponent_even_ge_dimension {k r : ℕ} {lam : ℝ}
    (hadm : AdmissibleExponent k (2*r) lam) : (2*r : ℕ)-(k : ℝ) ≤ lam := by
  apply admissibleExponent_ge_of_product_scale_lower hadm
  intro ε hε L
  obtain ⟨c,hc,hcbd⟩ := smooth_card_power_lower_product_scale L (2*r) hε
  have hr1 : 0 < (r : ℝ)+1 := by positivity
  refine ⟨c/((r : ℝ)+1),div_pos hc hr1,?_⟩
  intro M hM
  let P := (M : ℝ)^L
  have hP1 : 1 ≤ P := one_le_pow₀ (by exact_mod_cast hM)
  have hPp : 0 < P := zero_lt_one.trans_le hP1
  apply (mul_le_mul_right (show 0 < ((r : ℝ)+1)*P^k by positivity)).mp
  calc
    _ = c*P^((2*r : ℕ)-ε) := by
      rw [show (P^k : ℝ)=P^(k : ℝ) from (Real.rpow_natCast P k).symm]
      have he : (((2*r : ℕ) : ℝ)-(k : ℝ)-ε)+(k : ℝ)=((2*r : ℕ) : ℝ)-ε := by ring
      rw [div_eq_mul_inv]
      calc
        _ = c*(((r : ℝ)+1)⁻¹*((r : ℝ)+1))*
          (P^(((2*r : ℕ) : ℝ)-(k : ℝ)-ε)*P^(k : ℝ)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hr1.ne',mul_one,← Real.rpow_add hPp,he]
    _ ≤ ((smoothNumbers P M).card : ℝ)^(2*r) := hcbd M hM
    _ ≤ ((r : ℝ)+1)*P^k*smoothMoment k (2*r) P M :=
      smooth_card_pow_le_range_moment k r M hP1
    _ = _ := by ring

/-- Genuine admissible excesses at even orders are nonnegative. -/
theorem admissibleExcess_even_nonneg {k r : ℕ} {Δ : ℝ}
    (hadm : AdmissibleExcess k (2*r) Δ) : 0 ≤ Δ := by
  have h := admissibleExponent_even_ge_dimension hadm
  change ((2*r : ℕ) : ℝ)-(k : ℝ) ≤ ((2*r : ℕ) : ℝ)-(k : ℝ)+Δ at h
  linarith

/-- At positive even order the genuine full exponent is at least one. -/
theorem admissibleExponent_even_ge_one {k r : ℕ} {lam : ℝ} (hr : 1 ≤ r)
    (hadm : AdmissibleExponent k (2*r) lam) : 1 ≤ lam := by
  exact (by exact_mod_cast hr : (1 : ℝ) ≤ r).trans (admissibleExponent_even_ge_halfOrder hadm)

#print axioms admissibleExponent_even_ge_halfOrder
#print axioms admissibleExponent_even_ge_dimension
#print axioms admissibleExcess_even_nonneg
end Waring.SmoothMoments

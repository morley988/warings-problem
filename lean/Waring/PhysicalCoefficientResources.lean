import Waring.CoefficientConductor

/-!
# Refined and cube coefficient resources at the original physical conductor

The actual integer sampling and padded Fourier ranges enter through explicit
fixed-factor scale inequalities. They imply both lower conductor comparison
and polynomial upper conductor growth. The conclusions use only the original
common height at P^(k(1-T)); no comparison or sampling premise remains.
-/

noncomputable section
namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments CubicCoefficientSampling ResourceScales RationalHeight

/-- Upper counterpart of the exact physical conductor identity. -/
theorem physical_conductor_upper {P k T phi CH CN CJ ρ : ℝ} {H N J : ℕ}
    (hP : 0 < P) (hCH : 0 ≤ CH) (hCN : 0 ≤ CN) (hCJ : 0 ≤ CJ)
    (hH : (H : ℝ) ≤ CH*P^(1-k*phi))
    (hN : (N : ℝ) ≤ CN*P^(2*k*phi+ρ))
    (hJ : (J : ℝ) ≤ CJ*P^(k-3-k*T+k*phi)) :
    (H : ℝ)^3*((N : ℝ)*J) ≤ (CH^3*CN*CJ)*P^(k*(1-T)+ρ) := by
  have hprod := mul_le_mul (pow_le_pow_left₀ (by positivity) hH 3)
    (mul_le_mul hN hJ (by positivity) (by positivity)) (by positivity) (by positivity)
  have hid : (P^(1-k*phi))^3*(P^(2*k*phi+ρ)*P^(k-3-k*T+k*phi))=P^(k*(1-T)+ρ) := by
    rw [← Real.rpow_mul_natCast hP.le, ← Real.rpow_add hP, ← Real.rpow_add hP]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (CH*P^(1-k*phi))^3*((CN*P^(2*k*phi+ρ))*(CJ*P^(k-3-k*T+k*phi))) := hprod
    _ = (CH^3*CN*CJ)*((P^(1-k*phi))^3*(P^(2*k*phi+ρ)*P^(k-3-k*T+k*phi))) := by ring
    _ = _ := by rw [hid]

/-- Refined resource at the original physical conductor, retaining only explicit floor/padding scale comparisons. -/
theorem normalized_refined_physical {k r c : ℕ}
    {T phi Δ ε CHlo CHup CJlo CJup : ℝ}
    (hc : 0 < c) (hCHlo : 1 ≤ CHlo) (hCHup : 1 ≤ CHup)
    (hCJlo : 1 ≤ CJlo) (hCJup : 1 ≤ CJup)
    (hk : 0 < k) (hr : 1 ≤ r) (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ H J : ℕ, 0 < H → 0 < J →
      P^(1-(k : ℝ)*phi) ≤ CHlo*(H : ℝ) → (H : ℝ) ≤ CHup*P^(1-(k : ℝ)*phi) →
      P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤ CJlo*(J : ℝ) →
      (J : ℝ) ≤ CJup*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) →
      ∀ (α ell : ℝ) (σ : ℕ → ℝ), P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-refinedSaving k T phi ell Δ) := by
  have hkR : 0 < 2*(k : ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let v : ℝ := (k : ℝ)*(1-T)
  have hv : 0 ≤ v := mul_nonneg (by positivity) (sub_nonneg.mpr hT)
  have hB : 0 ≤ v+1 := by linarith
  have hCV : 1 ≤ CHlo^3*CJlo := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCHlo) hCJlo
  obtain ⟨ηs,C,P₀,hηs,hC,hP₀,hbound⟩ := normalized_refined_common_conductor
    (B := v+1) (T := T) (phi := phi) (Δ := Δ) (ε := ε) (CH := CHup) (CJ := CJlo) (CV := CHlo^3*CJlo)
    hc hCHup hCJlo hCV hk hr hB hphi hε hadm hlam
  let η := min ηs (1/(4*(k : ℝ)))
  have hη : 0 < η := lt_min hηs (by positivity)
  have hηs' : η ≤ ηs := min_le_left _ _
  have hηcap : η ≤ 1/(4*(k : ℝ)) := min_le_right _ _
  have hηloss : 2*(k : ℝ)*η ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hηcap hkR.le
    have hid : 2*(k : ℝ)*(1/(4*(k : ℝ)))=(1/2 : ℝ) := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
    rwa [hid] at hh
  let CN : ℝ := ((r : ℝ)+1)*2^(2*k)
  have hCN : 0 < CN := by dsimp [CN]; positivity
  let C0 : ℝ := CHup^3*CN*CJup
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨η,C,max P₀ (C0^(1/(1/2 : ℝ))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hHlo hHup hJlo hJup α ell σ hL
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hRs : R ≤ P^ηs := hRup.trans (Real.rpow_le_rpow_of_exponent_le hP1 hηs')
  have hC0P : C0 ≤ P^(1/2 : ℝ) := fixed_constant_rpow_bound hC0 (by norm_num)
    ((le_max_right _ _).trans hP₀')
  obtain ⟨hNl,hNu⟩ := paddedSupport_power_scales (2*k) r hP1 hphi.le hr hR hRup
  have hNl' : P^(2*(k : ℝ)*phi) ≤ paddedSupport (2*k) r (P^phi*R) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hNl
  have hNu' : (paddedSupport (2*k) r (P^phi*R) : ℝ) ≤ CN*P^(2*(k : ℝ)*phi+2*(k : ℝ)*η) := by
    simpa only [CN,Nat.cast_mul,Nat.cast_ofNat] using hNu
  have hVup : (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) ≤ P^(v+1) := by
    have hh := physical_conductor_upper hPpos (zero_le_one.trans hCHup) hCN.le
      (zero_le_one.trans hCJup) hHup hNu' hJup
    calc
      _ ≤ C0*P^(v+2*(k : ℝ)*η) := hh
      _ ≤ P^(1/2 : ℝ)*P^(v+1/2) := mul_le_mul hC0P
        (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
        (Real.rpow_nonneg hPpos.le _) (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  have hVlo := physical_conductor_lower hPpos (zero_le_one.trans hCHlo)
    (zero_le_one.trans hCJlo) hHlo hNl' hJlo
  exact hbound P hPP₀ R hR hRs A hA H J hH hJ hVup hHup hJlo
    α ell (P^v) σ hVlo hL

/-- Cube resource under the same physical comparisons. -/
theorem normalized_cube_physical {k r c : ℕ}
    {T phi Δ ε CHlo CHup CJlo CJup : ℝ}
    (hc : 0 < c) (hCHlo : 1 ≤ CHlo) (hCHup : 1 ≤ CHup)
    (hCJlo : 1 ≤ CJlo) (hCJup : 1 ≤ CJup)
    (hk : 0 < k) (hr : 1 ≤ r) (hT : T ≤ 1) (hphi : 0 < phi) (hε : 0 < ε)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ H J : ℕ, 0 < H → 0 < J →
      P^(1-(k : ℝ)*phi) ≤ CHlo*(H : ℝ) → (H : ℝ) ≤ CHup*P^(1-(k : ℝ)*phi) →
      P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤ CJlo*(J : ℝ) →
      (J : ℝ) ≤ CJup*P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) →
      ∀ (α ell : ℝ) (σ : ℕ → ℝ), P^ell ≤ height (P^((k : ℝ)*(1-T))) α →
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-cubeSaving k T phi ell Δ) := by
  have hkR : 0 < 2*(k : ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let v : ℝ := (k : ℝ)*(1-T)
  have hv : 0 ≤ v := mul_nonneg (by positivity) (sub_nonneg.mpr hT)
  have hB : 0 ≤ v+1 := by linarith
  have hCV : 1 ≤ CHlo^3*CJlo := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCHlo) hCJlo
  obtain ⟨ηs,C,P₀,hηs,hC,hP₀,hbound⟩ := normalized_cube_common_conductor
    (B := v+1) (T := T) (phi := phi) (Δ := Δ) (ε := ε) (CH := CHup) (CJ := CJlo) (CV := CHlo^3*CJlo)
    hc hCHup hCJlo hCV hk hr hB hphi hε hadm hlam
  let η := min ηs (1/(4*(k : ℝ)))
  have hη : 0 < η := lt_min hηs (by positivity)
  have hηs' : η ≤ ηs := min_le_left _ _
  have hηcap : η ≤ 1/(4*(k : ℝ)) := min_le_right _ _
  have hηloss : 2*(k : ℝ)*η ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hηcap hkR.le
    have hid : 2*(k : ℝ)*(1/(4*(k : ℝ)))=(1/2 : ℝ) := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      norm_num
    rwa [hid] at hh
  let CN : ℝ := ((r : ℝ)+1)*2^(2*k)
  have hCN : 0 < CN := by dsimp [CN]; positivity
  let C0 : ℝ := CHup^3*CN*CJup
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  refine ⟨η,C,max P₀ (C0^(1/(1/2 : ℝ))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hHlo hHup hJlo hJup α ell σ hL
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hRs : R ≤ P^ηs := hRup.trans (Real.rpow_le_rpow_of_exponent_le hP1 hηs')
  have hC0P : C0 ≤ P^(1/2 : ℝ) := fixed_constant_rpow_bound hC0 (by norm_num)
    ((le_max_right _ _).trans hP₀')
  obtain ⟨hNl,hNu⟩ := paddedSupport_power_scales (2*k) r hP1 hphi.le hr hR hRup
  have hNl' : P^(2*(k : ℝ)*phi) ≤ paddedSupport (2*k) r (P^phi*R) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hNl
  have hNu' : (paddedSupport (2*k) r (P^phi*R) : ℝ) ≤ CN*P^(2*(k : ℝ)*phi+2*(k : ℝ)*η) := by
    simpa only [CN,Nat.cast_mul,Nat.cast_ofNat] using hNu
  have hVup : (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) ≤ P^(v+1) := by
    have hh := physical_conductor_upper hPpos (zero_le_one.trans hCHup) hCN.le
      (zero_le_one.trans hCJup) hHup hNu' hJup
    calc
      _ ≤ C0*P^(v+2*(k : ℝ)*η) := hh
      _ ≤ P^(1/2 : ℝ)*P^(v+1/2) := mul_le_mul hC0P
        (Real.rpow_le_rpow_of_exponent_le hP1 (by linarith))
        (Real.rpow_nonneg hPpos.le _) (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  have hVlo := physical_conductor_lower hPpos (zero_le_one.trans hCHlo)
    (zero_le_one.trans hCJlo) hHlo hNl' hJlo
  exact hbound P hPP₀ R hR hRs A hA H J hH hJ hVup hHup hJlo
    α ell (P^v) σ hVlo hL

#print axioms physical_conductor_upper
#print axioms normalized_refined_physical
#print axioms normalized_cube_physical
end Waring.NormalizedCoefficient

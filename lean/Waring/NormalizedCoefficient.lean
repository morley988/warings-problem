import Waring.CoefficientPower
import Waring.ResourceScales

/-!
# Actual normalized refined coefficient resources

The full finite block sums are linked to the four affine caps. The explicit
scale and smooth-moment hypotheses state exactly the remaining source inputs;
this file does not assert any published seed admissibility or policy soundness.
-/

noncomputable section
open scoped BigOperators

namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments CubicCoefficientSampling ResourceScales RationalHeight

/-- The actual even coefficient moment, normalized by the number of sampled
parameters and by the trivial M^(2r) scale, where M=P^phi. -/
def normalizedSampledCoefficient (A : Finset ℕ) (degree r : ℕ)
    (P phi : ℝ) (H J : ℕ) (α : ℝ) (σ : ℕ → ℝ) : ℝ :=
  (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
    ‖coefficientWeyl A degree (α*(h:ℝ)^3*((j:ℝ)+σ h))‖^(2*r)) /
      ((H:ℝ)*J*P^((2*r:ℕ)*phi))

def refinedSaving (k T phi ell Δ : ℝ) : ℝ :=
  fourCap (1-k*phi) (2*k*phi) (k-3-k*T+k*phi) ell - Δ*phi

theorem sampling_power_identity {P : ℝ} (hP : 0 < P)
    (ε k p phi Δ ρN ρE cap : ℝ) :
    P^ε * P^(2*k*phi+ρN) * P^((p-2*k+Δ)*phi+ρE) * P^(-cap) =
      P^(ε+ρN+ρE-(cap-Δ*phi)) * P^(p*phi) := by
  rw [← Real.rpow_add hP, ← Real.rpow_add hP, ← Real.rpow_add hP, ← Real.rpow_add hP]
  congr 1
  ring

/-- Uniform refined-resource theorem for actual block sums. The parameters
rhoN and rhoE explicitly retain support and smooth-moment exponent losses. -/
theorem normalized_refined_coefficient {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (A : Finset ℕ) (k r : ℕ) (X R T phi ell Δ CN CE ρN ρE : ℝ),
      A ⊆ smoothNumbers X R → 0 ≤ CN → 0 ≤ CE →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ P^(1-(k:ℝ)*phi) →
      P^(2*(k:ℝ)*phi) ≤ paddedSupport (2*k) r X →
      (paddedSupport (2*k) r X : ℝ) ≤ CN*P^(2*(k:ℝ)*phi+ρN) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ≤ J →
      smoothMoment (2*k) (2*r) X R ≤ CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE) →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
      P^ell ≤ height ((H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J)) α →
      normalizedSampledCoefficient A (2*k) r P phi H J α σ ≤
        C*CN*CE*P^(ε+ρN+ρE-refinedSaving k T phi ell Δ) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_sampling_padded_epsilon hB hε
  refine ⟨4*C, by positivity, ?_⟩
  intro P hP A k r X R T phi ell Δ CN CE ρN ρE hA hCN hCE H J hH hJ hV
    hHs hNl hNu hJs hmoment α σ hLs
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hden : 0 < (H:ℝ)*J*P^((2*r:ℕ)*phi) := by positivity
  unfold normalizedSampledCoefficient
  apply (div_le_iff₀ hden).mpr
  have hshape := samplingShape_le_four_rpow hP (paddedSupport_pos (2*k) r X) hJ
    hHs hNl hJs hLs
  have hmoment0 := smoothMoment_nonneg (2*k) (2*r) X R
  have hshape0 := samplingShape_nonneg H (paddedSupport (2*k) r X) J α
  let cap := fourCap (1-(k:ℝ)*phi) (2*(k:ℝ)*phi)
    ((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ell
  calc
    _ ≤ C*P^ε*(H:ℝ)*((paddedSupport (2*k) r X : ℝ)*J)*
          smoothMoment (2*k) (2*r) X R * samplingShape H (paddedSupport (2*k) r X) J α :=
      hbound P hP A (2*k) r X R hA H J hH hJ hV α σ
    _ ≤ C*P^ε*(H:ℝ)*((CN*P^(2*(k:ℝ)*phi+ρN))*J)*
          (CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE))*(4*P^(-cap)) := by
      gcongr
    _ = (4*C*CN*CE*(H:ℝ)*J) *
        (P^ε*P^(2*(k:ℝ)*phi+ρN)*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE)*P^(-cap)) := by ring
    _ = _ := by
      rw [sampling_power_identity hPp ε (k:ℝ) (2*r:ℕ) phi Δ ρN ρE cap]
      dsimp [refinedSaving, cap]
      ring

/-- Ceil-padding supplies the correct lower support scale and a fixed upper
constant, while all smoothness-cutoff growth is exposed as degree*eta. -/
theorem paddedSupport_power_scales (degree r : ℕ) {P phi η R : ℝ}
    (hP : 1 ≤ P) (hphi : 0 ≤ phi) (hr : 1 ≤ r)
    (hR : 1 ≤ R) (hRup : R ≤ P^η) :
    P^((degree:ℝ)*phi) ≤ paddedSupport degree r (P^phi*R) ∧
      (paddedSupport degree r (P^phi*R) : ℝ) ≤
        (((r:ℝ)+1)*2^degree)*P^((degree:ℝ)*phi+(degree:ℝ)*η) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hM : 1 ≤ P^phi := Real.one_le_rpow hP hphi
  have hX : 1 ≤ P^phi*R := one_le_mul_of_one_le_of_one_le hM hR
  have hMr : P^phi ≤ P^phi*R := by nlinarith [Real.rpow_nonneg hP0 phi]
  have hXup : P^phi*R ≤ P^(phi+η) := by
    rw [Real.rpow_add hPp]
    exact mul_le_mul_of_nonneg_left hRup (Real.rpow_nonneg hP0 phi)
  obtain ⟨hlo,hhi⟩ := paddedSupport_bounds degree r hX hr
  constructor
  · calc
      P^((degree:ℝ)*phi) = (P^phi)^degree := by
        rw [← Real.rpow_mul_natCast hP0]
        congr 1
        ring
      _ ≤ (P^phi*R)^degree := pow_le_pow_left₀ (Real.rpow_nonneg hP0 phi) hMr degree
      _ ≤ _ := hlo
  · calc
      _ ≤ ((r:ℝ)+1)*(2*(P^phi*R))^degree := hhi
      _ = (((r:ℝ)+1)*2^degree)*(P^phi*R)^degree := by rw [mul_pow]; ring
      _ ≤ (((r:ℝ)+1)*2^degree)*(P^(phi+η))^degree := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_mul_natCast hP0]
        congr 2
        ring

/-- An actual admissible exponent controls smooth moments at the block
length P^phi*R. The smoothness exponent is chosen uniformly below any
prescribed positive cap, and the R contribution is absorbed explicitly. -/
theorem scaled_smoothMoment_of_admissible {degree p : ℕ} {lam phi ε ηmax : ℝ}
    (hadm : AdmissibleExponent degree p lam) (hlam : 0 ≤ lam)
    (hphi : 0 < phi) (hε : 0 < ε) (hηmax : 0 < ηmax) :
    ∃ η C P₀ : ℝ, 0 < η ∧ η ≤ ηmax ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
        smoothMoment degree p (P^phi*R) R ≤ C*P^(lam*phi+ε) := by
  let δ := ε/(2*phi)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδid : phi*δ = ε/2 := by dsimp [δ]; field_simp
  have hq : 0 < lam+δ := by linarith
  obtain ⟨ηs,hηs,C,hC,X₀,hX₀,hsource⟩ := hadm δ hδ
  let η := min ηmax (min (phi*ηs) (ε/(2*(lam+δ))))
  have hη : 0 < η := lt_min hηmax (lt_min (mul_pos hphi hηs) (div_pos hε (by positivity)))
  have hηmax' : η ≤ ηmax := min_le_left _ _
  have hηs' : η ≤ phi*ηs := (min_le_right _ _).trans (min_le_left _ _)
  have hηloss : η*(lam+δ) ≤ ε/2 := by
    have hh : η ≤ ε/(2*(lam+δ)) := (min_le_right _ _).trans (min_le_right _ _)
    have hm := mul_le_mul_of_nonneg_right hh hq.le
    have hid : ε/(2*(lam+δ))*(lam+δ) = ε/2 := by field_simp
    rwa [hid] at hm
  refine ⟨η,C,max 2 (X₀^(1/phi)),hη,hηmax',hC,le_max_left _ _,?_⟩
  intro P hP₀ R hR hRup
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP₀
  have hP : 1 ≤ P := by linarith
  have hPp : 0 < P := by linarith
  have hM : 1 ≤ P^phi := Real.one_le_rpow hP hphi.le
  have hMr : P^phi ≤ P^phi*R := le_mul_of_one_le_right (Real.rpow_nonneg hPp.le phi) hR
  have hX₀p : 0 < X₀ := zero_lt_one.trans_le hX₀
  have hlength : X₀ ≤ P^phi*R := by
    apply le_trans _ hMr
    calc
      X₀ = (X₀^(1/phi))^phi := by
        rw [← Real.rpow_mul hX₀p.le, one_div_mul_cancel hphi.ne', Real.rpow_one]
      _ ≤ P^phi := Real.rpow_le_rpow (Real.rpow_nonneg hX₀p.le _)
        ((le_max_right _ _).trans hP₀) hphi.le
  have hsmooth : R ≤ (P^phi*R)^ηs := by
    calc
      R ≤ P^η := hRup
      _ ≤ P^(phi*ηs) := Real.rpow_le_rpow_of_exponent_le hP hηs'
      _ = (P^phi)^ηs := Real.rpow_mul hPp.le phi ηs
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hPp.le phi) hMr hηs.le
  have hXup : P^phi*R ≤ P^(phi+η) := by
    rw [Real.rpow_add hPp]
    exact mul_le_mul_of_nonneg_left hRup (Real.rpow_nonneg hPp.le phi)
  have hexponent : (phi+η)*(lam+δ) ≤ lam*phi+ε := by nlinarith only [hδid,hηloss]
  calc
    _ ≤ C*(P^phi*R)^(lam+δ) := hsource _ hlength R hR hsmooth
    _ ≤ C*(P^(phi+η))^(lam+δ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hXup hq.le) hC.le
    _ = C*P^((phi+η)*(lam+δ)) := by rw [← Real.rpow_mul hPp.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hexponent) hC.le

/-- The normalized refined resource with every support and smoothness loss
absorbed. The only analytic source premise is the actual degree-2k smooth
admissible excess. Conductor and height comparisons remain explicit for later
insertion into the complete efficient-differencing policy. -/
theorem normalized_refined_of_admissible {k r : ℕ} {B T phi Δ ε : ℝ}
    (hk : 0 < k) (hr : 1 ≤ r) (hB : 0 ≤ B) (hphi : 0 < phi) (hε : 0 < ε)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ P^(1-(k:ℝ)*phi) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ≤ J →
      ∀ (α ell : ℝ) (σ : ℕ → ℝ),
      P^ell ≤ height ((H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J)) α →
      normalizedSampledCoefficient A (2*k) r P phi H J α σ ≤
        C*P^(ε-refinedSaving k T phi ell Δ) := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hkR : 0 < (2*(k:ℝ)) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let ηmax := δ/(2*(k:ℝ))
  have hηmax : 0 < ηmax := div_pos hδ hkR
  obtain ⟨η,CE,P₀,hη,hηcap,hCE,hP₀,hmoment⟩ :=
    scaled_smoothMoment_of_admissible hadm hlam hphi hδ hηmax
  obtain ⟨C,hC,hbound⟩ := normalized_refined_coefficient hB hδ
  let CN : ℝ := ((r:ℝ)+1)*2^(2*k)
  have hCN : 0 < CN := by dsimp [CN]; positivity
  have hηloss : (2*(k:ℝ))*η ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left hηcap hkR.le
    have hid : (2*(k:ℝ))*ηmax = δ := by dsimp [ηmax]; field_simp
    rwa [hid] at hh
  refine ⟨η,C*CN*CE,P₀,hη,by positivity,hP₀,?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hV hHs hJs α ell σ hLs
  have hP2 : 2 ≤ P := hP₀.trans hP₀'
  have hP : 1 ≤ P := by linarith
  have hPp : 0 < P := by linarith
  obtain ⟨hNl,hNu⟩ := paddedSupport_power_scales (2*k) r hP hphi.le hr hR hRup
  have hNl' : P^(2*(k:ℝ)*phi) ≤ paddedSupport (2*k) r (P^phi*R) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hNl
  have hNu' : (paddedSupport (2*k) r (P^phi*R) : ℝ) ≤ CN*P^(2*(k:ℝ)*phi+2*(k:ℝ)*η) := by
    simpa only [CN,Nat.cast_mul,Nat.cast_ofNat] using hNu
  have hm : smoothMoment (2*k) (2*r) (P^phi*R) R ≤
      CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+δ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmoment P hP₀' R hR hRup
  have hb := hbound P hP A k r (P^phi*R) R T phi ell Δ CN CE (2*(k:ℝ)*η) δ
    hA hCN.le hCE.le H J hH hJ hV hHs hNl' hNu' hJs hm α σ hLs
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C*CN*CE)
  apply Real.rpow_le_rpow_of_exponent_le hP
  dsimp [δ] at hηloss ⊢
  linarith

#print axioms normalized_refined_coefficient
#print axioms paddedSupport_power_scales
#print axioms scaled_smoothMoment_of_admissible
#print axioms normalized_refined_of_admissible

end Waring.NormalizedCoefficient

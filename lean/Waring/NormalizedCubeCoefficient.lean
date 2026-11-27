import Waring.NormalizedCoefficient
import Waring.CubicRootSamplingAsymptotic

/-!
# Actual normalized cube-root coefficient resources

The proved cube-root sampling estimate is linked to the four affine resource
caps. Genuine smooth admissibility remains an explicit source hypothesis;
all support, divisor, logarithmic, and smoothness losses are discharged.
-/

noncomputable section
open scoped BigOperators

namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments CubicCoefficientSampling ResourceScales RationalHeight

def cubeFourCap (h n j ell : ℝ) : ℝ :=
  min n (min j (min ((n+j-3*h)/2) (ell/3)))

def cubeSaving (k T phi ell Δ : ℝ) : ℝ :=
  cubeFourCap (1-k*phi) (2*k*phi) (k-3-k*T+k*phi) ell - Δ*phi

/-- The exact four caps in the cube-root sampling estimate, with each actual
integer scale allowed to satisfy an inequality rather than an exact power law. -/
theorem cubeSamplingShape_le_four_rpow {P h n j ell α : ℝ} {H N J : ℕ}
    (hP : 1 ≤ P) (hN : 0 < N) (hJ : 0 < J)
    (hHscale : (H:ℝ) ≤ P^h) (hNscale : P^n ≤ N) (hJscale : P^j ≤ J)
    (hLscale : P^ell ≤ height ((H:ℝ)^3*((N:ℝ)*J)) α) :
    cubeSamplingShape H N J α ≤ 4*P^(-cubeFourCap h n j ell) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  let L := height ((H:ℝ)^3*((N:ℝ)*J)) α
  have hL : 0 < L := height_pos _ _
  have h1 : 1/(N:ℝ) ≤ P^(-n) := by
    rw [Real.rpow_neg hP0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hNscale
  have h2 : 1/(J:ℝ) ≤ P^(-j) := by
    rw [Real.rpow_neg hP0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hJscale
  have hnum : Real.sqrt ((H:ℝ)^3) ≤ P^(3*h/2) := by
    calc
      _ ≤ Real.sqrt ((P^h)^3) := Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hHscale 3)
      _ = Real.sqrt (P^(h*3)) := by congr 1; simpa using (Real.rpow_mul_natCast hP0 h 3).symm
      _ = _ := by rw [sqrt_rpow hP0]; congr 1; ring
  have hden : P^((n+j)/2) ≤ Real.sqrt ((N:ℝ)*J) := by
    rw [← sqrt_rpow hP0, Real.rpow_add hPpos]
    apply Real.sqrt_le_sqrt
    exact mul_le_mul hNscale hJscale (Real.rpow_nonneg hP0 _) hNr.le
  have h3 : Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J) ≤ P^(-((n+j-3*h)/2)) := by
    calc
      _ ≤ P^(3*h/2)/P^((n+j)/2) :=
        div_le_div₀ (Real.rpow_nonneg hP0 _) hnum (Real.rpow_pos_of_pos hPpos _) hden
      _ = P^(3*h/2-(n+j)/2) := (Real.rpow_sub hPpos _ _).symm
      _ = _ := by congr 1; ring
  have hroot : P^(ell/3) ≤ L^(1/3:ℝ) := by
    calc
      _ = (P^ell)^(1/3:ℝ) := by
        rw [← Real.rpow_mul hP0]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hP0 _) hLscale (by norm_num)
  have h4 : 1/L^(1/3:ℝ) ≤ P^(-(ell/3)) := by
    rw [Real.rpow_neg hP0]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hroot
  have hn : cubeFourCap h n j ell ≤ n := min_le_left _ _
  have hj : cubeFourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hc : cubeFourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : cubeFourCap h n j ell ≤ ell/3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have b1 := h1.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hn))
  have b2 := h2.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hj))
  have b3 := h3.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hc))
  have b4 := h4.trans (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hl))
  unfold cubeSamplingShape
  change 1/(N:ℝ)+1/(J:ℝ)+Real.sqrt ((H:ℝ)^3)/Real.sqrt ((N:ℝ)*J)+1/L^(1/3:ℝ) ≤ _
  linarith

/-- Exact affine caps used by the cube alternative in the certificate. -/
theorem cubeFourCap_coefficient_identity (k T f ell : ℝ) :
    cubeFourCap (1-k*f) (2*k*f) (k-3-k*T+k*f) ell =
      min (2*k*f) (min (k-3-k*T+k*f)
        (min ((k-6-k*T+6*k*f)/2) (ell/3))) := by
  unfold cubeFourCap
  congr 3 <;> ring

/-- Same actual coefficient estimate with padded support, directly suited to
lower scale bounds in the four-cap resource theorem. -/
theorem coefficient_cube_sampling_padded_epsilon {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (A : Finset ℕ) (k r : ℕ) (X R : ℝ),
      A ⊆ smoothNumbers X R → ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport k r X : ℝ)*J) ≤ P^B →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
        (∑ h ∈ Finset.Icc 1 H, ∑ j ∈ Finset.range J,
          ‖coefficientWeyl A k (α*(h:ℝ)^3*((j:ℝ)+σ h))‖ ^ (2*r)) ≤
          C*P^ε*(H:ℝ)*((paddedSupport k r X : ℝ)*J)*
            smoothMoment k (2*r) X R * cubeSamplingShape H (paddedSupport k r X) J α := by
  obtain ⟨C,hC,hbound⟩ := cubic_root_sampling_epsilon hB hε
  refine ⟨C,hC,?_⟩
  intro P hP A k r X R hA H J hH hJ hV α σ
  have hAm : ∀ m ∈ A, m ≤ ⌈X⌉₊ :=
    fun m hm => (mem_smoothNumbers.mp (hA hm)).1.2.trans (Nat.floor_le_ceil X)
  rw [sampled_power_eq_cubicSecondMoment A k r ⌈X⌉₊ H J hAm α σ]
  apply (hbound P hP H (paddedSupport k r X) J hH (paddedSupport_pos k r X) hJ hV α
    (powerCoefficient A k r) σ).trans
  have hshape := cubeSamplingShape_nonneg H (paddedSupport k r X) J α
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  apply mul_le_mul_of_nonneg_right _ hshape
  apply mul_le_mul_of_nonneg_left (powerCoefficient_padded_energy_le_smoothMoment A k r X R hA)
  positivity

/-- Uniform cube-resource theorem for actual block sums. The parameters
rhoN and rhoE explicitly retain support and smooth-moment exponent losses. -/
theorem normalized_cube_coefficient {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
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
        C*CN*CE*P^(ε+ρN+ρE-cubeSaving k T phi ell Δ) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_cube_sampling_padded_epsilon hB hε
  refine ⟨4*C, by positivity, ?_⟩
  intro P hP A k r X R T phi ell Δ CN CE ρN ρE hA hCN hCE H J hH hJ hV
    hHs hNl hNu hJs hmoment α σ hLs
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hden : 0 < (H:ℝ)*J*P^((2*r:ℕ)*phi) := by positivity
  unfold normalizedSampledCoefficient
  apply (div_le_iff₀ hden).mpr
  have hshape := cubeSamplingShape_le_four_rpow hP (paddedSupport_pos (2*k) r X) hJ
    hHs hNl hJs hLs
  have hmoment0 := smoothMoment_nonneg (2*k) (2*r) X R
  have hshape0 := cubeSamplingShape_nonneg H (paddedSupport (2*k) r X) J α
  let cap := cubeFourCap (1-(k:ℝ)*phi) (2*(k:ℝ)*phi)
    ((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ell
  calc
    _ ≤ C*P^ε*(H:ℝ)*((paddedSupport (2*k) r X : ℝ)*J)*
          smoothMoment (2*k) (2*r) X R * cubeSamplingShape H (paddedSupport (2*k) r X) J α :=
      hbound P hP A (2*k) r X R hA H J hH hJ hV α σ
    _ ≤ C*P^ε*(H:ℝ)*((CN*P^(2*(k:ℝ)*phi+ρN))*J)*
          (CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE))*(4*P^(-cap)) := by
      gcongr
    _ = (4*C*CN*CE*(H:ℝ)*J) *
        (P^ε*P^(2*(k:ℝ)*phi+ρN)*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE)*P^(-cap)) := by ring
    _ = _ := by
      rw [sampling_power_identity hPp ε (k:ℝ) (2*r:ℕ) phi Δ ρN ρE cap]
      dsimp [cubeSaving, cap]
      ring

/-- The normalized cube resource with every support and smoothness loss
absorbed. The only analytic source premise is the actual degree-2k smooth
admissible excess. Conductor and height comparisons remain explicit for later
insertion into the complete efficient-differencing policy. -/
theorem normalized_cube_of_admissible {k r : ℕ} {B T phi Δ ε : ℝ}
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
        C*P^(ε-cubeSaving k T phi ell Δ) := by
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hkR : 0 < (2*(k:ℝ)) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let ηmax := δ/(2*(k:ℝ))
  have hηmax : 0 < ηmax := div_pos hδ hkR
  obtain ⟨η,CE,P₀,hη,hηcap,hCE,hP₀,hmoment⟩ :=
    scaled_smoothMoment_of_admissible hadm hlam hphi hδ hηmax
  obtain ⟨C,hC,hbound⟩ := normalized_cube_coefficient hB hδ
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

#print axioms cubeSamplingShape_le_four_rpow
#print axioms coefficient_cube_sampling_padded_epsilon
#print axioms normalized_cube_coefficient
#print axioms normalized_cube_of_admissible

end Waring.NormalizedCoefficient

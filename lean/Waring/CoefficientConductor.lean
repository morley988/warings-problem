import Waring.FixedCoefficientPhase
import Waring.RationalHeightScale

/-!
# Common-conductor coefficient resources with physical scale constants

The actual sampled conductor H^3*N*J can differ from the common auxiliary
conductor. Fixed floor, padding, and phase constants are accounted for
explicitly and absorbed using the requested epsilon, with uniform smoothness.
-/

noncomputable section
open scoped BigOperators
namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments CubicCoefficientSampling ResourceScales RationalHeight

/-- A one-sided comparison of positive conductors gives the same one-sided
height comparison. No assumption that the larger conductor is W is needed. -/
theorem height_conductor_compare {V W C α : ℝ} (hV : 0 < V) (hC : 1 ≤ C)
    (hWV : W ≤ C*V) : height W α ≤ C*height V α := by
  obtain ⟨r,hr⟩ := exists_minimizer hV α
  apply (height_le_cost W α r).trans
  rw [← hr]
  unfold cost
  apply max_le
  · have hden : (r.den : ℝ) ≤ C*(r.den : ℝ) :=
      le_mul_of_one_le_left (by positivity) hC
    exact hden.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (zero_le_one.trans hC))
  · have he := mul_le_mul_of_nonneg_right hWV (abs_nonneg ((r.den : ℝ)*α-(r.num : ℝ)))
    have hh := mul_le_mul_of_nonneg_left (le_max_right (r.den : ℝ) (V*|(r.den : ℝ)*α-(r.num : ℝ)|))
      (zero_le_one.trans hC)
    nlinarith only [he,hh]

/-- Physical scale lower bounds imply the required conductor comparison,
with the exact cube of the h-floor constant. -/
theorem physical_conductor_lower {P k T phi CH CJ : ℝ} {H N J : ℕ}
    (hP : 0 < P) (hCH : 0 ≤ CH) (hCJ : 0 ≤ CJ)
    (hH : P^(1-k*phi) ≤ CH*(H : ℝ)) (hN : P^(2*k*phi) ≤ N)
    (hJ : P^(k-3-k*T+k*phi) ≤ CJ*(J : ℝ)) :
    P^(k*(1-T)) ≤ (CH^3*CJ)*((H : ℝ)^3*((N : ℝ)*J)) := by
  have hprod := mul_le_mul
    (pow_le_pow_left₀ (Real.rpow_nonneg hP.le _) hH 3)
    (mul_le_mul hN hJ (Real.rpow_nonneg hP.le _) (by positivity))
    (by positivity : 0 ≤ P^(2*k*phi)*P^(k-3-k*T+k*phi)) (by positivity)
  have hid : (P^(1-k*phi))^3*(P^(2*k*phi)*P^(k-3-k*T+k*phi))=P^(k*(1-T)) := by
    rw [← Real.rpow_mul_natCast hP.le, ← Real.rpow_add hP, ← Real.rpow_add hP]
    congr 1
    push_cast
    ring
  rw [hid] at hprod
  convert hprod using 1 <;> ring

/-- A factor-C conductor comparison and a fixed phase multiplier together
cost at most delta in the original height exponent. -/
theorem common_height_phase_shift {P V W C ell δ α : ℝ}
    (hP : 0 < P) (hV : 0 < V) (hC : 1 ≤ C) (hWV : W ≤ C*V)
    (c : ℕ) (hc : 0 < c) (hcP : C*(c : ℝ) ≤ P^δ)
    (hL : P^ell ≤ height W α) : P^(ell-δ) ≤ height V ((c : ℝ)*α) := by
  have hcompare := height_conductor_compare (α := α) hV hC hWV
  have hphase := height_mul_phase_lower (α := α) hV hc
  have hh : P^ell ≤ P^δ*height V ((c : ℝ)*α) := by
    calc
      _ ≤ height W α := hL
      _ ≤ C*height V α := hcompare
      _ ≤ C*((c : ℝ)*height V ((c : ℝ)*α)) :=
        mul_le_mul_of_nonneg_left hphase (zero_le_one.trans hC)
      _ = (C*(c : ℝ))*height V ((c : ℝ)*α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcP (height_pos _ _).le
  rw [Real.rpow_sub hP]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hP _)).mpr (by simpa only [mul_comm] using hh)

def perturbedRefinedSaving (k T phi ell Δ δ : ℝ) : ℝ :=
  fourCap (1-k*phi+δ) (2*k*phi) (k-3-k*T+k*phi-δ) (ell-δ)-Δ*phi

def perturbedCubeSaving (k T phi ell Δ δ : ℝ) : ℝ :=
  cubeFourCap (1-k*phi+δ) (2*k*phi) (k-3-k*T+k*phi-δ) (ell-δ)-Δ*phi

theorem perturbedRefinedSaving_lower (k T phi ell Δ δ : ℝ) (hδ : 0 ≤ δ) :
    refinedSaving k T phi ell Δ-3*δ ≤ perturbedRefinedSaving k T phi ell Δ δ := by
  let h := 1-k*phi
  let n := 2*k*phi
  let j := k-3-k*T+k*phi
  have hn : fourCap h n j ell ≤ n := min_le_left _ _
  have hj : fourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hm : fourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : fourCap h n j ell ≤ ell-2*h :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb : fourCap h n j ell-3*δ ≤ fourCap (h+δ) n (j-δ) (ell-δ) := by
    change fourCap h n j ell-3*δ ≤ min n (min (j-δ) (min ((n+(j-δ)-3*(h+δ))/2) ((ell-δ)-2*(h+δ))))
    exact le_min (by linarith) (le_min (by linarith) (le_min (by linarith) (by linarith)))
  change fourCap h n j ell-Δ*phi-3*δ ≤ fourCap (h+δ) n (j-δ) (ell-δ)-Δ*phi
  linarith

theorem perturbedCubeSaving_lower (k T phi ell Δ δ : ℝ) (hδ : 0 ≤ δ) :
    cubeSaving k T phi ell Δ-3*δ ≤ perturbedCubeSaving k T phi ell Δ δ := by
  let h := 1-k*phi
  let n := 2*k*phi
  let j := k-3-k*T+k*phi
  have hn : cubeFourCap h n j ell ≤ n := min_le_left _ _
  have hj : cubeFourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hm : cubeFourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : cubeFourCap h n j ell ≤ ell/3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb : cubeFourCap h n j ell-3*δ ≤ cubeFourCap (h+δ) n (j-δ) (ell-δ) := by
    change cubeFourCap h n j ell-3*δ ≤ min n (min (j-δ) (min ((n+(j-δ)-3*(h+δ))/2) ((ell-δ)/3)))
    exact le_min (by linarith) (le_min (by linarith) (le_min (by linarith) (by linarith)))
  change cubeFourCap h n j ell-Δ*phi-3*δ ≤ cubeFourCap (h+δ) n (j-δ) (ell-δ)-Δ*phi
  linarith

theorem normalized_refined_perturbed {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (A : Finset ℕ) (k r : ℕ) (X R T phi ell Δ δ CN CE ρN ρE : ℝ),
      A ⊆ smoothNumbers X R → 0 ≤ CN → 0 ≤ CE →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ P^(1-(k:ℝ)*phi+δ) →
      P^(2*(k:ℝ)*phi) ≤ paddedSupport (2*k) r X →
      (paddedSupport (2*k) r X : ℝ) ≤ CN*P^(2*(k:ℝ)*phi+ρN) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi-δ) ≤ J →
      smoothMoment (2*k) (2*r) X R ≤ CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE) →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
      P^(ell-δ) ≤ height ((H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J)) α →
      normalizedSampledCoefficient A (2*k) r P phi H J α σ ≤
        C*CN*CE*P^(ε+ρN+ρE-perturbedRefinedSaving k T phi ell Δ δ) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_sampling_padded_epsilon hB hε
  refine ⟨4*C, by positivity, ?_⟩
  intro P hP A k r X R T phi ell Δ δ CN CE ρN ρE hA hCN hCE H J hH hJ hV
    hHs hNl hNu hJs hmoment α σ hLs
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hden : 0 < (H:ℝ)*J*P^((2*r:ℕ)*phi) := by positivity
  unfold normalizedSampledCoefficient
  apply (div_le_iff₀ hden).mpr
  have hshape := samplingShape_le_four_rpow hP (paddedSupport_pos (2*k) r X) hJ
    hHs hNl hJs hLs
  have hmoment0 := smoothMoment_nonneg (2*k) (2*r) X R
  have hshape0 := samplingShape_nonneg H (paddedSupport (2*k) r X) J α
  let cap := fourCap (1-(k:ℝ)*phi+δ) (2*(k:ℝ)*phi)
    ((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi-δ) (ell-δ)
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
      dsimp [perturbedRefinedSaving, cap]
      ring

theorem normalized_cube_perturbed {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (A : Finset ℕ) (k r : ℕ) (X R T phi ell Δ δ CN CE ρN ρE : ℝ),
      A ⊆ smoothNumbers X R → 0 ≤ CN → 0 ≤ CE →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ P^(1-(k:ℝ)*phi+δ) →
      P^(2*(k:ℝ)*phi) ≤ paddedSupport (2*k) r X →
      (paddedSupport (2*k) r X : ℝ) ≤ CN*P^(2*(k:ℝ)*phi+ρN) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi-δ) ≤ J →
      smoothMoment (2*k) (2*r) X R ≤ CE*P^(((2*r:ℕ)-(2*(k:ℝ))+Δ)*phi+ρE) →
      ∀ (α : ℝ) (σ : ℕ → ℝ),
      P^(ell-δ) ≤ height ((H:ℝ)^3*((paddedSupport (2*k) r X : ℝ)*J)) α →
      normalizedSampledCoefficient A (2*k) r P phi H J α σ ≤
        C*CN*CE*P^(ε+ρN+ρE-perturbedCubeSaving k T phi ell Δ δ) := by
  obtain ⟨C,hC,hbound⟩ := coefficient_cube_sampling_padded_epsilon hB hε
  refine ⟨4*C, by positivity, ?_⟩
  intro P hP A k r X R T phi ell Δ δ CN CE ρN ρE hA hCN hCE H J hH hJ hV
    hHs hNl hNu hJs hmoment α σ hLs
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hden : 0 < (H:ℝ)*J*P^((2*r:ℕ)*phi) := by positivity
  unfold normalizedSampledCoefficient
  apply (div_le_iff₀ hden).mpr
  have hshape := cubeSamplingShape_le_four_rpow hP (paddedSupport_pos (2*k) r X) hJ
    hHs hNl hJs hLs
  have hmoment0 := smoothMoment_nonneg (2*k) (2*r) X R
  have hshape0 := cubeSamplingShape_nonneg H (paddedSupport (2*k) r X) J α
  let cap := cubeFourCap (1-(k:ℝ)*phi+δ) (2*(k:ℝ)*phi)
    ((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi-δ) (ell-δ)
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
      dsimp [perturbedCubeSaving, cap]
      ring

/-- Source-conditional refined resource with fixed physical scale constants and an arbitrary common conductor. -/
theorem normalized_refined_common_conductor {k r c : ℕ} {B T phi Δ ε CH CJ CV : ℝ}
    (hc : 0 < c) (hCH : 1 ≤ CH) (hCJ : 1 ≤ CJ) (hCV : 1 ≤ CV)
    (hk : 0 < k) (hr : 1 ≤ r) (hB : 0 ≤ B) (hphi : 0 < phi) (hε : 0 < ε)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ CH*P^(1-(k:ℝ)*phi) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ≤ CJ*(J:ℝ) →
      ∀ (α ell W : ℝ) (σ : ℕ → ℝ),
      W ≤ CV*((H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J)) →
      P^ell ≤ height W α →
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-refinedSaving k T phi ell Δ) := by
  let δ := ε/6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hkR : 0 < 2*(k : ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let ηmax := δ/(2*(k : ℝ))
  have hηmax : 0 < ηmax := div_pos hδ hkR
  obtain ⟨η,CE,P₀,hη,hηcap,hCE,hP₀,hmoment⟩ :=
    scaled_smoothMoment_of_admissible hadm hlam hphi hδ hηmax
  obtain ⟨C,hC,hbound⟩ := normalized_refined_perturbed hB hδ
  let CN : ℝ := ((r : ℝ)+1)*2^(2*k)
  have hCN : 0 < CN := by dsimp [CN]; positivity
  let K : ℝ := max 1 (max CH (max CJ (CV*(c : ℝ))))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hCHK : CH ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCJK : CJ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCVcK : CV*(c : ℝ) ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hηloss : 2*(k : ℝ)*η ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left hηcap hkR.le
    have hid : 2*(k : ℝ)*ηmax=δ := by dsimp [ηmax]; field_simp
    rwa [hid] at hh
  refine ⟨η,C*CN*CE,max P₀ (K^(1/δ)),hη,by positivity,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hV hHs hJs α ell W σ hWV hLs
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hKP : K ≤ P^δ := fixed_constant_rpow_bound hK hδ ((le_max_right _ _).trans hP₀')
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNpos : (0 : ℝ) < (paddedSupport (2*k) r (P^phi*R) : ℝ) := by
    exact_mod_cast paddedSupport_pos (2*k) r (P^phi*R)
  have hVpos : 0 < (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) := by positivity
  have hHs' : (H : ℝ) ≤ P^(1-(k : ℝ)*phi+δ) := by
    calc
      _ ≤ CH*P^(1-(k : ℝ)*phi) := hHs
      _ ≤ P^δ*P^(1-(k : ℝ)*phi) := mul_le_mul_of_nonneg_right
        (hCHK.trans hKP) (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  have hJs' : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi-δ) ≤ J := by
    have hh : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤ P^δ*(J : ℝ) :=
      hJs.trans (mul_le_mul_of_nonneg_right (hCJK.trans hKP) hJpos.le)
    rw [Real.rpow_sub hPpos]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hPpos _)).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨hNl,hNu⟩ := paddedSupport_power_scales (2*k) r hP1 hphi.le hr hR hRup
  have hNl' : P^(2*(k : ℝ)*phi) ≤ paddedSupport (2*k) r (P^phi*R) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hNl
  have hNu' : (paddedSupport (2*k) r (P^phi*R) : ℝ) ≤ CN*P^(2*(k : ℝ)*phi+2*(k : ℝ)*η) := by
    simpa only [CN,Nat.cast_mul,Nat.cast_ofNat] using hNu
  have hm : smoothMoment (2*k) (2*r) (P^phi*R) R ≤
      CE*P^(((2*r:ℕ)-(2*(k : ℝ))+Δ)*phi+δ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmoment P hPP₀ R hR hRup
  have hheight := common_height_phase_shift hPpos hVpos hCV hWV c hc (hCVcK.trans hKP) hLs
  have hb := hbound P hP1 A k r (P^phi*R) R T phi ell Δ δ CN CE (2*(k : ℝ)*η) δ
    hA hCN.le hCE.le H J hH hJ hV hHs' hNl' hNu' hJs' hm ((c : ℝ)*α) σ hheight
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C*CN*CE)
  apply Real.rpow_le_rpow_of_exponent_le hP1
  have hs := perturbedRefinedSaving_lower (k : ℝ) T phi ell Δ δ hδ.le
  have heq : 6*δ=ε := by dsimp [δ]; ring
  linarith

/-- The cube counterpart with exactly the same physical comparison assumptions. -/
theorem normalized_cube_common_conductor {k r c : ℕ} {B T phi Δ ε CH CJ CV : ℝ}
    (hc : 0 < c) (hCH : 1 ≤ CH) (hCJ : 1 ≤ CJ) (hCV : 1 ≤ CV)
    (hk : 0 < k) (hr : 1 ≤ r) (hB : 0 ≤ B) (hphi : 0 < phi) (hε : 0 < ε)
    (hadm : AdmissibleExcess (2*k) (2*r) Δ)
    (hlam : 0 ≤ ((2*r:ℕ):ℝ)-((2*k:ℕ):ℝ)+Δ) :
    ∃ η C P₀ : ℝ, 0 < η ∧ 0 < C ∧ 2 ≤ P₀ ∧
      ∀ P : ℝ, P₀ ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ A : Finset ℕ, A ⊆ smoothNumbers (P^phi*R) R →
      ∀ H J : ℕ, 0 < H → 0 < J →
      (H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) ≤ P^B →
      (H:ℝ) ≤ CH*P^(1-(k:ℝ)*phi) →
      P^((k:ℝ)-3-(k:ℝ)*T+(k:ℝ)*phi) ≤ CJ*(J:ℝ) →
      ∀ (α ell W : ℝ) (σ : ℕ → ℝ),
      W ≤ CV*((H:ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J)) →
      P^ell ≤ height W α →
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-cubeSaving k T phi ell Δ) := by
  let δ := ε/6
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hkR : 0 < 2*(k : ℝ) := by exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hk
  let ηmax := δ/(2*(k : ℝ))
  have hηmax : 0 < ηmax := div_pos hδ hkR
  obtain ⟨η,CE,P₀,hη,hηcap,hCE,hP₀,hmoment⟩ :=
    scaled_smoothMoment_of_admissible hadm hlam hphi hδ hηmax
  obtain ⟨C,hC,hbound⟩ := normalized_cube_perturbed hB hδ
  let CN : ℝ := ((r : ℝ)+1)*2^(2*k)
  have hCN : 0 < CN := by dsimp [CN]; positivity
  let K : ℝ := max 1 (max CH (max CJ (CV*(c : ℝ))))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := zero_lt_one.trans_le hK1
  have hCHK : CH ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCJK : CJ ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCVcK : CV*(c : ℝ) ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hηloss : 2*(k : ℝ)*η ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left hηcap hkR.le
    have hid : 2*(k : ℝ)*ηmax=δ := by dsimp [ηmax]; field_simp
    rwa [hid] at hh
  refine ⟨η,C*CN*CE,max P₀ (K^(1/δ)),hη,by positivity,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hV hHs hJs α ell W σ hWV hLs
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hKP : K ≤ P^δ := fixed_constant_rpow_bound hK hδ ((le_max_right _ _).trans hP₀')
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNpos : (0 : ℝ) < (paddedSupport (2*k) r (P^phi*R) : ℝ) := by
    exact_mod_cast paddedSupport_pos (2*k) r (P^phi*R)
  have hVpos : 0 < (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) := by positivity
  have hHs' : (H : ℝ) ≤ P^(1-(k : ℝ)*phi+δ) := by
    calc
      _ ≤ CH*P^(1-(k : ℝ)*phi) := hHs
      _ ≤ P^δ*P^(1-(k : ℝ)*phi) := mul_le_mul_of_nonneg_right
        (hCHK.trans hKP) (Real.rpow_nonneg hPpos.le _)
      _ = _ := by rw [← Real.rpow_add hPpos]; congr 1; ring
  have hJs' : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi-δ) ≤ J := by
    have hh : P^((k : ℝ)-3-(k : ℝ)*T+(k : ℝ)*phi) ≤ P^δ*(J : ℝ) :=
      hJs.trans (mul_le_mul_of_nonneg_right (hCJK.trans hKP) hJpos.le)
    rw [Real.rpow_sub hPpos]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hPpos _)).mpr (by simpa only [mul_comm] using hh)
  obtain ⟨hNl,hNu⟩ := paddedSupport_power_scales (2*k) r hP1 hphi.le hr hR hRup
  have hNl' : P^(2*(k : ℝ)*phi) ≤ paddedSupport (2*k) r (P^phi*R) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hNl
  have hNu' : (paddedSupport (2*k) r (P^phi*R) : ℝ) ≤ CN*P^(2*(k : ℝ)*phi+2*(k : ℝ)*η) := by
    simpa only [CN,Nat.cast_mul,Nat.cast_ofNat] using hNu
  have hm : smoothMoment (2*k) (2*r) (P^phi*R) R ≤
      CE*P^(((2*r:ℕ)-(2*(k : ℝ))+Δ)*phi+δ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hmoment P hPP₀ R hR hRup
  have hheight := common_height_phase_shift hPpos hVpos hCV hWV c hc (hCVcK.trans hKP) hLs
  have hb := hbound P hP1 A k r (P^phi*R) R T phi ell Δ δ CN CE (2*(k : ℝ)*η) δ
    hA hCN.le hCE.le H J hH hJ hV hHs' hNl' hNu' hJs' hm ((c : ℝ)*α) σ hheight
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C*CN*CE)
  apply Real.rpow_le_rpow_of_exponent_le hP1
  have hs := perturbedCubeSaving_lower (k : ℝ) T phi ell Δ δ hδ.le
  have heq : 6*δ=ε := by dsimp [δ]; ring
  linarith

#print axioms physical_conductor_lower
#print axioms normalized_refined_common_conductor
#print axioms normalized_cube_common_conductor

end Waring.NormalizedCoefficient

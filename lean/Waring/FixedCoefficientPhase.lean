import Waring.NormalizedCubeCoefficient
import Waring.RationalHeightMin

/-!
# Fixed integer phase multipliers in the normalized coefficient resources

The actual coefficient phase may be c*alpha for a fixed positive integer c.
Its rational height need not equal that of alpha. We account for the exact
factor c in the height comparison and absorb it at a sufficiently large P.
-/

noncomputable section
namespace Waring.NormalizedCoefficient
open CoefficientPower SmoothMoments CubicCoefficientSampling ResourceScales RationalHeight

/-- Fixed positive constants are eventually bounded by any positive power. -/
theorem fixed_constant_rpow_bound {c δ P : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hP : c^(1/δ) ≤ P) : c ≤ P^δ := by
  calc
    c = (c^(1/δ))^δ := by
      rw [← Real.rpow_mul hc.le,one_div_mul_cancel hδ.ne',Real.rpow_one]
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hc.le _) hP hδ.le

/-- The fixed phase multiplier is retained exactly before exponent shifting. -/
theorem height_phase_lower_shift {P V ell δ α : ℝ} (hP : 0 < P) (hV : 0 < V)
    (c : ℕ) (hc : 0 < c) (hcP : (c : ℝ) ≤ P^δ)
    (hL : P^ell ≤ height V α) : P^(ell-δ) ≤ height V ((c : ℝ)*α) := by
  have hphase := height_mul_phase_lower (α := α) hV hc
  have hh : P^ell ≤ P^δ*height V ((c : ℝ)*α) :=
    hL.trans (hphase.trans (mul_le_mul_of_nonneg_right hcP (height_pos _ _).le))
  rw [Real.rpow_sub hP]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hP _)).mpr (by simpa only [mul_comm] using hh)

/-- Shifting the intrinsic height exponent down by delta loses at most delta
in the refined saving, uniformly in all other scale parameters. -/
theorem refinedSaving_shift_lower (k T phi ell Δ δ : ℝ) (hδ : 0 ≤ δ) :
    refinedSaving k T phi ell Δ-δ ≤ refinedSaving k T phi (ell-δ) Δ := by
  let h := 1-k*phi
  let n := 2*k*phi
  let j := k-3-k*T+k*phi
  have hn : fourCap h n j ell ≤ n := min_le_left _ _
  have hj : fourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hm : fourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : fourCap h n j ell ≤ ell-2*h :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb : fourCap h n j ell-δ ≤ fourCap h n j (ell-δ) := by
    change fourCap h n j ell-δ ≤ min n (min j (min ((n+j-3*h)/2) ((ell-δ)-2*h)))
    exact le_min (by linarith) (le_min (by linarith) (le_min (by linarith) (by linarith)))
  change fourCap h n j ell-Δ*phi-δ ≤ fourCap h n j (ell-δ)-Δ*phi
  linarith

/-- A common unit Lipschitz bound also suffices for the sharper cube branch. -/
theorem cubeSaving_shift_lower (k T phi ell Δ δ : ℝ) (hδ : 0 ≤ δ) :
    cubeSaving k T phi ell Δ-δ ≤ cubeSaving k T phi (ell-δ) Δ := by
  let h := 1-k*phi
  let n := 2*k*phi
  let j := k-3-k*T+k*phi
  have hn : cubeFourCap h n j ell ≤ n := min_le_left _ _
  have hj : cubeFourCap h n j ell ≤ j := (min_le_right _ _).trans (min_le_left _ _)
  have hm : cubeFourCap h n j ell ≤ (n+j-3*h)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hl : cubeFourCap h n j ell ≤ ell/3 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb : cubeFourCap h n j ell-δ ≤ cubeFourCap h n j (ell-δ) := by
    change cubeFourCap h n j ell-δ ≤ min n (min j (min ((n+j-3*h)/2) ((ell-δ)/3)))
    exact le_min (by linarith) (le_min (by linarith) (le_min (by linarith) (by linarith)))
  change cubeFourCap h n j ell-Δ*phi-δ ≤ cubeFourCap h n j (ell-δ)-Δ*phi
  linarith

/-- The refined resource at a fixed integer multiple of the common phase. -/
theorem normalized_refined_fixed_phase_of_admissible {k r c : ℕ} {B T phi Δ ε : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hr : 1 ≤ r) (hB : 0 ≤ B) (hphi : 0 < phi) (hε : 0 < ε)
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
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-refinedSaving k T phi ell Δ) := by
  obtain ⟨η,C,P₀,hη,hC,hP₀,hbound⟩ :=
    normalized_refined_of_admissible hk hr hB hphi (half_pos hε) hadm hlam
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨η,C,max P₀ ((c : ℝ)^(1/(ε/2))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hV hHs hJs α ell σ hLs
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hcP : (c : ℝ) ≤ P^(ε/2) := fixed_constant_rpow_bound hcR (half_pos hε)
    ((le_max_right _ _).trans hP₀')
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNpos : (0 : ℝ) < (paddedSupport (2*k) r (P^phi*R) : ℝ) := by
    exact_mod_cast paddedSupport_pos (2*k) r (P^phi*R)
  have hVpos : 0 < (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) := by positivity
  have hheight := height_phase_lower_shift hPpos hVpos c hc hcP hLs
  have hb := hbound P hPP₀ R hR hRup A hA H J hH hJ hV hHs hJs
    ((c : ℝ)*α) (ell-ε/2) σ hheight
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hP1
  have hs := refinedSaving_shift_lower (k : ℝ) T phi ell Δ (ε/2) (half_pos hε).le
  linarith

/-- The cube resource at a fixed integer multiple of the common phase. -/
theorem normalized_cube_fixed_phase_of_admissible {k r c : ℕ} {B T phi Δ ε : ℝ}
    (hc : 0 < c) (hk : 0 < k) (hr : 1 ≤ r) (hB : 0 ≤ B) (hphi : 0 < phi) (hε : 0 < ε)
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
      normalizedSampledCoefficient A (2*k) r P phi H J ((c : ℝ)*α) σ ≤
        C*P^(ε-cubeSaving k T phi ell Δ) := by
  obtain ⟨η,C,P₀,hη,hC,hP₀,hbound⟩ :=
    normalized_cube_of_admissible hk hr hB hphi (half_pos hε) hadm hlam
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨η,C,max P₀ ((c : ℝ)^(1/(ε/2))),hη,hC,hP₀.trans (le_max_left _ _),?_⟩
  intro P hP₀' R hR hRup A hA H J hH hJ hV hHs hJs α ell σ hLs
  have hPP₀ : P₀ ≤ P := (le_max_left _ _).trans hP₀'
  have hP2 : 2 ≤ P := hP₀.trans hPP₀
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hcP : (c : ℝ) ≤ P^(ε/2) := fixed_constant_rpow_bound hcR (half_pos hε)
    ((le_max_right _ _).trans hP₀')
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hNpos : (0 : ℝ) < (paddedSupport (2*k) r (P^phi*R) : ℝ) := by
    exact_mod_cast paddedSupport_pos (2*k) r (P^phi*R)
  have hVpos : 0 < (H : ℝ)^3*((paddedSupport (2*k) r (P^phi*R) : ℝ)*J) := by positivity
  have hheight := height_phase_lower_shift hPpos hVpos c hc hcP hLs
  have hb := hbound P hPP₀ R hR hRup A hA H J hH hJ hV hHs hJs
    ((c : ℝ)*α) (ell-ε/2) σ hheight
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hP1
  have hs := cubeSaving_shift_lower (k : ℝ) T phi ell Δ (ε/2) (half_pos hε).le
  linarith

#print axioms height_phase_lower_shift
#print axioms normalized_refined_fixed_phase_of_admissible
#print axioms normalized_cube_fixed_phase_of_admissible
end Waring.NormalizedCoefficient

import Waring.SampledQuadraticAsymptotic

/-!
# The two concave normalized quadratic fourth-moment resources

Both branches are obtained from the actual sampled fourth moment. The older
branch retains its harmless height-range cap; the refined branch uses the
second short-height bound. Arbitrary real modulation for each sample is allowed.
-/

noncomputable section
open scoped BigOperators
namespace Waring.NormalizedQuadratic
open RationalHeight

def z4Saving (ell h : ℝ) : ℝ := min ell (min 2 h)
def z4RefinedSaving (ell h : ℝ) : ℝ := min 2 (2*ell-h)

def normalizedFourth (s : Finset ℕ) (a b : ℕ → ℤ) (t : ℕ → ℝ)
    (c : ℕ) (P H α : ℝ) : ℝ :=
  (∑ q ∈ s, ‖∑ z ∈ Finset.Icc (a q) (b q),
    QuadraticModulation.e ((c : ℝ)*((q : ℝ)*α)*(z : ℝ)^2+t q*z)‖^4)/(H*P^4)

/-- Elementary normalization of the genuine fourth-moment shape. -/
theorem fourth_shape_bound {P H L cap : ℝ} (hP : 1 ≤ P) (hH : 0 ≤ H)
    (hcap : cap ≤ 2)
    (hmin : min (H/L) (H^2/L^2) ≤ H*P^(-cap)) :
    H*P^2+P^4*min (H/L) (H^2/L^2) ≤ 2*H*P^4*P^(-cap) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hid : P^2 = P^4*P^(-2:ℝ) := by
    rw [Real.rpow_neg hPpos.le]
    norm_num only [Real.rpow_ofNat]
    field_simp
  have hfirst : H*P^2 ≤ H*P^4*P^(-cap) := by
    rw [hid]
    have hb := Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap)
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ H*P^4 by positivity)
    simpa only [mul_assoc] using hm
  have hsecond := mul_le_mul_of_nonneg_left hmin (show 0 ≤ P^4 by positivity)
  nlinarith only [hfirst,hsecond]

/-- The old cap is min(ell,2,h); its h component is a valid weakening. -/
theorem fourth_shape_old {P H L ell h : ℝ} (hP : 1 ≤ P) (hH : 0 ≤ H)
    (hL : 0 < L) (hLscale : P^ell ≤ L) :
    H*P^2+P^4*min (H/L) (H^2/L^2) ≤ 2*H*P^4*P^(-z4Saving ell h) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hcapell : z4Saving ell h ≤ ell := min_le_left _ _
  have hcap2 : z4Saving ell h ≤ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrec : 1/L ≤ P^(-ell) := by
    rw [Real.rpow_neg hPpos.le]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos ell) hLscale
  apply fourth_shape_bound hP hH hcap2
  calc
    min (H/L) (H^2/L^2) ≤ H/L := min_le_left _ _
    _ = H*(1/L) := by ring
    _ ≤ H*P^(-ell) := mul_le_mul_of_nonneg_left hrec hH
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcapell)) hH

/-- The refined concave cap is min(2,2ell-h). -/
theorem fourth_shape_refined {P H L ell h : ℝ} (hP : 1 ≤ P) (hH : 0 ≤ H)
    (hL : 0 < L) (hHscale : H ≤ P^h) (hLscale : P^ell ≤ L) :
    H*P^2+P^4*min (H/L) (H^2/L^2) ≤ 2*H*P^4*P^(-z4RefinedSaving ell h) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hcap : z4RefinedSaving ell h ≤ 2*ell-h := min_le_right _ _
  have hcap2 : z4RefinedSaving ell h ≤ 2 := min_le_left _ _
  have hden : P^(2*ell) ≤ L^2 := by
    calc
      _ = (P^ell)^2 := by rw [← Real.rpow_mul_natCast hPpos.le]; congr 1; ring
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hPpos.le ell) hLscale 2
  have hratio : H/L^2 ≤ P^(-(2*ell-h)) := by
    calc
      _ ≤ P^h/P^(2*ell) :=
        div_le_div₀ (Real.rpow_nonneg hPpos.le h) hHscale
          (Real.rpow_pos_of_pos hPpos _) hden
      _ = P^(h-2*ell) := (Real.rpow_sub hPpos _ _).symm
      _ = _ := by congr 1; ring
  apply fourth_shape_bound hP hH hcap2
  calc
    min (H/L) (H^2/L^2) ≤ H^2/L^2 := min_le_right _ _
    _ = H*(H/L^2) := by ring
    _ ≤ H*P^(-(2*ell-h)) := mul_le_mul_of_nonneg_left hratio hH
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg hcap)) hH

/-- Converting a proved shape bound to the actual normalized finite sum. -/
theorem normalize_fourth_bound {s : Finset ℕ} {a b : ℕ → ℤ} {t : ℕ → ℝ}
    {c : ℕ} {P H α C ε cap X : ℝ} (hP : 0 < P) (hH : 0 < H) (hC : 0 ≤ C)
    (hmoment : (∑ q ∈ s, ‖∑ z ∈ Finset.Icc (a q) (b q),
      QuadraticModulation.e ((c : ℝ)*((q : ℝ)*α)*(z : ℝ)^2+t q*z)‖^4) ≤ C*P^ε*X)
    (hshape : X ≤ 2*H*P^4*P^(-cap)) :
    normalizedFourth s a b t c P H α ≤ (2*C)*P^(ε-cap) := by
  unfold normalizedFourth
  apply (div_le_iff₀ (by positivity : 0 < H*P^4)).mpr
  calc
    _ ≤ C*P^ε*X := hmoment
    _ ≤ C*P^ε*(2*H*P^4*P^(-cap)) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = (2*C)*(P^ε*P^(-cap))*(H*P^4) := by ring
    _ = _ := by rw [← Real.rpow_add hP, sub_eq_add_neg]

/-- Both exact fourth-moment resource branches, uniformly in the shell height
and all real sample-dependent modulations. No pointwise, counting, divisor,
logarithmic, or transference estimate remains a hypothesis. -/
theorem normalized_fourth_resources_epsilon (B : ℝ) (hB : 0 ≤ B) (c : ℕ) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P → ∀ H : ℝ, 1 ≤ H → H ≤ P^B →
      ∀ α ell h : ℝ, H ≤ P^h → P^ell ≤ height (H*P^2) α →
      ∀ s : Finset ℕ, ∀ a b : ℕ → ℤ, ∀ t : ℕ → ℝ,
      (∀ q ∈ s, 0 < q ∧ (q : ℝ) ≤ H) →
      (∀ q ∈ s, a q ≤ b q) →
      (∀ q ∈ s, (((b q+1-a q).toNat : ℕ) : ℝ) ≤ P) →
      normalizedFourth s a b t c P H α ≤ C*P^(ε-z4Saving ell h) ∧
      normalizedFourth s a b t c P H α ≤ C*P^(ε-z4RefinedSaving ell h) := by
  obtain ⟨C,hC,hbound⟩ := SampledQuadraticAsymptotic.sampled_fourth_moment_epsilon B hB c hc hε
  refine ⟨2*C,by positivity,?_⟩
  intro P hP H hH hHB α ell h hHs hLs s a b t hs hab hlength
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hHpos : 0 < H := by linarith
  have hLpos := height_pos (H*P^2) α
  have hb := hbound P hP H hH hHB α s a b t hs hab hlength
  constructor
  · exact normalize_fourth_bound hPpos hHpos hC.le hb
      (fourth_shape_old hP1 hHpos.le hLpos hLs)
  · exact normalize_fourth_bound hPpos hHpos hC.le hb
      (fourth_shape_refined hP1 hHpos.le hLpos hHs hLs)

#print axioms fourth_shape_old
#print axioms fourth_shape_refined
#print axioms normalized_fourth_resources_epsilon
end Waring.NormalizedQuadratic

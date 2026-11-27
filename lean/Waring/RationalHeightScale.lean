import Waring.RationalHeightMin

/-! # Scaling the intrinsic conductor -/

noncomputable section
namespace Waring.RationalHeight

/-- Enlarging the conductor scales height by at most the same factor. -/
theorem height_conductor_scale_upper {V W α : ℝ} (hV : 0 < V) (hVW : V ≤ W) :
    height W α ≤ (W/V)*height V α := by
  obtain ⟨r, hr⟩ := exists_minimizer hV α
  have hratio : 1 ≤ W/V := (le_div_iff₀ hV).mpr (by simpa using hVW)
  have hratio0 : 0 ≤ W/V := zero_le_one.trans hratio
  have hq : (0 : ℝ) ≤ r.den := by positivity
  apply (height_le_cost W α r).trans
  rw [← hr]
  unfold cost
  apply max_le
  · calc
      (r.den : ℝ) ≤ (W/V)*(r.den : ℝ) := by nlinarith
      _ ≤ (W/V)*max (r.den : ℝ) (V*|(r.den : ℝ)*α-(r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hratio0
  · calc
      W*|(r.den : ℝ)*α-(r.num : ℝ)| =
          (W/V)*(V*|(r.den : ℝ)*α-(r.num : ℝ)|) := by field_simp
      _ ≤ (W/V)*max (r.den : ℝ) (V*|(r.den : ℝ)*α-(r.num : ℝ)|) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hratio0

/-- The ratio conductor/height increases with the positive conductor. -/
theorem conductor_div_height_mono {V W α : ℝ} (hV : 0 < V) (hVW : V ≤ W) :
    V/height V α ≤ W/height W α := by
  have hHV := height_pos V α
  have hHW := height_pos W α
  have h := mul_le_mul_of_nonneg_right (height_conductor_scale_upper (α := α) hV hVW) hV.le
  have hid : (W/V)*height V α*V = W*height V α := by field_simp
  rw [hid] at h
  apply (div_le_div_iff₀ hHV hHW).mpr
  nlinarith

#print axioms conductor_div_height_mono
end Waring.RationalHeight

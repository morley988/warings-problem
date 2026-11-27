import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Continuous height control from two endpoint checks

Each resource in the frozen recipes is a minimum of affine functions of the
intrinsic height, possibly minus a constant. Nonnegative weighted sums remain
concave. The diagonal cap `min 1` is retained. Subtracting a nonnegative
multiple of this capped saving from an affine function is convex, so endpoint
bounds control every real height in the interval.

This is an analytic/algebraic theorem about all real heights. It does not
assert that the functions bound exponential sums; that implication is a
separate mathematical obligation.
-/

noncomputable section

namespace Waring.Height

theorem affine_convex (a b : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    a * (u * x + v * y) + b = a * (u * x + v * y) + (u + v) * b := by
      rw [huv, one_mul]
    _ = u * (a * x + b) + v * (a * y + b) := by ring

theorem affine_concave (a b : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => a * x + b) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    u * (a * x + b) + v * (a * y + b) = a * (u * x + v * y) + (u + v) * b := by ring
    _ = a * (u * x + v * y) + b := by rw [huv, one_mul]

theorem min_concave {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ Set.univ f) (hg : ConcaveOn ℝ Set.univ g) :
    ConcaveOn ℝ Set.univ (fun x => min (f x) (g x)) :=
  hf.inf hg

theorem min_four_affine_concave (a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℝ) :
    ConcaveOn ℝ Set.univ
      (fun x => min (min (min (a₁ * x + b₁) (a₂ * x + b₂))
        (a₃ * x + b₃)) (a₄ * x + b₄)) :=
  min_concave (min_concave (min_concave (affine_concave a₁ b₁)
    (affine_concave a₂ b₂)) (affine_concave a₃ b₃)) (affine_concave a₄ b₄)

theorem refined_coefficient_concave (c₁ c₂ c₃ c₄ loss : ℝ) :
    ConcaveOn ℝ Set.univ
      (fun x => min (min (min c₁ c₂) c₃) (x + c₄) - loss) := by
  have h := min_four_affine_concave 0 c₁ 0 c₂ 0 c₃ 1 c₄
  have hc := (convexOn_const loss (convex_univ : Convex ℝ (Set.univ : Set ℝ)))
  simpa only [zero_mul, zero_add, one_mul, Pi.sub_apply] using h.sub hc

theorem quadratic_refined_concave (h : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => min (2 : ℝ) (2 * x - h)) := by
  have hc := affine_concave 0 2
  have ha := affine_concave 2 (-h)
  simpa only [zero_mul, zero_add, sub_eq_add_neg] using min_concave hc ha

theorem quadratic_old_concave (h : ℝ) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => min (min x 2) h) := by
  have hx := affine_concave 1 0
  have h2 := affine_concave 0 2
  have hh := affine_concave 0 h
  simpa only [one_mul, zero_mul, zero_add, add_zero] using
    min_concave (min_concave hx h2) hh

theorem weighted_add_concave {f g : ℝ → ℝ} {w : ℝ}
    (hf : ConcaveOn ℝ Set.univ f) (hg : ConcaveOn ℝ Set.univ g)
    (hw : 0 ≤ w) :
    ConcaveOn ℝ Set.univ (fun x => w * f x + g x) := by
  simpa only [smul_eq_mul, Pi.add_apply] using (hf.smul hw).add hg

theorem diagonal_cap_concave {saving : ℝ → ℝ}
    (hs : ConcaveOn ℝ Set.univ saving) :
    ConcaveOn ℝ Set.univ (fun x => min (1 : ℝ) (saving x)) := by
  exact min_concave (concaveOn_const 1 convex_univ) hs

def residual (base slope scale : ℝ) (saving : ℝ → ℝ) (height : ℝ) : ℝ :=
  base + slope * height - scale * min 1 (saving height)

theorem residual_convex {base slope scale : ℝ} {saving : ℝ → ℝ}
    (hs : ConcaveOn ℝ Set.univ saving) (hc : 0 ≤ scale) :
    ConvexOn ℝ Set.univ (residual base slope scale saving) := by
  have hlin := affine_convex slope base
  have hcap := (diagonal_cap_concave hs).smul hc
  simpa only [residual, smul_eq_mul, Pi.sub_apply, add_comm] using hlin.sub hcap

/-- Exact endpoint bounds imply the same bound at every real height in a piece. -/
theorem residual_le_of_endpoints {base slope scale lo hi height bound : ℝ}
    {saving : ℝ → ℝ} (hs : ConcaveOn ℝ Set.univ saving) (hc : 0 ≤ scale)
    (hheight : height ∈ Set.Icc lo hi)
    (hlo : residual base slope scale saving lo ≤ bound)
    (hhi : residual base slope scale saving hi ≤ bound) :
    residual base slope scale saving height ≤ bound := by
  have h := (residual_convex (base := base) (slope := slope) hs hc).le_max_of_mem_Icc
    (Set.mem_univ lo) (Set.mem_univ hi) hheight
  exact h.trans (max_le hlo hhi)

end Waring.Height

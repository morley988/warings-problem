import WaringSiegel.WSL4WeilRingCharacters

/-! # Exact cubic stationary restriction in a finite ring

Average the actual sum over translations by c*t when c^2=0.  Primitive
character orthogonality removes exactly the points where c*f'(x) is nonzero.
The weighted version will also handle the unit mask at an auxiliary prime.
-/

noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical

theorem cubic_shift_of_square_zero
    {A : Type*} [CommRing A] (a b x t c : A) (hc : c^2=0) :
    a*(x+c*t)^3+b*(x+c*t) = a*x^3+b*x+(c*(3*a*x^2+b))*t := by
  calc
    _ = a*x^3+b*x+(c*(3*a*x^2+b))*t+c^2*(3*a*x*t^2+c*a*t^3) := by ring
    _ = _ := by rw [hc, zero_mul, add_zero]

theorem weighted_cubic_sum_stationary_restriction
    {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (a b c : A) (hc : c^2=0)
    (w : A → ℂ) (hw : ∀ x t, w (x+c*t)=w x) :
    (∑ x : A, w x*ψ (a*x^3+b*x)) =
      ∑ x ∈ Finset.univ.filter (fun x : A => c*(3*a*x^2+b)=0), w x*ψ (a*x^3+b*x) := by
  have hshift (t : A) :
      (∑ x : A, w (x+c*t)*ψ (a*(x+c*t)^3+b*(x+c*t))) =
        ∑ x : A, w x*ψ (a*x^3+b*x) :=
    (Equiv.addRight (c*t)).bijective.sum_comp (fun x : A => w x*ψ (a*x^3+b*x))
  have hchar (x : A) : (∑ t : A, ψ ((c*(3*a*x^2+b))*t)) =
      if c*(3*a*x^2+b)=0 then (Fintype.card A : ℂ) else 0 := by
    simpa [mul_comm] using AddChar.sum_mulShift (c*(3*a*x^2+b)) hψ
  have he : (Fintype.card A : ℂ)*(∑ x : A, w x*ψ (a*x^3+b*x)) =
      (Fintype.card A : ℂ)*
        (∑ x ∈ Finset.univ.filter (fun x : A => c*(3*a*x^2+b)=0), w x*ψ (a*x^3+b*x)) := by
    calc
      _ = ∑ t : A, ∑ x : A, w (x+c*t)*ψ (a*(x+c*t)^3+b*(x+c*t)) := by
        simp only [hshift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ x : A, ∑ t : A, (w x*ψ (a*x^3+b*x))*ψ ((c*(3*a*x^2+b))*t) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro t _
        rw [hw, cubic_shift_of_square_zero a b x t c hc, ψ.map_add_eq_mul]
        ring
      _ = ∑ x : A, (w x*ψ (a*x^3+b*x))*
          (if c*(3*a*x^2+b)=0 then (Fintype.card A : ℂ) else 0) := by
        simp only [← Finset.mul_sum, hchar]
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> ring
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) he

theorem mixedCubicSum_stationary_restriction
    {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (a b c : A) (hc : c^2=0) :
    mixedCubicSum ψ a b =
      ∑ x ∈ Finset.univ.filter (fun x : A => c*(3*a*x^2+b)=0), ψ (a*x^3+b*x) := by
  simpa only [mixedCubicSum, one_mul] using
    weighted_cubic_sum_stationary_restriction ψ hψ a b c hc (fun _ => 1) (by intros; rfl)

theorem mixedCubicSum_norm_le_stationary_count
    {A : Type*} [CommRing A] [Fintype A]
    (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (a b c : A) (hc : c^2=0) :
    ‖mixedCubicSum ψ a b‖ ≤
      (Finset.univ.filter (fun x : A => c*(3*a*x^2+b)=0)).card := by
  rw [mixedCubicSum_stationary_restriction ψ hψ a b c hc]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : A => c*(3*a*x^2+b)=0), ‖ψ (a*x^3+b*x)‖ :=
      norm_sum_le _ _
    _ = _ := by simp [finite_addChar_norm_one]

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.weighted_cubic_sum_stationary_restriction
#print axioms WaringSiegel.WSL4Weil.mixedCubicSum_norm_le_stationary_count

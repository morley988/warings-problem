import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-! # Complete quadratic sums with a linear twist

A difference variable and additive orthogonality evaluate the squared norm on
any finite commutative ring with a primitive complex additive character.
In particular, a unit Hessian gives the exact square-root magnitude.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace WaringLinear

variable {A : Type*} [CommRing A] [Fintype A]

theorem quadraticGauss_mul_conj (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive) (a b c : A) :
    (∑ x : A, ψ (a*x^2+b*x+c)) * conj (∑ x : A, ψ (a*x^2+b*x+c)) =
      (Fintype.card A : ℂ) * ∑ h ∈ Finset.univ.filter (fun h : A => 2*a*h=0),
        ψ (a*h^2+b*h) := by
  classical
  let f (x : A) := a*x^2+b*x+c
  change (∑ x, ψ (f x)) * conj (∑ x, ψ (f x)) = _
  calc
    _ = ∑ y, ∑ x, ψ (f x-f y) := by
      rw [map_sum, Finset.mul_sum]
      simp_rw [Finset.sum_mul, sub_eq_add_neg, ψ.map_add_eq_mul, ψ.map_neg_eq_conj]
    _ = ∑ y, ∑ h, ψ (f (h+y)-f y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact ((Equiv.addRight y).bijective.sum_comp (fun x => ψ (f x-f y))).symm
    _ = ∑ h, ψ (a*h^2+b*h) * ∑ y, ψ ((2*a*h)*y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ψ.map_add_eq_mul]
      apply congrArg ψ
      dsimp [f]
      ring
    _ = _ := by
      have hsum (u : A) : (∑ y : A, ψ (u*y)) =
          if u=0 then (Fintype.card A : ℂ) else 0 := by
        simpa [mul_comm] using AddChar.sum_mulShift u hψ
      simp_rw [hsum]
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> ring

/-- Primitive finite-ring quadratic Gauss sums have norm `√|A|` whenever the
Hessian is a unit. The linear and constant coefficients are arbitrary. -/
theorem norm_quadraticGauss_of_isUnit (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (a b c : A) (ha : IsUnit (2*a)) :
    ‖∑ x : A, ψ (a*x^2+b*x+c)‖ = Real.sqrt (Fintype.card A : ℝ) := by
  classical
  have hzero (h : A) : 2*a*h=0 ↔ h=0 := by
    simpa only [mul_zero] using ha.mul_right_inj (b := h) (c := 0)
  have h := quadraticGauss_mul_conj ψ hψ a b c
  simp only [hzero, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    zero_pow (by decide : (2:ℕ)≠0), mul_zero, add_zero, ψ.map_zero_eq_one, mul_one,
    Complex.mul_conj'] at h
  have hs : ‖∑ x : A, ψ (a*x^2+b*x+c)‖^2 = (Fintype.card A : ℝ) := by
    exact_mod_cast h
  rw [← hs,Real.sqrt_sq (norm_nonneg _)]

theorem norm_quadraticGauss_field {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a b c : F) (ha : 2*a≠0) :
    ‖∑ x : F, ψ (a*x^2+b*x+c)‖ = Real.sqrt (Fintype.card F : ℝ) :=
  norm_quadraticGauss_of_isUnit ψ (AddChar.IsPrimitive.of_ne_one hψ) a b c (isUnit_iff_ne_zero.mpr ha)

/-- Translating an integral critical point separates the complete square and
its exact additive phase, without dividing in the coefficient ring. -/
theorem quadraticGauss_stationary_phase (ψ : AddChar A ℂ) (a b c x₀ : A)
    (hx : 2*a*x₀+b=0) :
    (∑ x : A, ψ (a*x^2+b*x+c)) = ψ (a*x₀^2+b*x₀+c) * ∑ y : A, ψ (a*y^2) := by
  let f (x : A) := a*x^2+b*x+c
  calc
    _ = ∑ y : A, ψ (f (y+x₀)) :=
      ((Equiv.addRight x₀).bijective.sum_comp (fun x => ψ (f x))).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [← ψ.map_add_eq_mul]
      apply congrArg ψ
      dsimp [f]
      linear_combination y*hx

/-- A nontrivial phase on a radical translation forces exact cancellation,
including at residue characteristic two. -/
theorem quadraticGauss_eq_zero_of_radical_twist (ψ : AddChar A ℂ) (a b c h : A)
    (hz : 2*a*h=0) (hphase : ψ (a*h^2+b*h)≠1) :
    (∑ x : A, ψ (a*x^2+b*x+c)) = 0 := by
  let f (x : A) := a*x^2+b*x+c
  have hdiff (x : A) : f (x+h)=(a*h^2+b*h)+f x := by
    dsimp [f]
    linear_combination x*hz
  have hsum : (∑ x : A, ψ (f x)) = ψ (a*h^2+b*h) * ∑ x : A, ψ (f x) := by
    calc
      _ = ∑ x : A, ψ (f (x+h)) :=
        ((Equiv.addRight h).bijective.sum_comp (fun x => ψ (f x))).symm
      _ = _ := by simp only [hdiff,ψ.map_add_eq_mul,Finset.mul_sum]
  have hprod : (ψ (a*h^2+b*h)-1)*(∑ x : A, ψ (f x))=0 := by
    rw [sub_mul,one_mul,← hsum,sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hphase)

/-- If the additive phase is trivial on all Hessian-radical translations,
the Gauss norm is exactly the square root of the ring size times radical size. -/
theorem norm_quadraticGauss_of_radical_trivial (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (a b c : A) (hphase : ∀ h : A, 2*a*h=0 → ψ (a*h^2+b*h)=1) :
    ‖∑ x : A, ψ (a*x^2+b*x+c)‖ = Real.sqrt ((Fintype.card A : ℝ) *
      ((Finset.univ.filter (fun h : A => 2*a*h=0)).card : ℝ)) := by
  classical
  have hid := quadraticGauss_mul_conj ψ hψ a b c
  have hs : (∑ h ∈ Finset.univ.filter (fun x : A => 2*a*x=0), ψ (a*h^2+b*h)) =
      ((Finset.univ.filter (fun h : A => 2*a*h=0)).card : ℂ) := by
    rw [Finset.sum_congr rfl (fun h hh => hphase h (Finset.mem_filter.mp hh).2)]
    simp
  rw [hs,Complex.mul_conj'] at hid
  have hreal : ‖∑ x : A, ψ (a*x^2+b*x+c)‖^2 = (Fintype.card A : ℝ) *
      ((Finset.univ.filter (fun h : A => 2*a*h=0)).card : ℝ) := by
    exact_mod_cast hid
  rw [← hreal,Real.sqrt_sq (norm_nonneg _)]

#print axioms quadraticGauss_eq_zero_of_radical_twist
#print axioms norm_quadraticGauss_of_radical_trivial
#print axioms quadraticGauss_stationary_phase
#print axioms quadraticGauss_mul_conj
#print axioms norm_quadraticGauss_of_isUnit
#print axioms norm_quadraticGauss_field
end WaringLinear

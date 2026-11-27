import Waring.External.GafniTao.VmvtCore
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
Exact normalized-Haar identity from S. McColm's MIT-0 source
FordVinogradovIntegral.lean, commit bed45b21cb18f26f4d234422ebaa8b17e6624f05.
This extraction imports the identical finite-count core and omits unrelated
classical Ford lower bounds. The tuple box remains 1..Q in every coordinate.
-/
open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory
namespace GafniTao
noncomputable section

/-- The degree vector contributed by one source integer `1 ≤ n ≤ Q`. -/
def fordVinogradovExponent {k Q : ℕ} (n : Fin Q) : Fin k → ℤ :=
  fun j => (((n : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ)

/-- One exponential monomial in Ford's complete Weyl sum. -/
def fordVinogradovMonomial {k Q : ℕ} (n : Fin Q)
    (α : UnitAddTorus (Fin k)) : ℂ :=
  UnitAddTorus.mFourier (fordVinogradovExponent n) α

/-- The complete Weyl sum over the literal integer range `1, ..., Q`. -/
def fordVinogradovWeylSum (k Q : ℕ) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ n : Fin Q, fordVinogradovMonomial n α

/-- A nonzero Fourier character has normalized Haar integral zero; the zero
character has integral one. -/
theorem ford_integral_fourier_haar_eq (n : ℤ) :
    ∫ x : UnitAddCircle, fourier n x ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  split_ifs with hn
  · subst n
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num))

/-- Product orthogonality on the `k`-dimensional unit torus. -/
theorem ford_integral_mFourier_pi_haar_eq {k : ℕ} (h : Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k), UnitAddTorus.mFourier h α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      if h = 0 then 1 else 0 := by
  change (∫ α : UnitAddTorus (Fin k), ∏ i, fourier (h i) (α i)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [ford_integral_fourier_haar_eq]
  split_ifs with hh
  · subst h
    simp
  · simp only [Finset.prod_ite_zero, Finset.prod_const_one]
    rw [if_neg]
    simpa [funext_iff] using hh

theorem fordVinogradovPowerVector_eq_sum_exponent
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) :
    fordVinogradovPowerVector s k Q x =
      ∑ i : Fin s, fordVinogradovExponent (x i) := by
  ext j
  simp [fordVinogradovPowerVector, fordVinogradovExponent]

theorem ford_prod_monomial_eq
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (α : UnitAddTorus (Fin k)) :
    ∏ i : Fin s, fordVinogradovMonomial (x i) α =
      UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  classical
  rw [fordVinogradovPowerVector_eq_sum_exponent]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [UnitAddTorus.mFourier_add]
      exact congrArg (fun z => fordVinogradovMonomial (x a) α * z) ih

theorem ford_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordVinogradovWeylSum k Q α ^ s =
      ∑ x : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  rw [fordVinogradovWeylSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact ford_prod_monomial_eq x α

theorem ford_conj_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    conj (fordVinogradovWeylSum k Q α) ^ s =
      ∑ y : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α := by
  have h := congrArg conj (ford_vinogradov_weyl_pow s k Q α)
  simpa only [map_pow, map_sum, UnitAddTorus.mFourier_neg] using h

theorem ford_pair_character
    {s k Q : ℕ} (x y : FordVinogradovTuple s Q)
    (α : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α *
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α =
      UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add]

/-- Complex-valued orthogonality form of Ford's equation (1.3). -/
theorem ford_vinogradov_torus_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordVinogradovWeylSum k Q α ^ s *
          conj (fordVinogradovWeylSum k Q α) ^ s
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℂ) := by
  simp_rw [ford_vinogradov_weyl_pow, ford_conj_vinogradov_weyl_pow,
    Finset.sum_mul_sum]
  simp_rw [ford_pair_character]
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hchar (x y : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    rw [← integrableOn_univ]
    have hc : Continuous (fun α : UnitAddTorus (Fin k) =>
        UnitAddTorus.mFourier
          (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) :=
      (UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y)).continuous
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hinner (x : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          ∑ y : FordVinogradovTuple s Q,
            UnitAddTorus.mFourier
              (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    exact integrable_finset_sum Finset.univ fun y _hy => hchar x y
  change (∫ α : UnitAddTorus (Fin k),
      ∑ x : FordVinogradovTuple s Q,
        ∑ y : FordVinogradovTuple s Q,
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α ∂μ) = _
  rw [MeasureTheory.integral_finset_sum Finset.univ (fun x _hx => hinner x)]
  calc
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ∫ α : UnitAddTorus (Fin k),
              UnitAddTorus.mFourier
                (fordVinogradovPowerVector s k Q x -
                  fordVinogradovPowerVector s k Q y) α ∂μ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact MeasureTheory.integral_finset_sum Finset.univ (fun y _hy => hchar x y)
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            if fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y = 0
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact ford_integral_mFourier_pi_haar_eq _
    _ = (fordVinogradovMomentNat s k Q : ℂ) := by
        simp only [fordVinogradovMomentNat, fordVinogradovShiftedCountNat,
          fordRepresentationCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_product]

theorem ford_vinogradov_torus_real_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k), ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          ((‖fordVinogradovWeylSum k Q α‖ ^ (2 * s) : ℝ) : ℂ)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ((∫ α : UnitAddTorus (Fin k),
          ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← hcast]
  simpa only [ford_pow_mul_conj_pow, Complex.ofReal_natCast, Complex.ofReal_pow] using
    ford_vinogradov_torus_mean_eq s k Q


/-- The same literal complete moment on the half-open real unit cube.
The product quotient map preserves the explicitly normalized Haar measure. -/
theorem ford_equation_1_3 (s k Q : ℕ) :
    (∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1},
      ‖fordVinogradovWeylSum k Q (fun j => (α j : UnitAddCircle))‖ ^ (2 * s)) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let qmap : (Fin k → ℝ) → UnitAddTorus (Fin k) :=
    fun α j => (α j : UnitAddCircle)
  let μ : Measure (Fin k → ℝ) :=
    Measure.pi (fun _ : Fin k => volume.restrict (Set.Ioc (0 : ℝ) 1))
  let ν : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    norm_num
  have hone : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, hvol] using UnitAddCircle.measurePreserving_mk 0
  have hpres : MeasurePreserving qmap μ ν :=
    measurePreserving_pi _ _ (fun _ : Fin k => hone)
  have hbox :
      {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1} =
        Set.univ.pi (fun _ : Fin k => Set.Ioc (0 : ℝ) 1) := by
    ext α
    simp
  have hrestrict :
      (volume : Measure (Fin k → ℝ)).restrict
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1} = μ := by
    change (Measure.pi (fun _ : Fin k => (volume : Measure ℝ))).restrict _ = μ
    rw [hbox, Measure.restrict_pi_pi]
  have hcont : Continuous
      (fun α : UnitAddTorus (Fin k) => ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)) := by
    apply Continuous.pow
    apply Continuous.norm
    unfold fordVinogradovWeylSum fordVinogradovMonomial
    exact continuous_finset_sum _ fun n _ =>
      (UnitAddTorus.mFourier (fordVinogradovExponent n)).continuous
  have hi := integral_map (μ := μ) hpres.measurable.aemeasurable hcont.aestronglyMeasurable
  rw [hpres.map_eq] at hi
  rw [hrestrict]
  exact hi.symm.trans (ford_vinogradov_torus_real_mean_eq s k Q)

#print axioms ford_vinogradov_torus_mean_eq
#print axioms ford_vinogradov_torus_real_mean_eq
#print axioms ford_equation_1_3
end
end GafniTao

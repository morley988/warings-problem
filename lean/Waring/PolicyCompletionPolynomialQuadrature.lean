import Waring.PolicyCompletionPolynomialCalculus
import Waring.EndgameCompletionQuadrature

/-!
# Uniform quadrature for actual polynomial phases

Dyadic refinement converts the grid error into a nonzero linear twist.
The coefficient-positive first-derivative estimate bounds every refinement
uniformly; a coarse C¹ bound identifies the limit with the actual integral.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.PolicyCompletionPolynomialQuadrature
open Polynomial QuadraticModulation EndgameCompletion
open PolicyCompletionPolynomialDiscrete PolicyCompletionPolynomialCalculus

def dilatedPolynomial (f : Polynomial ℝ) (M : ℕ) : Polynomial ℝ :=
  f.comp (C ((M : ℝ)⁻¹)*X)

theorem dilatedPolynomial_eval (f : Polynomial ℝ) (M : ℕ) (x : ℝ) :
    (dilatedPolynomial f M).eval x = f.eval (x/M) := by
  simp only [dilatedPolynomial, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, div_eq_mul_inv, mul_comm]

theorem dilatedPolynomial_nonnegative (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (M : ℕ) : NonnegativeCoefficients (dilatedPolynomial f M) := by
  intro i
  rw [dilatedPolynomial, Polynomial.comp_C_mul_X_coeff]
  exact mul_nonneg (hf i) (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)

theorem dilatedPolynomial_derivative_eval (f : Polynomial ℝ) (M : ℕ) (x : ℝ) :
    (dilatedPolynomial f M).derivative.eval x = f.derivative.eval (x/M)/M := by
  simp only [dilatedPolynomial, Polynomial.derivative_comp, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, Polynomial.derivative_X, mul_one, zero_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X]
  simp only [div_eq_mul_inv, mul_comm]

def polynomialGrid (f : Polynomial ℝ) (N M : ℕ) (β : ℝ) : ℂ :=
  (M : ℂ)⁻¹*∑ n ∈ Finset.range (M*N), e (β*f.eval ((n : ℝ)/M))

theorem polynomialGrid_one (f : Polynomial ℝ) (N : ℕ) (β : ℝ) :
    polynomialGrid f N 1 β = ∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)) := by
  simp [polynomialGrid]

theorem polynomialGrid_doubling (f : Polynomial ℝ) (N M : ℕ) (hM : 0 < M) (β : ℝ) :
    polynomialGrid f N M β-polynomialGrid f N (2*M) β =
      ((2*M : ℕ) : ℂ)⁻¹*∑ n ∈ Finset.range (2*M*N),
        e (β*(dilatedPolynomial f (2*M)).eval (n:ℝ)-(1/2 : ℝ)*n) := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have heven (n : ℕ) :
      e (β*(dilatedPolynomial f (2*M)).eval ((2*n:ℕ):ℝ)-(1/2:ℝ)*(2*n:ℕ)) =
        e (β*f.eval ((n:ℝ)/M)) := by
    rw [dilatedPolynomial_eval]
    have harg : ((2*n:ℕ):ℝ)/(2*M:ℕ)=(n:ℝ)/M := by push_cast; field_simp
    rw [harg]
    have heq : β*f.eval ((n:ℝ)/M)-(1/2:ℝ)*(2*n:ℕ) =
        β*f.eval ((n:ℝ)/M)+(-(n:ℤ):ℤ) := by push_cast; ring
    rw [heq, e_add_int]
  have hodd (n : ℕ) :
      e (β*(dilatedPolynomial f (2*M)).eval ((2*n+1:ℕ):ℝ)-(1/2:ℝ)*(2*n+1:ℕ)) =
        -e (β*f.eval (((2*n+1:ℕ):ℝ)/(2*M:ℕ))) := by
    rw [dilatedPolynomial_eval]
    have heq : β*f.eval (((2*n+1:ℕ):ℝ)/(2*M:ℕ))-(1/2:ℝ)*(2*n+1:ℕ) =
        (β*f.eval (((2*n+1:ℕ):ℝ)/(2*M:ℕ))-(1/2:ℝ))+(-(n:ℤ):ℤ) := by push_cast; ring
    rw [heq, e_add_int, sub_eq_add_neg, e_add, e_neg_half, mul_neg_one]
  have hgridEven (n : ℕ) :
      e (β*f.eval (((2*n:ℕ):ℝ)/(2*M:ℕ))) = e (β*f.eval ((n:ℝ)/M)) := by
    congr 3
    push_cast
    field_simp
  unfold polynomialGrid
  rw [show 2*M*N=2*(M*N) by ring, sum_range_even_odd, sum_range_even_odd]
  simp only [heven, hodd, hgridEven, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp
  ring

theorem polynomialGrid_doubling_bound (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (N M : ℕ) (hM : 1 ≤ M) (β : ℝ) (hβ : |β| *f.derivative.eval (N:ℝ) ≤ 1/2) :
    ‖polynomialGrid f N M β-polynomialGrid f N (2*M) β‖ ≤
      (1+Real.pi/4)/(M:ℝ) := by
  by_cases hN : N=0
  · subst N
    simp only [polynomialGrid, mul_zero, Finset.sum_range_zero, sub_self, norm_zero]
    positivity
  have hN1 : 1 ≤ N := by omega
  have hMpos : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hhalf : integerDistance (1/2:ℝ)=1/2 := by
    rw [integerDistance, one_div, round_two_inv]
    norm_num
  have hscale : |β| *(dilatedPolynomial f (2*M)).derivative.eval ((2*M*N:ℕ):ℝ) =
      (|β| *f.derivative.eval (N:ℝ))/(2*M) := by
    rw [dilatedPolynomial_derivative_eval]
    have harg : ((2*M*N:ℕ):ℝ)/(2*M:ℕ)=(N:ℝ) := by push_cast; field_simp
    rw [harg]
    push_cast
    ring
  have hsmall : |β| *(dilatedPolynomial f (2*M)).derivative.eval ((2*M*N:ℕ):ℝ) ≤
      integerDistance (1/2:ℝ)/2 := by
    rw [hscale, hhalf]
    have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*M)).mpr
    nlinarith
  have hsum := norm_polynomial_linear_sum_le (dilatedPolynomial f (2*M))
    (dilatedPolynomial_nonnegative f hf (2*M)) (2*M*N) (by nlinarith)
    β (1/2) (by rw [hhalf]; norm_num) hsmall
  rw [polynomialGrid_doubling f N M (by omega), norm_mul, norm_inv, Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  rw [hhalf]
  push_cast
  field_simp

theorem polynomialIntegral_rescale_grid (f : Polynomial ℝ) (N M : ℕ)
    (hM : 0<M) (β : ℝ) :
    polynomialIntegral (dilatedPolynomial f M) (M*N:ℕ) β =
      (M:ℂ)*polynomialIntegral f N β := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => e (β*(dilatedPolynomial f M).eval t)) (a := 0) (b := (N:ℝ)) (M:ℝ)
  have hM0 : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hid (x : ℝ) : (dilatedPolynomial f M).eval ((M:ℝ)*x) = f.eval x := by
    rw [dilatedPolynomial_eval]
    congr 1
    field_simp
  simpa only [polynomialIntegral, mul_zero, hid, Complex.real_smul, Nat.cast_mul] using h.symm

theorem polynomialGrid_coarse_error (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (N M : ℕ) (hM : 0<M) (β : ℝ) :
    ‖polynomialGrid f N M β-polynomialIntegral f N β‖ ≤
      (5+6*Real.pi*|β| *(N:ℝ)*f.derivative.eval (N:ℝ))/(M:ℝ) := by
  have hMpos : (0:ℝ)<M := by exact_mod_cast hM
  have hM0 : (M:ℝ)≠0 := hMpos.ne'
  have hMc : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
  let g := dilatedPolynomial f M
  have hg := dilatedPolynomial_nonnegative f hf M
  have h := norm_positive_sum_sub_mean_integral_le (q := 1) (by norm_num)
    (c := fun _ => 1) (by intro n; rfl) (by intro n; norm_num)
    (P := ((M*N:ℕ):ℝ)) (Nat.cast_nonneg _) (B := 1)
    (fun t => (hasDerivAt_polynomial_e g β t).differentiableAt)
    (continuous_deriv_polynomial_e g β) (by rw [norm_e])
    (fun t ht => norm_deriv_polynomial_e_le g hg β ht)
  have harg : ((M*N:ℕ):ℝ)/(M:ℝ)=(N:ℝ) := by push_cast; field_simp
  have hder : g.derivative.eval ((M*N:ℕ):ℝ)=f.derivative.eval (N:ℝ)/M := by
    rw [dilatedPolynomial_derivative_eval, harg]
  have hmean : periodicMean (fun _ : ℕ => (1:ℂ)) 1=1 := by simp [periodicMean]
  simp only [hmean, one_mul, mul_one, Nat.floor_natCast, Nat.cast_one] at h
  change ‖(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))-
    polynomialIntegral g (M*N:ℕ) β‖ ≤ _ at h
  rw [polynomialIntegral_rescale_grid f N M hM β, hder] at h
  have hrhs : 3*(1+((M*N:ℕ):ℝ)*(2*Real.pi*|β| *(f.derivative.eval (N:ℝ)/M))) =
      3*(1+2*Real.pi*|β| *(N:ℝ)*f.derivative.eval (N:ℝ)) := by push_cast; field_simp
  rw [hrhs] at h
  have hright : ‖(M:ℂ)⁻¹*(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))-
      polynomialIntegral f N β‖ ≤
      (3*(1+2*Real.pi*|β| *(N:ℝ)*f.derivative.eval (N:ℝ)))/(M:ℝ) := by
    have hid : (M:ℂ)⁻¹*(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))-
        polynomialIntegral f N β = (M:ℂ)⁻¹*((∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))-
          (M:ℂ)*polynomialIntegral f N β) := by field_simp
    rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)
  have hend : ‖polynomialGrid f N M β-
      (M:ℂ)⁻¹*(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))‖ ≤ 2/(M:ℝ) := by
    simp_rw [show ∀ n : ℕ, g.eval (n:ℝ)=f.eval ((n:ℝ)/M) from
      fun n => dilatedPolynomial_eval f M n]
    rw [sum_positive_eq_range_endpoints]
    have hid : polynomialGrid f N M β-(M:ℂ)⁻¹*
        ((∑ n ∈ Finset.range (M*N), e (β*f.eval ((n:ℝ)/M)))+
          e (β*f.eval (((M*N:ℕ):ℝ)/M))-e (β*f.eval ((0:ℝ)/M))) =
        (M:ℂ)⁻¹*(e (β*f.eval ((0:ℝ)/M))-e (β*f.eval (((M*N:ℕ):ℝ)/M))) := by
      unfold polynomialGrid
      ring
    simp only [Nat.cast_zero]
    rw [hid, norm_mul, norm_inv, Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans_eq
    rw [norm_e, norm_e]
    ring
  calc
    _ ≤ ‖polynomialGrid f N M β-
        (M:ℂ)⁻¹*(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))‖+
        ‖(M:ℂ)⁻¹*(∑ n ∈ Finset.Icc 1 (M*N), e (β*g.eval (n:ℝ)))-polynomialIntegral f N β‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2/(M:ℝ)+(3*(1+2*Real.pi*|β| *(N:ℝ)*f.derivative.eval (N:ℝ)))/(M:ℝ) :=
      add_le_add hend hright
    _ = _ := by ring

theorem polynomialGrid_dyadic_error (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (N J : ℕ) (β : ℝ) (hβ : |β| *f.derivative.eval (N:ℝ) ≤ 1/2) :
    ‖polynomialGrid f N 1 β-polynomialGrid f N (2^J) β‖ ≤ 2+Real.pi/2 := by
  let u : ℕ → ℂ := fun j => polynomialGrid f N (2^j) β
  have hstep (j : ℕ) : ‖u (j+1)-u j‖ ≤ (1+Real.pi/4)/((2^j:ℕ):ℝ) := by
    dsimp [u]
    rw [norm_sub_rev, show 2^(j+1)=2*2^j by rw [pow_succ, Nat.mul_comm]]
    exact polynomialGrid_doubling_bound f hf N (2^j) (Nat.one_le_pow _ _ (by norm_num)) β hβ
  have hgeom : (∑ j ∈ Finset.range J, (1/2:ℝ)^j) ≤ 2 := by
    have h := geom_sum_mul (1/2:ℝ) J
    nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) J]
  calc
    _ = ‖∑ j ∈ Finset.range J, (u (j+1)-u j)‖ := by
      rw [Finset.sum_range_sub, norm_sub_rev]
      rfl
    _ ≤ ∑ j ∈ Finset.range J, ‖u (j+1)-u j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range J, (1+Real.pi/4)/((2^j:ℕ):ℝ) :=
      Finset.sum_le_sum (fun j _ => hstep j)
    _ = (1+Real.pi/4)*∑ j ∈ Finset.range J, (1/2:ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, ← inv_pow, one_div]
    _ ≤ (1+Real.pi/4)*2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

theorem polynomial_range_quadrature (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (N : ℕ) (β : ℝ) (hβ : |β| *f.derivative.eval (N:ℝ) ≤ 1/2) :
    ‖(∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)))-polynomialIntegral f N β‖ ≤ 2+Real.pi/2 := by
  let B : ℝ := 5+6*Real.pi*|β| *(N:ℝ)*f.derivative.eval (N:ℝ)
  have hb (J : ℕ) :
      ‖(∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)))-polynomialIntegral f N β‖ ≤
        (2+Real.pi/2)+B/((2^J:ℕ):ℝ) := by
    rw [← polynomialGrid_one]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (polynomialGrid f N (2^J) β) _).trans
      (add_le_add (polynomialGrid_dyadic_error f hf N J β hβ)
        (polynomialGrid_coarse_error f hf N (2^J) (pow_pos (by norm_num) _) β))
  have ht : Tendsto (fun J : ℕ => (2+Real.pi/2)+B/((2^J:ℕ):ℝ)) atTop (𝓝 (2+Real.pi/2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      ((tendsto_const_div_atTop_nhds_zero_nat B).comp
        (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<2)))
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hb)

theorem polynomial_positive_quadrature (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    (N : ℕ) (β : ℝ) (hβ : |β| *f.derivative.eval (N:ℝ) ≤ 1/2) :
    ‖(∑ n ∈ Finset.Icc 1 N, e (β*f.eval (n:ℝ)))-polynomialIntegral f N β‖ ≤ 4+Real.pi/2 := by
  have hmain := polynomial_range_quadrature f hf N β hβ
  rw [sum_positive_eq_range_endpoints]
  have hid : (∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)))+
      e (β*f.eval (N:ℝ))-e (β*f.eval (0:ℝ))-polynomialIntegral f N β =
      ((∑ n ∈ Finset.range N, e (β*f.eval (n:ℝ)))-polynomialIntegral f N β)+
        (e (β*f.eval (N:ℝ))-e (β*f.eval (0:ℝ))) := by ring
  simp only [Nat.cast_zero]
  rw [hid]
  apply (norm_add_le _ _).trans
  have hend : ‖e (β*f.eval (N:ℝ))-e (β*f.eval (0:ℝ))‖ ≤ 2 := by
    simpa only [norm_e, one_add_one_eq_two] using norm_sub_le
      (e (β*f.eval (N:ℝ))) (e (β*f.eval (0:ℝ)))
  exact (add_le_add hmain hend).trans_eq (by ring)

theorem polynomial_quadrature (f : Polynomial ℝ) (hf : NonnegativeCoefficients f)
    {P β : ℝ} (hP : 0 ≤ P) (hβ : |β| *f.derivative.eval P ≤ 1/2) :
    ‖(∑ n ∈ ordinaryNumbers P, e (β*f.eval (n:ℝ)))-polynomialIntegral f P β‖ ≤ 5+Real.pi/2 := by
  have hN : (⌊P⌋₊:ℝ)≤P := Nat.floor_le hP
  have hsmall : |β| *f.derivative.eval (⌊P⌋₊:ℝ) ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (eval_monotone f.derivative (derivative_nonnegative f hf)
      (Nat.cast_nonneg _) hN) (abs_nonneg _)).trans hβ
  have hmain := polynomial_positive_quadrature f hf ⌊P⌋₊ β hsmall
  have hfc := continuous_polynomial_e f β
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hfc.intervalIntegrable 0 (⌊P⌋₊:ℝ)) (hfc.intervalIntegrable (⌊P⌋₊:ℝ) P)
  change polynomialIntegral f (⌊P⌋₊:ℝ) β+
    (∫ t in (⌊P⌋₊:ℝ)..P, e (β*f.eval t))=polynomialIntegral f P β at hadd
  have htail : ‖polynomialIntegral f (⌊P⌋₊:ℝ) β-polynomialIntegral f P β‖ ≤ 1 := by
    rw [norm_sub_rev, ← hadd, add_sub_cancel_left]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      (a := (⌊P⌋₊:ℝ)) (b := P) (fun t _ => (norm_e (β*f.eval t)).le)
    rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hN)] at hh
    exact hh.trans (by have := Nat.lt_floor_add_one P; linarith)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (polynomialIntegral f (⌊P⌋₊:ℝ) β) _).trans
    ((add_le_add hmain htail).trans_eq (by ring))

#print axioms polynomialGrid_coarse_error
#print axioms polynomial_range_quadrature
#print axioms polynomial_quadrature
end Waring.PolicyCompletionPolynomialQuadrature

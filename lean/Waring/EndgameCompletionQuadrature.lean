import Waring.EndgameCompletionDiscrete
import Waring.EndgameCompletionSingular

/-!
# Uniform monomial quadrature by dyadic refinement

The difference between a grid sum and its refinement is an alternating
monomial sum.  The proved discrete first-derivative estimate controls that
difference; a geometric telescope and the elementary coarse integral
approximation then give a uniform sum-versus-integral estimate.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Waring.EndgameCompletion
open QuadraticModulation

theorem sum_range_even_odd (f : ℕ → ℂ) (N : ℕ) :
    (∑ n∈Finset.range (2*N),f n)=∑ n∈Finset.range N,(f (2*n)+f (2*n+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]
      simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.add_zero,zero_add]

theorem e_neg_half : e (-(1/2 : ℝ))= -1 := by
  unfold e
  have hh : (((2*Real.pi*(-(1/2 : ℝ)) : ℝ) : ℂ)*Complex.I) =
      -((Real.pi : ℂ)*Complex.I) := by push_cast; ring
  rw [hh,Complex.exp_neg,Complex.exp_pi_mul_I]
  norm_num

def monomialGrid (k N M : ℕ) (β : ℝ) : ℂ :=
  (M : ℂ)⁻¹*∑ n∈Finset.range (M*N),e (β*((n : ℝ)/M)^k)

theorem monomialGrid_one (k N : ℕ) (β : ℝ) :
    monomialGrid k N 1 β=∑ n∈Finset.range N,e (β*(n : ℝ)^k) := by
  simp [monomialGrid]

theorem monomialGrid_doubling (k N M : ℕ) (hM : 0<M) (β : ℝ) :
    monomialGrid k N M β-monomialGrid k N (2*M) β =
      ((2*M : ℕ) : ℂ)⁻¹*∑ n∈Finset.range (2*M*N),
        e ((β/((2*M : ℕ) : ℝ)^k)*(n : ℝ)^k-(1/2 : ℝ)*n) := by
  have hM0 : (M : ℝ)≠0 := by exact_mod_cast hM.ne'
  have heven (n : ℕ) :
      e ((β/((2*M : ℕ) : ℝ)^k)*((2*n : ℕ) : ℝ)^k-(1/2 : ℝ)*(2*n : ℕ)) =
        e (β*((n : ℝ)/M)^k) := by
    have heq : (β/((2*M : ℕ) : ℝ)^k)*((2*n : ℕ) : ℝ)^k-(1/2 : ℝ)*(2*n : ℕ) =
        β*((n : ℝ)/M)^k+(-(n : ℤ) : ℤ) := by
      push_cast
      rw [div_pow,mul_pow,mul_pow]
      field_simp
      ring
    rw [heq,e_add_int]
  have hodd (n : ℕ) :
      e ((β/((2*M : ℕ) : ℝ)^k)*((2*n+1 : ℕ) : ℝ)^k-(1/2 : ℝ)*(2*n+1 : ℕ)) =
        -e (β*(((2*n+1 : ℕ) : ℝ)/(2*M : ℕ))^k) := by
    have heq : (β/((2*M : ℕ) : ℝ)^k)*((2*n+1 : ℕ) : ℝ)^k-(1/2 : ℝ)*(2*n+1 : ℕ) =
        (β*(((2*n+1 : ℕ) : ℝ)/(2*M : ℕ))^k-(1/2 : ℝ))+(-(n : ℤ) : ℤ) := by
      push_cast
      rw [div_pow]
      ring
    rw [heq,e_add_int,sub_eq_add_neg,e_add,e_neg_half,mul_neg_one]
  have hgridEven (n : ℕ) :
      e (β*(((2*n : ℕ) : ℝ)/(2*M : ℕ))^k)=e (β*((n : ℝ)/M)^k) := by
    congr 2
    push_cast
    field_simp
  unfold monomialGrid
  rw [show 2*M*N=2*(M*N) by ring,sum_range_even_odd,sum_range_even_odd]
  simp only [heven,hodd,hgridEven,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  push_cast
  have hMc : (M : ℂ)≠0 := by exact_mod_cast hM.ne'
  field_simp
  ring

theorem monomialGrid_doubling_bound (k N M : ℕ) (hk : 1≤k) (hM : 1≤M)
    (β : ℝ) (hβ : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤1/2) :
    ‖monomialGrid k N M β-monomialGrid k N (2*M) β‖ ≤ (1+Real.pi/4)/(M : ℝ) := by
  by_cases hN : N=0
  · subst N
    simp only [monomialGrid,Finset.sum_range_zero,mul_zero,sub_self,norm_zero]
    positivity
  have hN1 : 1≤N := by omega
  have hMpos : (0 : ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hM0 : (M : ℝ)≠0 := hMpos.ne'
  have hhalf : integerDistance (1/2 : ℝ)=1/2 := by
    rw [integerDistance,one_div,round_two_inv]
    norm_num
  have hscale : |β/((2*M : ℕ) : ℝ)^k| *(k : ℝ)*((2*M*N : ℕ) : ℝ)^(k-1) =
      (|β| *(k : ℝ)*(N : ℝ)^(k-1))/(2*M) := by
    rw [abs_div,abs_of_nonneg (by positivity : (0 : ℝ)≤((2*M : ℕ) : ℝ)^k)]
    push_cast
    rw [mul_pow,mul_pow,mul_pow,
      show (M : ℝ)^k=M^(k-1)*M by rw [← pow_succ,Nat.sub_add_cancel hk],
      show (2 : ℝ)^k=2^(k-1)*2 by rw [← pow_succ,Nat.sub_add_cancel hk]]
    field_simp
  have hsmall : |β/((2*M : ℕ) : ℝ)^k| *(k : ℝ)*((2*M*N : ℕ) : ℝ)^(k-1)≤
      integerDistance (1/2 : ℝ)/2 := by
    rw [hscale,hhalf]
    have hM1 : (1 : ℝ)≤M := by exact_mod_cast hM
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*M)).mpr
    nlinarith
  have hsum := norm_monomial_linear_sum_le k (2*M*N) (by nlinarith) (β/((2*M : ℕ) : ℝ)^k)
    (1/2) (by rw [hhalf]; norm_num) hsmall
  rw [monomialGrid_doubling k N M (by omega),norm_mul,norm_inv,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  rw [hhalf]
  push_cast
  field_simp

theorem sum_positive_eq_range_endpoints (f : ℕ → ℂ) (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,f n)=(∑ n∈Finset.range N,f n)+f N-f 0 := by
  rw [← Finset.Ico_succ_right_eq_Icc,Order.succ_eq_add_one,
    Finset.sum_Ico_eq_sub _ (by omega : 1≤N+1),Finset.sum_range_succ,Finset.sum_range_one]

theorem monomialIntegral_rescale_grid (k N M : ℕ) (hM : 0<M) (β : ℝ) :
    monomialIntegral k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)=
      (M : ℂ)*monomialIntegral k N β := by
  rw [monomialIntegral_scale k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k),monomialIntegral_scale k N β]
  have hM0 : (M : ℝ)≠0 := by exact_mod_cast hM.ne'
  have harg : (β/(M : ℝ)^k)*((M*N : ℕ) : ℝ)^k=β*(N : ℝ)^k := by
    push_cast
    rw [mul_pow]
    field_simp
  rw [harg]
  push_cast
  ring

theorem ordinaryWeyl_grid_eq (k N M : ℕ) (β : ℝ) :
    ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)=
      ∑ n∈Finset.Icc 1 (M*N),e (β*((n : ℝ)/M)^k) := by
  unfold ordinaryWeyl ordinaryNumbers
  rw [Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro n _
  rw [phase_eq_e,div_pow]
  congr 1
  ring

/-- A coarse O(1/M) grid-to-integral error.  Its constant may depend on N
and beta; it is used only to identify the limit of the dyadic grids. -/
theorem monomialGrid_coarse_error (k N M : ℕ) (hk : 1≤k) (hM : 0<M) (β : ℝ) :
    ‖monomialGrid k N M β-monomialIntegral k N β‖ ≤
      (5+6*Real.pi*|β| *(k : ℝ)*(N : ℝ)^k)/(M : ℝ) := by
  have hMpos : (0 : ℝ)<M := by exact_mod_cast hM
  have hM0 : (M : ℝ)≠0 := hMpos.ne'
  have hMc : (M : ℂ)≠0 := by exact_mod_cast hM.ne'
  have hS : completeMonomialSum k 0 1=1 := by simp [completeMonomialSum,e]
  have h := ordinary_rational_approximation k hk 0 (q := 1) (by norm_num)
    (P := ((M*N : ℕ) : ℝ)) (Nat.cast_nonneg _) (β/(M : ℝ)^k)
  simp only [Int.cast_zero,Nat.cast_one,zero_add,hS,div_one,one_mul,mul_one] at h
  rw [monomialIntegral_rescale_grid k N M hM β] at h
  have hrhs : 3*(1+2*Real.pi*|β/(M : ℝ)^k| *(k : ℝ)*((M*N : ℕ) : ℝ)^k)=
      3*(1+2*Real.pi*|β| *(k : ℝ)*(N : ℝ)^k) := by
    rw [abs_div,abs_of_nonneg (pow_nonneg hMpos.le _)]
    push_cast
    rw [mul_pow]
    field_simp
  rw [hrhs] at h
  have hright : ‖(M : ℂ)⁻¹*ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)-
      monomialIntegral k N β‖ ≤ (3*(1+2*Real.pi*|β| *(k : ℝ)*(N : ℝ)^k))/(M : ℝ) := by
    have hid : (M : ℂ)⁻¹*ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)-
        monomialIntegral k N β = (M : ℂ)⁻¹*(ordinaryWeyl k ((M*N : ℕ) : ℝ)
          (β/(M : ℝ)^k)-(M : ℂ)*monomialIntegral k N β) := by field_simp
    rw [hid,norm_mul,norm_inv,Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)
  have hend : ‖monomialGrid k N M β-
      (M : ℂ)⁻¹*ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)‖ ≤ 2/(M : ℝ) := by
    rw [ordinaryWeyl_grid_eq,sum_positive_eq_range_endpoints]
    have hid : monomialGrid k N M β-(M : ℂ)⁻¹*
        ((∑ n∈Finset.range (M*N),e (β*((n : ℝ)/M)^k))+
          e (β*(((M*N : ℕ) : ℝ)/M)^k)-e (β*((0 : ℝ)/M)^k)) =
        (M : ℂ)⁻¹*(e (β*((0 : ℝ)/M)^k)-e (β*(((M*N : ℕ) : ℝ)/M)^k)) := by
      unfold monomialGrid
      ring
    simp only [Nat.cast_zero]
    rw [hid,norm_mul,norm_inv,Complex.norm_natCast]
    apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans_eq
    rw [norm_e,norm_e]
    ring
  calc
    _ ≤ ‖monomialGrid k N M β-(M : ℂ)⁻¹*ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)‖+
        ‖(M : ℂ)⁻¹*ordinaryWeyl k ((M*N : ℕ) : ℝ) (β/(M : ℝ)^k)-monomialIntegral k N β‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2/(M : ℝ)+(3*(1+2*Real.pi*|β| *(k : ℝ)*(N : ℝ)^k))/(M : ℝ) := add_le_add hend hright
    _ = _ := by ring

theorem monomialGrid_dyadic_error (k N J : ℕ) (hk : 1≤k) (β : ℝ)
    (hβ : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤1/2) :
    ‖monomialGrid k N 1 β-monomialGrid k N (2^J) β‖ ≤ 2+Real.pi/2 := by
  let u : ℕ → ℂ := fun j=>monomialGrid k N (2^j) β
  have hstep (j : ℕ) : ‖u (j+1)-u j‖≤(1+Real.pi/4)/((2^j : ℕ) : ℝ) := by
    dsimp [u]
    rw [norm_sub_rev,show 2^(j+1)=2*2^j by rw [pow_succ,Nat.mul_comm]]
    exact monomialGrid_doubling_bound k N (2^j) hk (Nat.one_le_pow _ _ (by norm_num)) β hβ
  have hgeom : (∑ j∈Finset.range J,((1/2 : ℝ)^j))≤2 := by
    have h := geom_sum_mul (1/2 : ℝ) J
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ)≤1/2) J]
  calc
    _ = ‖∑ j∈Finset.range J,(u (j+1)-u j)‖ := by
      rw [Finset.sum_range_sub,norm_sub_rev]
      rfl
    _ ≤ ∑ j∈Finset.range J,‖u (j+1)-u j‖ := norm_sum_le _ _
    _ ≤ ∑ j∈Finset.range J,(1+Real.pi/4)/((2^j : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun j _=>hstep j)
    _ = (1+Real.pi/4)*∑ j∈Finset.range J,(1/2 : ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv,← inv_pow,one_div]
    _ ≤ (1+Real.pi/4)*2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- Uniform quadrature at an integer endpoint. This closes the zero
Fourier frequency without importing an external Poisson or Euler estimate. -/
theorem monomial_range_quadrature (k N : ℕ) (hk : 1≤k) (β : ℝ)
    (hβ : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤1/2) :
    ‖(∑ n∈Finset.range N,e (β*(n : ℝ)^k))-monomialIntegral k N β‖ ≤ 2+Real.pi/2 := by
  let B : ℝ := 5+6*Real.pi*|β| *(k : ℝ)*(N : ℝ)^k
  have hb (J : ℕ) :
      ‖(∑ n∈Finset.range N,e (β*(n : ℝ)^k))-monomialIntegral k N β‖ ≤
        (2+Real.pi/2)+B/((2^J : ℕ) : ℝ) := by
    rw [← monomialGrid_one]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (monomialGrid k N (2^J) β) _).trans
      (add_le_add (monomialGrid_dyadic_error k N J hk β hβ)
        (monomialGrid_coarse_error k N (2^J) hk (pow_pos (by norm_num) _) β))
  have ht : Tendsto (fun J : ℕ=>(2+Real.pi/2)+B/((2^J : ℕ) : ℝ)) atTop
      (𝓝 (2+Real.pi/2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      ((tendsto_const_div_atTop_nhds_zero_nat B).comp
        (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<2)))
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hb)

theorem monomial_positive_quadrature (k N : ℕ) (hk : 1≤k) (β : ℝ)
    (hβ : |β| *(k : ℝ)*(N : ℝ)^(k-1)≤1/2) :
    ‖(∑ n∈Finset.Icc 1 N,e (β*(n : ℝ)^k))-monomialIntegral k N β‖ ≤ 4+Real.pi/2 := by
  have hmain := monomial_range_quadrature k N hk β hβ
  rw [sum_positive_eq_range_endpoints]
  have hid : (∑ n∈Finset.range N,e (β*(n : ℝ)^k))+e (β*(N : ℝ)^k)-e (β*(0 : ℕ)^k)-
      monomialIntegral k N β =
      ((∑ n∈Finset.range N,e (β*(n : ℝ)^k))-monomialIntegral k N β)+
        (e (β*(N : ℝ)^k)-e (β*(0 : ℕ)^k)) := by ring
  rw [hid]
  apply (norm_add_le _ _).trans
  have hend : ‖e (β*(N : ℝ)^k)-e (β*(0 : ℕ)^k)‖≤2 := by
    simpa only [norm_e,one_add_one_eq_two] using norm_sub_le
      (e (β*(N : ℝ)^k)) (e (β*(0 : ℕ)^k))
  exact (add_le_add hmain hend).trans_eq (by ring)

/-- Uniform zero-frequency quadrature for the actual positive-integer sum
and a real cutoff. The final fractional interval costs at most one. -/
theorem ordinary_monomial_quadrature (k : ℕ) (hk : 1≤k) {P β : ℝ}
    (hP : 0≤P) (hβ : |β| *(k : ℝ)*P^(k-1)≤1/2) :
    ‖(∑ n∈ordinaryNumbers P,e (β*(n : ℝ)^k))-monomialIntegral k P β‖ ≤ 5+Real.pi/2 := by
  have hN : (⌊P⌋₊ : ℝ)≤P := Nat.floor_le hP
  have hsmall : |β| *(k : ℝ)*(⌊P⌋₊ : ℝ)^(k-1)≤1/2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _) (by positivity)).trans hβ
  have hmain := monomial_positive_quadrature k ⌊P⌋₊ hk β hsmall
  have hfc : Continuous (fun t : ℝ=>e (β*t^k)) := by unfold e; fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hfc.intervalIntegrable 0 (⌊P⌋₊ : ℝ)) (hfc.intervalIntegrable (⌊P⌋₊ : ℝ) P)
  change monomialIntegral k (⌊P⌋₊ : ℝ) β+
    (∫ t in (⌊P⌋₊ : ℝ)..P,e (β*t^k))=monomialIntegral k P β at hadd
  have htail : ‖monomialIntegral k (⌊P⌋₊ : ℝ) β-monomialIntegral k P β‖≤1 := by
    rw [norm_sub_rev,← hadd,add_sub_cancel_left]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      (a := (⌊P⌋₊ : ℝ)) (b := P) (fun t _=>(norm_e (β*t^k)).le)
    rw [one_mul,abs_of_nonneg (sub_nonneg.mpr hN)] at hh
    exact hh.trans (by have := Nat.lt_floor_add_one P; linarith)
  apply (norm_sub_le_norm_sub_add_norm_sub _ (monomialIntegral k (⌊P⌋₊ : ℝ) β) _).trans
  change ‖(∑ n∈Finset.Icc 1 ⌊P⌋₊,e (β*(n : ℝ)^k))-monomialIntegral k (⌊P⌋₊ : ℝ) β‖+
    ‖monomialIntegral k (⌊P⌋₊ : ℝ) β-monomialIntegral k P β‖≤_
  linarith

#print axioms monomialGrid_doubling_bound
#print axioms monomialGrid_coarse_error
#print axioms monomial_range_quadrature
#print axioms ordinary_monomial_quadrature

end Waring.EndgameCompletion

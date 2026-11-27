import Waring.EndgameCompletionSingularEuler
/-! # Uniform positivity of the actual mixed product singular series -/

noncomputable section
open scoped BigOperators
open Filter Topology
namespace Waring.EndgameCompletion

theorem uniform_positive_complex_product {ι ν : Type*}
    (a : ν→ι→ℂ) (z : ν→ℂ) (c b : ι→ℝ)
    (hc : ∀ i,0<c i) (hb : Summable b) (hb0 : ∀ i,0≤b i)
    (ha : ∀ n i,c i≤(a n i).re) (hai : ∀ n i,(a n i).im=0)
    (hdev : ∀ n i,‖a n i-1‖≤b i) (hprod : ∀ n,HasProd (a n) (z n)) :
    ∃ C : ℝ,0<C ∧ ∀ n,C≤(z n).re := by
  classical
  have hsmall : ∀ᶠ i in cofinite,b i<(1/2 : ℝ) :=
    hb.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  let S : Finset ι := (eventually_cofinite.mp hsmall).toFinset
  have hS (i : ι) (hi : i∉S) : b i<1/2 := by
    simpa only [S,Set.Finite.mem_toFinset,Set.mem_setOf_eq,not_not] using hi
  let d : ι→ℝ := fun i=>if i∈S then min (c i) 1 else 1-b i
  have hdpos (i : ι) : 0<d i := by
    dsimp [d]
    split_ifs with hi
    · exact lt_min (hc i) zero_lt_one
    · have hh := hS i hi
      linarith
  have hdle (n : ν) (i : ι) : d i≤(a n i).re := by
    dsimp [d]
    split_ifs with hi
    · exact (min_le_left _ _).trans (ha n i)
    · have hh := (Complex.re_le_norm (1-a n i)).trans (by
        simpa only [norm_sub_rev] using hdev n i)
      simp only [Complex.sub_re,Complex.one_re] at hh
      linarith
  have hdnorm : Summable (fun i=>‖d i-1‖) := by
    apply hb.congr_cofinite
    filter_upwards [S.eventually_cofinite_notMem] with i hi
    simp only [d,if_neg hi,sub_sub_cancel_left,norm_neg,Real.norm_eq_abs,
      abs_of_nonneg (hb0 i)]
  have hdmul : Multipliable d := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hdnorm
  have hdne : (∏' i,d i)≠0 := by
    have hh := tprod_one_add_ne_zero_of_summable
      (fun i=>by simpa only [add_sub_cancel] using (hdpos i).ne') hdnorm
    simpa only [add_sub_cancel] using hh
  have hdnneg : (0 : ℝ)≤∏' i,d i :=
    ge_of_tendsto' hdmul.hasProd (fun T=>Finset.prod_nonneg (fun i _=>(hdpos i).le))
  refine ⟨∏' i,d i,lt_of_le_of_ne hdnneg (Ne.symm hdne),?_⟩
  intro n
  have hfinite (T : Finset ι) : (∏ i∈T,d i)≤(∏ i∈T,a n i).re := by
    have he : (∏ i∈T,a n i)=((∏ i∈T,(a n i).re : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact Complex.ext rfl (by simpa using hai n i)
    rw [he,Complex.ofReal_re]
    exact Finset.prod_le_prod (fun i _=>(hdpos i).le) (fun i _=>hdle n i)
  exact le_of_tendsto_of_tendsto' hdmul.hasProd
    ((Complex.continuous_re.tendsto _).comp (hprod n)) hfinite

theorem degree8_productSingularSeries_uniform_positive (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℤ,C≤(productSingularSeries 8 8 30 (L+1) n).re := by
  obtain ⟨b,hb,hb0,hdev⟩ := degree8_localFactor_tail_majorant L
  refine uniform_positive_complex_product
    (fun n (p : Nat.Primes)=>productLocalFactor 8 8 30 (L+1) n p)
    (fun n=>productSingularSeries 8 8 30 (L+1) n)
    (fun p : Nat.Primes=>primeDensityLower p 38 (L*30) (LocalSolubility.localDepth8 p))
    b (fun p=>primeDensityLower_pos p.prop.pos _ _ _) hb hb0 ?_ ?_ hdev ?_
  · intro n p
    letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    exact degree8_productLocalFactor_lower p.prop L n
  · intro n p
    letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    exact productLocalFactor_im_eq_zero p.prop 8 8 30 L n
      (degree8_productSingularCoefficient_summable L n)
  · intro n
    exact productSingularSeries_hasProd 8 8 30 (L+1) n
      (degree8_productSingularCoefficient_summable L n)

theorem degree9_productSingularSeries_uniform_positive (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℤ,C≤(productSingularSeries 9 11 35 (L+1) n).re := by
  obtain ⟨b,hb,hb0,hdev⟩ := degree9_localFactor_tail_majorant L
  refine uniform_positive_complex_product
    (fun n (p : Nat.Primes)=>productLocalFactor 9 11 35 (L+1) n p)
    (fun n=>productSingularSeries 9 11 35 (L+1) n)
    (fun p : Nat.Primes=>primeDensityLower p 46 (L*35) (LocalSolubility.localDepth9 p))
    b (fun p=>primeDensityLower_pos p.prop.pos _ _ _) hb hb0 ?_ ?_ hdev ?_
  · intro n p
    letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    exact degree9_productLocalFactor_lower p.prop L n
  · intro n p
    letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    exact productLocalFactor_im_eq_zero p.prop 9 11 35 L n
      (degree9_productSingularCoefficient_summable L n)
  · intro n
    exact productSingularSeries_hasProd 9 11 35 (L+1) n
      (degree9_productSingularCoefficient_summable L n)

#print axioms degree8_productSingularSeries_uniform_positive
#print axioms degree9_productSingularSeries_uniform_positive


theorem complex_hasProd_im_eq_zero {ι : Type*} {a : ι→ℂ} {z : ℂ}
    (hprod : HasProd a z) (ha : ∀ i,(a i).im=0) : z.im=0 := by
  classical
  have hfinite (T : Finset ι) : (∏ i∈T,a i).im=0 := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
        rw [Finset.prod_insert hi,Complex.mul_im,ha,ih]
        ring
  have ht : Tendsto (fun _ : Finset ι=>(0 : ℝ)) atTop (𝓝 z.im) := by
    have hh := (Complex.continuous_im.tendsto _).comp hprod
    change Tendsto (fun T : Finset ι=>(∏ i∈T,a i).im) atTop (𝓝 z.im) at hh
    simpa only [hfinite] using hh
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem productSingularSeries_im_eq_zero (k u v L : ℕ) (n : ℤ)
    (hsum : Summable (fun q=>‖productSingularCoefficient k u v (L+1) n q‖)) :
    (productSingularSeries k u v (L+1) n).im=0 := by
  apply complex_hasProd_im_eq_zero (productSingularSeries_hasProd k u v (L+1) n hsum)
  intro p
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact productLocalFactor_im_eq_zero p.prop k u v L n hsum

#print axioms productSingularSeries_im_eq_zero

end Waring.EndgameCompletion


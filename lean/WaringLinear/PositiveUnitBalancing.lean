import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Tactic

/-! Uniform balancing by even powers of units at all infinite places.
The coordinates are weighted by the local real dimensions, so their
sum is the logarithm of the absolute norm. -/
noncomputable section
open NumberField InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators
namespace WaringLinear.PositiveUnitBalancing

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
private theorem log_cover :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖logEmbedding K (Additive.ofMul u) - y‖ ≤ C := by
  classical
  let b := (basisUnitLattice K).ofZLatticeBasis ℝ
  refine ⟨∑ i, ‖b i‖, by positivity, ?_⟩
  intro y
  obtain ⟨⟨e, he⟩, h, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b (-y)
  have mem : e ∈ unitLattice K := by
    rwa [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]
  obtain ⟨u, _, rfl⟩ := mem
  refine ⟨u.toMul, ?_⟩
  change logEmbedding K u + -y ∈ ZSpan.fundamentalDomain b at h
  have hbound := ZSpan.norm_fract_le b (logEmbedding K u - y)
  rwa [ZSpan.fract_eq_self.mpr (by simpa [sub_eq_add_neg] using h)] at hbound

/-- A fixed even power of a unit approximates every prescribed zero-sum
logarithmic vector to bounded error in *all* weighted coordinates. -/
theorem weighted_log_cover (k : ℕ) (hk : 0<k) :
    ∃ C : ℝ, ∀ y : InfinitePlace K → ℝ, (∑w, y w)=0 →
      ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
        |(mult w : ℝ)*Real.log (w ((u^(2*k) : (𝓞 K)ˣ) : K)) - y w| ≤ C := by
  classical
  obtain ⟨B,hB,hcover⟩ := log_cover K
  let d : ℝ := 2*(k:ℝ)
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨(Fintype.card (InfinitePlace K)+1 : ℝ)*(d*B), ?_⟩
  intro y hy
  let z : logSpace K := fun w => y w / d
  obtain ⟨u,hu⟩ := hcover z
  let s : InfinitePlace K → ℝ := fun w =>
    (mult w : ℝ)*Real.log (w ((u^(2*k) : (𝓞 K)ˣ) : K)) - y w
  have hrest (w : {w : InfinitePlace K // w ≠ w₀}) : |s w| ≤ d*B := by
    have hb : |(mult w.val : ℝ) * Real.log (w.val (u:K)) - y w/d| ≤ B := by
      exact (norm_le_pi_norm (logEmbedding K (Additive.ofMul u) - z) w).trans hu
    have hlogs : s w = d * ((mult w.val : ℝ) * Real.log (w.val (u:K)) - y w/d) := by
      simp only [s, Units.val_pow_eq_pow_val, map_pow, Real.log_pow]
      dsimp [d]
      push_cast
      field_simp
    rw [hlogs, abs_mul, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_left hb hd.le
  have hsum : (∑w, s w)=0 := by
    simp only [s,Finset.sum_sub_distrib, sum_mult_mul_log,hy,sub_self]
  refine ⟨u,?_⟩
  intro w
  change |s w| ≤ _
  by_cases hw : w=w₀
  · subst w
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
    have hrestsum := Finset.abs_sum_le_sum_abs (fun j : {w : InfinitePlace K // w ≠ w₀} => s j) Finset.univ
    have hbound : |∑j : {w : InfinitePlace K // w ≠ w₀}, s j| ≤
        Fintype.card {w : InfinitePlace K // w≠w₀} * (d*B) :=
      hrestsum.trans (calc
        _ ≤ ∑ _j : {w : InfinitePlace K // w≠w₀}, d*B := Finset.sum_le_sum (fun i _ => hrest i)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])
    rw [show s w₀ = -(∑j : {w : InfinitePlace K // w ≠ w₀}, s j) by linarith, abs_neg]
    refine hbound.trans ?_
    gcongr
    exact_mod_cast (Fintype.card_subtype_le (fun w : InfinitePlace K => w ≠ w₀)).trans (Nat.le_add_right _ _)
  · refine (hrest ⟨w,hw⟩).trans ?_
    have hnon : 0 ≤ d*B := mul_nonneg hd.le hB
    nlinarith [(Fintype.card (InfinitePlace K)).cast_nonneg (α:=ℝ)]

omit [NumberField K] in
/-- The multiplying unit is a square at every real embedding. -/
theorem positive_at_real (u : (𝓞 K)ˣ) (k : ℕ) (φ : K →+* ℝ) :
    0 < φ ((u^(2*k) : (𝓞 K)ˣ) : K) := by
  simp only [Units.val_pow_eq_pow_val, map_pow, mul_comm 2 k, pow_mul]
  exact sq_pos_of_ne_zero (pow_ne_zero k (by
    apply (map_ne_zero φ).mpr
    exact (u.isUnit.map (algebraMap (𝓞 K) K)).ne_zero))

/-- Multiplicative comparison with any target radii of the same weighted
product. This formulation can be applied to the absolute embeddings of
an element in a prescribed narrow ideal class, preserving its real signs. -/
theorem balance_radii (k : ℕ) (hk : 0<k) :
    ∃ D : ℝ, 0 < D ∧ ∀ r t : InfinitePlace K → ℝ,
      (∀ w, 0<r w) → (∀ w, 0<t w) →
      (∑ w, (mult w : ℝ)*Real.log (r w)) = (∑ w, (mult w : ℝ)*Real.log (t w)) →
      ∃ u : (𝓞 K)ˣ, ∀ w,
        t w / D ≤ r w * w ((u^(2*k) : (𝓞 K)ˣ) : K) ∧
        r w * w ((u^(2*k) : (𝓞 K)ˣ) : K) ≤ D * t w := by
  classical
  obtain ⟨C,hC⟩ := weighted_log_cover K k hk
  refine ⟨Real.exp C, Real.exp_pos _, ?_⟩
  intro r t hr ht heq
  let y := fun w : InfinitePlace K => (mult w : ℝ)*(Real.log (t w) - Real.log (r w))
  have hy : (∑ w, y w)=0 := by simp only [y,mul_sub,Finset.sum_sub_distrib,heq,sub_self]
  obtain ⟨u,hu⟩ := hC y hy
  refine ⟨u,fun w => ?_⟩
  let a := w ((u^(2*k) : (𝓞 K)ˣ) : K)
  have ha : 0<a := Units.pos_at_place _ _
  have hw : (1:ℝ) ≤ mult w := by
    unfold mult
    split_ifs <;> norm_num
  have hlog : |Real.log (r w*a/t w)| ≤ C := by
    calc
      _ ≤ (mult w:ℝ)*|Real.log (r w*a/t w)| := le_mul_of_one_le_left (abs_nonneg _) hw
      _ = |(mult w:ℝ)*Real.log a-y w| := by
        rw [←abs_of_nonneg (by positivity : 0≤(mult w:ℝ)), ←abs_mul,
          Real.log_div (mul_pos (hr w) ha).ne' (ht w).ne',
          Real.log_mul (hr w).ne' ha.ne']
        congr 1
        dsimp [y]
        rw [abs_of_nonneg (by positivity : 0≤(mult w:ℝ))]
        ring
      _ ≤ C := hu w
  obtain ⟨hlo,hhi⟩ := abs_le.mp hlog
  have hpos := div_pos (mul_pos (hr w) ha) (ht w)
  have hup := Real.exp_le_exp.mpr hhi
  have hdn := Real.exp_le_exp.mpr hlo
  rw [Real.exp_log hpos] at hup hdn
  rw [Real.exp_neg] at hdn
  constructor
  · have hl := (le_div_iff₀ (ht w)).mp hdn
    calc
      _ = (Real.exp C)⁻¹ * t w := by ring
      _ ≤ _ := hl
  · exact (div_le_iff₀ (ht w)).mp hup

/-- After scaling by an even power of an actual integral unit, every
archimedean absolute value of a nonzero field element is comparable
to the geometric mean of its conjugates. -/
theorem balance_element (k : ℕ) (hk : 0<k) :
    ∃ D : ℝ, 0<D ∧ ∀ x : K, x≠0 →
      ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
        let m := |(Algebra.norm ℚ x:ℝ)| ^ (1/(Module.finrank ℚ K:ℝ))
        m/D ≤ w (x * ((u^(2*k) : (𝓞 K)ˣ) : K)) ∧
          w (x * ((u^(2*k) : (𝓞 K)ˣ) : K)) ≤ D*m := by
  classical
  obtain ⟨D,hD,hbalance⟩ := balance_radii K k hk
  refine ⟨D,hD,?_⟩
  intro x hx
  let m := |(Algebra.norm ℚ x:ℝ)| ^ (1/(Module.finrank ℚ K:ℝ))
  have hN : 0 < |(Algebra.norm ℚ x:ℝ)| := abs_pos.mpr (by
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr hx : Algebra.norm ℚ x ≠ 0))
  have hm : 0<m := Real.rpow_pos_of_pos hN _
  have hlogs : ∑ w : InfinitePlace K, (mult w:ℝ)*Real.log (w x) =
      ∑ w : InfinitePlace K, (mult w:ℝ)*Real.log m := by
    have hdegree : (∑ w : InfinitePlace K, (mult w : ℝ)) = (Module.finrank ℚ K:ℝ) := by
      exact_mod_cast (sum_mult_eq (K:=K))
    have hn : (0:ℝ)<(Module.finrank ℚ K:ℝ) := by
      exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
    have hproduct := Real.log_prod Finset.univ (fun w : InfinitePlace K => w x ^ mult w)
      (fun w _ => pow_ne_zero _ (InfinitePlace.pos_iff.mpr hx).ne')
    simp only [prod_eq_abs_norm,Real.log_pow] at hproduct
    rw [← Finset.sum_mul, hdegree, ← hproduct]
    dsimp [m]
    rw [Real.log_rpow hN,Rat.cast_abs]
    field_simp
  obtain ⟨u,hu⟩ := hbalance (fun w => w x) (fun _ => m)
      (fun _ => InfinitePlace.pos_iff.mpr hx) (fun _ => hm) hlogs
  exact ⟨u,fun w => by simpa only [map_mul] using hu w⟩

#print axioms balance_element
#print axioms weighted_log_cover
#print axioms balance_radii
#print axioms positive_at_real
end WaringLinear.PositiveUnitBalancing

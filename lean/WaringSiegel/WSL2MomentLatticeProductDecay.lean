import WaringSiegel.WSL2MomentLatticeDecay

/-!
# Product decay and absolute convergence on fractional-ideal cosets

This is the literal anisotropic product kernel occurring in the ideal Poisson
tail.  It is dominated by the rescaled radial kernel and inherits its proved
uniform, explicit bound.  No ideal Poisson formula is assumed.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped BigOperators NumberField nonZeroDivisors Classical

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

def latticeProductDecay (R : InfinitePlace K→ℝ) (c : mixedSpace K) (z : K) : ℝ :=
  ∏v, 1/(1+normAtPlace v (mixedEmbedding K z-c)/R v)^(finrank ℚ K+2)

theorem latticeProductDecay_nonneg (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v)
    (c : mixedSpace K) (z : K) : 0≤latticeProductDecay R c z := by
  unfold latticeProductDecay
  apply Finset.prod_nonneg
  intro v hv
  have hv0 := normAtPlace_nonneg v (mixedEmbedding K z-c)
  exact div_nonneg zero_le_one (pow_nonneg
    (add_nonneg zero_le_one (div_nonneg hv0 (hR v).le)) _)

/-- Domination for an arbitrary archimedean vector, also usable in shifted
close-pair kernels. -/
theorem mixed_product_decay_le_radial (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v)
    (x : mixedSpace K) :
    (∏v, 1/(1+normAtPlace v x/R v)^(finrank ℚ K+2)) ≤
      1/(1+‖rescaleMixed R x‖)^(finrank ℚ K+2) := by
  let b : InfinitePlace K→ℝ := fun v=>1+normAtPlace v x/R v
  have hb : ∀v, 1≤b v := by
    intro v
    have hv0 : 0≤normAtPlace v x/R v := div_nonneg (normAtPlace_nonneg v x) (hR v).le
    dsimp [b]
    linarith
  have hmax : ‖rescaleMixed R x‖ ≤ (∏v, b v)-1 := by
    apply (mixed_norm_le_iff _ _).mpr
    intro v
    rw [normAtPlace_rescaleMixed R hR]
    have hv : b v ≤ ∏w, b w := by
      have herase : 1≤∏w∈(Finset.univ.erase v), b w := by
        calc
          _ = ∏_w∈(Finset.univ.erase v), (1:ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod (fun _ _=>zero_le_one) (fun w _=>hb w)
      calc
        _ = b v*1 := by ring
        _ ≤ b v*(∏w∈(Finset.univ.erase v), b w) :=
          mul_le_mul_of_nonneg_left herase (zero_le_one.trans (hb v))
        _ = _ := Finset.mul_prod_erase Finset.univ b (Finset.mem_univ v)
    change 1+normAtPlace v x/R v ≤ ∏w, b w at hv
    linarith
  have hbase : 1+‖rescaleMixed R x‖ ≤ ∏v, b v := by linarith
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow]
  apply one_div_le_one_div_of_le (pow_pos (by positivity) _)
  exact pow_le_pow_left₀ (by positivity) hbase _

theorem latticeProductDecay_le_radial (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v)
    (c : mixedSpace K) (z : K) : latticeProductDecay R c z≤latticeRadialDecay R c z :=
  mixed_product_decay_le_radial R hR (mixedEmbedding K z-c)

theorem fractionalIdeal_product_decay_finite_sum
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0) (S : Finset K) (a : K)
    (c : mixedSpace K) (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v)
    (hmem : ∀z∈S, z-a∈I) :
    (∑z∈S, latticeProductDecay R c z) ≤
      2*(3:ℝ)^(finrank ℚ K)*(1+(∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)) :=
  (Finset.sum_le_sum (fun z _=>latticeProductDecay_le_radial R hR c z)).trans
    (fractionalIdeal_radial_decay_finite_sum I hI S a c R hR hmem)

/-- The full product-decay series on an actual ideal coset converges
absolutely and satisfies the uniform anisotropic lattice-tail estimate. -/
theorem fractionalIdeal_product_decay_summable
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0) (a : K)
    (c : mixedSpace K) (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v) :
    Summable (fun z : {z : K // z-a∈I}=>latticeProductDecay R c (z:K)) ∧
      (∑'z : {z : K // z-a∈I}, latticeProductDecay R c (z:K)) ≤
        2*(3:ℝ)^(finrank ℚ K)*(1+(∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)) := by
  obtain ⟨hsrad,hbound⟩ := fractionalIdeal_radial_decay_summable I hI a c R hR
  have hs : Summable (fun z : {z : K // z-a∈I}=>latticeProductDecay R c (z:K)) :=
    Summable.of_nonneg_of_le (fun z=>latticeProductDecay_nonneg R hR c z)
      (fun z=>latticeProductDecay_le_radial R hR c z) hsrad
  exact ⟨hs, (hs.tsum_le_tsum
    (fun z : {z : K // z-a∈I}=>latticeProductDecay_le_radial R hR c (z:K)) hsrad).trans hbound⟩

end WaringSiegel.WSL2

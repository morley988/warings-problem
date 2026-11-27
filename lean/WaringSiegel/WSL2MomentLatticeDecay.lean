import WaringSiegel.WSL2AnisotropicPacking
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Convergent anisotropic lattice tails for actual fractional ideals

Integer annuli and the proved ideal packing estimate yield an absolutely
convergent decay sum.  The constant is uniform in the ideal, its coset, the
archimedean center, and all ratios of positive place radii.  This is the
geometric lattice-tail input used after ideal Poisson summation; no Poisson or
oscillatory-integral estimate is assumed here.
-/

noncomputable section
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped BigOperators NumberField nonZeroDivisors Classical

namespace WaringSiegel.WSL2

theorem inv_square_le_telescoping (n : ℕ) :
    1/((n:ℝ)+1)^2 ≤ 2/((n:ℝ)+1)-2/((n:ℝ)+2) := by
  have h1 : 0<(n:ℝ)+1 := by positivity
  have h2 : 0<(n:ℝ)+2 := by positivity
  calc
    _ ≤ 2/(((n:ℝ)+1)*((n:ℝ)+2)) := by
      apply (div_le_div_iff₀ (pow_pos h1 2) (mul_pos h1 h2)).mpr
      have hn : (0:ℝ)≤n := by positivity
      nlinarith
    _ = _ := by field_simp; ring

theorem sum_inv_nat_add_one_sq_le_two (N : ℕ) :
    (∑n∈Finset.range N, 1/((n:ℝ)+1)^2) ≤ 2 := by
  have hpartial (n : ℕ) : (∑j∈Finset.range n, 1/((j:ℝ)+1)^2) ≤ 2-2/((n:ℝ)+1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have ht := inv_square_le_telescoping n
      push_cast
      rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring]
      linarith
  exact (hpartial N).trans (by
    have hnonneg : 0≤2/((N:ℝ)+1) := by positivity
    linarith)

theorem finite_annular_decay_bound {α : Type*} (S : Finset α) (r : α→ℝ)
    (hr : ∀x∈S, 0≤r x) (d : ℕ) (B : ℝ) (hB : 0≤B)
    (hcount : ∀n : ℕ, ((S.filter (fun x=>⌊r x⌋₊=n)).card:ℝ) ≤ B*((n:ℝ)+1)^d) :
    (∑x∈S, 1/(1+r x)^(d+2)) ≤ 2*B := by
  let N : ℕ := S.sup (fun x=>⌊r x⌋₊)+1
  have hmaps : ∀x∈S, ⌊r x⌋₊∈Finset.range N := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=fun x=>⌊r x⌋₊) hx))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun x=>1/(1+r x)^(d+2))
  rw [← hfiber]
  have hterm (n : ℕ) :
      (∑x∈S.filter (fun x=>⌊r x⌋₊=n), 1/(1+r x)^(d+2)) ≤ B*(1/((n:ℝ)+1)^2) := by
    have ht : 0<(n:ℝ)+1 := by positivity
    calc
      _ ≤ ∑_x∈S.filter (fun x=>⌊r x⌋₊=n), 1/((n:ℝ)+1)^(d+2) := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hx,hfloor⟩ := Finset.mem_filter.mp hx
        have hn : (n:ℝ)≤r x := by simpa only [hfloor] using Nat.floor_le (hr x hx)
        exact one_div_le_one_div_of_le (pow_pos ht _) (pow_le_pow_left₀ ht.le (by linarith) _)
      _ = ((S.filter (fun x=>⌊r x⌋₊=n)).card:ℝ) * (1/((n:ℝ)+1)^(d+2)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (B*((n:ℝ)+1)^d) * (1/((n:ℝ)+1)^(d+2)) :=
        mul_le_mul_of_nonneg_right (hcount n) (by positivity)
      _ = _ := by rw [pow_add]; field_simp
  calc
    _ ≤ ∑n∈Finset.range N, B*(1/((n:ℝ)+1)^2) := Finset.sum_le_sum (fun n _=>hterm n)
    _ = B*(∑n∈Finset.range N, 1/((n:ℝ)+1)^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*2 := mul_le_mul_of_nonneg_left (sum_inv_nat_add_one_sq_le_two N) hB
    _ = _ := by ring

variable {K : Type*} [Field K] [NumberField K]

def anisotropicRadius (R : InfinitePlace K→ℝ) (c : mixedSpace K) (z : K) : ℝ :=
  ‖rescaleMixed R (mixedEmbedding K z-c)‖

def latticeRadialDecay (R : InfinitePlace K→ℝ) (c : mixedSpace K) (z : K) : ℝ :=
  1/(1+anisotropicRadius R c z)^(finrank ℚ K+2)

/-- Finite partial sums with an explicit constant, uniform in every geometric
parameter and in the actual fractional ideal. -/
theorem fractionalIdeal_radial_decay_finite_sum
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0) (S : Finset K) (a : K)
    (c : mixedSpace K) (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v)
    (hmem : ∀z∈S, z-a∈I) :
    (∑z∈S, latticeRadialDecay R c z) ≤
      2*(3:ℝ)^(finrank ℚ K)*(1+(∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)) := by
  let d : ℕ := finrank ℚ K
  let V : ℝ := (∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)
  have hV : 0≤V := by
    dsimp [V]
    exact div_nonneg (Finset.prod_nonneg (fun v _=>pow_nonneg (hR v).le _))
      (fractionalIdeal_absNorm_pos I hI).le
  have h := finite_annular_decay_bound S (anisotropicRadius R c)
    (fun _ _=>norm_nonneg _) d ((3:ℝ)^d*(1+V)) (by positivity) (by
      intro n
      let T := S.filter (fun z=>⌊anisotropicRadius R c z⌋₊=n)
      have ht : 0<(n:ℝ)+1 := by positivity
      have hb (z : K) (hz : z∈T) (v : InfinitePlace K) :
          normAtPlace v (mixedEmbedding K z-c) ≤ ((n:ℝ)+1)*R v := by
        have hfloor := (Finset.mem_filter.mp hz).2
        have hr : anisotropicRadius R c z ≤ (n:ℝ)+1 := by
          have hn := Nat.lt_floor_add_one (anisotropicRadius R c z)
          rw [hfloor] at hn
          exact hn.le
        have hv := normAtPlace_le_mixed_norm (rescaleMixed R (mixedEmbedding K z-c)) v
        rw [normAtPlace_rescaleMixed R hR] at hv
        exact (div_le_iff₀ (hR v)).mp (hv.trans hr)
      have hpack := fractionalIdeal_anisotropic_packing I hI T a c
        (fun v=>((n:ℝ)+1)*R v) (fun v=>mul_pos ht (hR v))
        (fun z hz=>hmem z (Finset.mem_filter.mp hz).1) hb
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
        InfinitePlace.sum_mult_eq] at hpack
      have htone : 1≤((n:ℝ)+1)^d := one_le_pow₀ (by
        have hn : (0:ℝ)≤n := by positivity
        linarith)
      calc
        _ ≤ (3:ℝ)^d*(1+((n:ℝ)+1)^d*V) := by simpa only [V, mul_div_assoc] using hpack
        _ ≤ (3:ℝ)^d*(((n:ℝ)+1)^d+((n:ℝ)+1)^d*V) :=
          mul_le_mul_of_nonneg_left (add_le_add_right htone _) (by positivity)
        _ = _ := by ring)
  simpa only [latticeRadialDecay, d, V, mul_assoc] using h

/-- Actual absolute summability and sum bound on the whole ideal coset. -/
theorem fractionalIdeal_radial_decay_summable
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I≠0) (a : K)
    (c : mixedSpace K) (R : InfinitePlace K→ℝ) (hR : ∀v, 0<R v) :
    Summable (fun z : {z : K // z-a∈I}=>latticeRadialDecay R c (z:K)) ∧
      (∑'z : {z : K // z-a∈I}, latticeRadialDecay R c (z:K)) ≤
        2*(3:ℝ)^(finrank ℚ K)*(1+(∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)) := by
  have hbound (S : Finset {z : K // z-a∈I}) :
      (∑z∈S, latticeRadialDecay R c (z:K)) ≤
        2*(3:ℝ)^(finrank ℚ K)*(1+(∏v, (R v)^(mult v))/(FractionalIdeal.absNorm I:ℝ)) := by
    have h := fractionalIdeal_radial_decay_finite_sum I hI (S.image Subtype.val) a c R hR (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact x.property)
    rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.ext hxy)] at h
    exact h
  have hs : Summable (fun z : {z : K // z-a∈I}=>latticeRadialDecay R c (z:K)) :=
    summable_of_sum_le (fun _=>by unfold latticeRadialDecay anisotropicRadius; positivity) hbound
  exact ⟨hs, hs.tsum_le_of_sum_le hbound⟩

end WaringSiegel.WSL2

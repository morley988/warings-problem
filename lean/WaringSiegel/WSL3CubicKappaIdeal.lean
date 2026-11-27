import WaringSiegel.WSL3CubicKappaLocal

/-! # WSL3: weighted ideal sums for the explicit cubic kappa function

The constants at the finitely many primes over6 are arbitrary nonnegative
parameters. The remaining finite twisted-sum bound is not an assumption of
the arithmetic convergence results below and is not asserted here.
-/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def cubicKappaGood (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Bool :=
  decide ((6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)

def cubicKappa (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (I : {I : Ideal (𝓞 K) // I ≠ 0}) : ℝ :=
  ∏ ve ∈ nonzeroIdealConductorGraph I,
    cubicKappaLocal (Ideal.absNorm ve.1.asIdeal) (C ve.1) (cubicKappaGood ve.1) ve.2

theorem cubicKappa_residue_norm_ge_two (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  letI := completionIntegers_residueFinite v
  letI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers K))
  have h : 2 ≤ Nat.card (ResidueField (v.adicCompletionIntegers K)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rw [completion_residue_card_eq_absNorm] at h
  exact_mod_cast h

theorem cubicKappa_nonneg (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (hC : ∀ v, 0 ≤ C v) (I : {I : Ideal (𝓞 K) // I ≠ 0}) : 0 ≤ cubicKappa C I :=
  Finset.prod_nonneg (fun ve _ => cubicKappaLocal_nonneg _ _ _ _ (by positivity) (hC ve.1))

theorem cubicKappaLocalMoment_pair_summable
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (m : ℕ) (t δ : ℝ) (hδ : 1 < δ) (h1 : δ ≤ (m:ℝ)/2-t)
    (h2 : δ ≤ (m:ℝ)-2*t) (h3 : δ ≤ (m:ℝ)-3*t) :
    Summable (fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
      cubicKappaLocalMoment (Ideal.absNorm ve.1.asIdeal) (C ve.1) (cubicKappaGood ve.1) m t ve.2) := by
  have hnonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
      0 ≤ cubicKappaLocalMoment (Ideal.absNorm v.asIdeal) (C v) (cubicKappaGood v) m t e :=
    cubicKappaLocalMoment_nonneg _ _ _ _ _ _ (by positivity) (hC v)
  apply (summable_prod_of_nonneg (fun ve => hnonneg ve.1 ve.2)).mpr
  constructor
  · intro v
    change Summable (cubicKappaLocalMoment (Ideal.absNorm v.asIdeal) (C v) (cubicKappaGood v) m t)
    exact cubicKappaLocalMoment_all_summable (Ideal.absNorm v.asIdeal) (C v) (cubicKappaGood v) m t
      (cubicKappa_residue_norm_ge_two v) (hC v) (by linarith)
  · have hmajor := (primeIdeal_norm_rpow_summable (K := K) hδ).mul_left (6*2^m)
    apply hmajor.of_norm_bounded_eventually
    filter_upwards [good_cubic_residue_primes_cofinite (K := K)] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hnonneg v))]
    simpa only [cubicKappaGood,decide_eq_true hv] using
      (cubicKappaLocalMoment_good_summable_bound (Ideal.absNorm v.asIdeal) (C v) m t δ
        (cubicKappa_residue_norm_ge_two v) hδ h1 h2 h3).2

theorem cubicKappa_weighted_eq_graph_product
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (I : {I : Ideal (𝓞 K) // I ≠ 0}) (m : ℕ) (t : ℝ) :
    (Ideal.absNorm I.1 : ℝ)^t * cubicKappa C I^m =
      ∏ ve ∈ nonzeroIdealConductorGraph I,
        cubicKappaLocalMoment (Ideal.absNorm ve.1.asIdeal) (C ve.1) (cubicKappaGood ve.1) m t ve.2 := by
  have hn : (Ideal.absNorm I.1 : ℝ) =
      ∏ ve ∈ nonzeroIdealConductorGraph I, (Ideal.absNorm ve.1.asIdeal : ℝ)^(ve.2+1) := by
    have h := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ))
      (nonzeroIdealConductorGraph_product I)
    simpa only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow] using h.symm
  rw [hn,← Real.finset_prod_rpow]
  · unfold cubicKappa
    rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ve _
    rw [cubicKappaLocalMoment,Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  · intro ve _
    positivity

theorem cubicKappa_weighted_summable
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (m : ℕ) (t δ : ℝ) (hδ : 1 < δ) (h1 : δ ≤ (m:ℝ)/2-t)
    (h2 : δ ≤ (m:ℝ)-2*t) (h3 : δ ≤ (m:ℝ)-3*t) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^t * cubicKappa C I^m) := by
  let f := fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
    cubicKappaLocalMoment (Ideal.absNorm ve.1.asIdeal) (C ve.1) (cubicKappaGood ve.1) m t ve.2
  have hs := summable_finset_products_of_nonneg f
    (fun ve => cubicKappaLocalMoment_nonneg _ _ _ _ _ _ (by positivity) (hC ve.1))
    (cubicKappaLocalMoment_pair_summable C hC m t δ hδ h1 h2 h3)
  apply (hs.comp_injective (nonzeroIdealConductorGraph_injective (K := K))).congr
  intro I
  exact (cubicKappa_weighted_eq_graph_product C I m t).symm

theorem cubicKappa_fourth_weighted_summable
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (t : ℝ) (ht : t < 1) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^t * cubicKappa C I^4) := by
  apply cubicKappa_weighted_summable C hC 4 t (2-t)
  all_goals norm_num <;> linarith

theorem cubicKappa_eighth_weighted_summable
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (t : ℝ) (ht : t < 7/3) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^t * cubicKappa C I^8) := by
  apply cubicKappa_weighted_summable C hC 8 t (min (4-t) (8-3*t))
  · exact lt_min (by linarith) (by linarith)
  · convert min_le_left (4-t) (8-3*t) using 1 <;> norm_num
  · exact (min_le_left (4-t) (8-3*t)).trans (by norm_num; linarith)
  · convert min_le_right (4-t) (8-3*t) using 1 <;> norm_num

end WaringSiegel
#print axioms WaringSiegel.cubicKappa_fourth_weighted_summable
#print axioms WaringSiegel.cubicKappa_eighth_weighted_summable

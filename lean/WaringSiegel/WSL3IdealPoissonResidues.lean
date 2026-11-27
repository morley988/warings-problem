import WaringSiegel.WSL3IdealPoissonIntegral

/-!
# Exact residue-class decomposition over an integral ideal
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {K : Type*} [Field K] [NumberField K]

def idealResidueRepresentative (I : Ideal (𝓞 K)) (q : 𝓞 K ⧸ I) : 𝓞 K :=
  Classical.choose (Ideal.Quotient.mk_surjective q)

@[simp] theorem idealResidueRepresentative_spec (I : Ideal (𝓞 K)) (q : 𝓞 K ⧸ I) :
    Ideal.Quotient.mk I (idealResidueRepresentative I q) = q :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective q)

def idealResiduePoint (I : Ideal (𝓞 K)) (p : (𝓞 K ⧸ I) × I) : 𝓞 K :=
  idealResidueRepresentative I p.1 + p.2

theorem idealResiduePoint_bijective (I : Ideal (𝓞 K)) :
    Function.Bijective (idealResiduePoint (K:=K) I) := by
  constructor
  · rintro ⟨q,x⟩ ⟨r,y⟩ h
    have hq : q = r := by
      have hh := congrArg (Ideal.Quotient.mk I) h
      change Ideal.Quotient.mk I (idealResidueRepresentative I q + (x:𝓞 K)) =
        Ideal.Quotient.mk I (idealResidueRepresentative I r + (y:𝓞 K)) at hh
      simpa only [(Ideal.Quotient.mk I).map_add,idealResidueRepresentative_spec,
        Ideal.Quotient.eq_zero_iff_mem.mpr x.2,Ideal.Quotient.eq_zero_iff_mem.mpr y.2,add_zero] using hh
    subst r
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact add_left_cancel h
  · intro x
    let q := Ideal.Quotient.mk I x
    let y : I := ⟨x-idealResidueRepresentative I q,by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [(Ideal.Quotient.mk I).map_sub,idealResidueRepresentative_spec]
      exact sub_self _⟩
    refine ⟨(q,y),?_⟩
    change idealResidueRepresentative I q + (x-idealResidueRepresentative I q) = x
    abel

def idealResidueEquiv (I : Ideal (𝓞 K)) : ((𝓞 K ⧸ I) × I) ≃ 𝓞 K :=
  Equiv.ofBijective (idealResiduePoint I) (idealResiduePoint_bijective I)

@[simp] theorem idealResidueEquiv_apply (I : Ideal (𝓞 K)) (p : (𝓞 K ⧸ I) × I) :
    idealResidueEquiv I p = idealResidueRepresentative I p.1 + p.2 := rfl

@[simp] theorem idealResidueEquiv_mk (I : Ideal (𝓞 K)) (p : (𝓞 K ⧸ I) × I) :
    Ideal.Quotient.mk I (idealResidueEquiv I p) = p.1 := by
  rw [idealResidueEquiv_apply,(Ideal.Quotient.mk I).map_add,idealResidueRepresentative_spec,
    Ideal.Quotient.eq_zero_iff_mem.mpr p.2.2,add_zero]

theorem schwartz_integralIdeal_coset_summable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun x : I => f (a+mixedEmbedding K ((x:𝓞 K):K))) := by
  have h := schwartz_fractionalIdeal_summable (integralIdealAsUnit I hI) (translateSchwartz a f)
  have he := (integralIdealFractionalEquiv I).summable_iff.mpr h
  simpa only [translateSchwartz_apply,integralIdealFractionalEquiv,Equiv.ofBijective,
    integralIdealFractionalMap] using he

theorem schwartz_residue_weight_summable (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)]
    (F : (𝓞 K ⧸ I) → ℂ) (f : 𝓢(mixedSpace K,ℂ)) :
    Summable (fun x : 𝓞 K => F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K))) := by
  apply Summable.of_norm_bounded ((schwartz_integerRing_summable f).norm.mul_left (∑ q,‖F q‖))
  intro x
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun q _ => norm_nonneg (F q)) (Finset.mem_univ (Ideal.Quotient.mk I x)))
    (norm_nonneg _)

/-- Actual decomposition of a weighted integer-ring sum into ideal cosets. -/
theorem schwartz_residue_decomposition (I : Ideal (𝓞 K)) [Fintype (𝓞 K ⧸ I)]
    (F : (𝓞 K ⧸ I) → ℂ) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K))) =
      ∑ q : 𝓞 K ⧸ I, F q * ∑' y : I,
        f (mixedEmbedding K (idealResidueRepresentative I q:K)+mixedEmbedding K ((y:𝓞 K):K)) := by
  have he (p : (𝓞 K ⧸ I) × I) :
      F (Ideal.Quotient.mk I (idealResidueEquiv I p))*f (mixedEmbedding K (idealResidueEquiv I p:K)) =
        F p.1*f (mixedEmbedding K (idealResidueRepresentative I p.1:K)+mixedEmbedding K ((p.2:𝓞 K):K)) := by
    rw [idealResidueEquiv_mk,idealResidueEquiv_apply]
    simp only [RingOfIntegers.coe_eq_algebraMap,
      (algebraMap (𝓞 K) K).map_add,(mixedEmbedding K).map_add]
  have hs := (idealResidueEquiv I).summable_iff.mpr (schwartz_residue_weight_summable I F f)
  have hseq : Summable (fun p : (𝓞 K ⧸ I) × I =>
      F p.1*f (mixedEmbedding K (idealResidueRepresentative I p.1:K)+mixedEmbedding K ((p.2:𝓞 K):K))) := by
    apply hs.congr
    intro p
    exact he p
  calc
    _ = ∑' p : (𝓞 K ⧸ I) × I,
        F (Ideal.Quotient.mk I (idealResidueEquiv I p))*f (mixedEmbedding K (idealResidueEquiv I p:K)) :=
      ((idealResidueEquiv I).tsum_eq (fun x : 𝓞 K => F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K)))).symm
    _ = ∑' p : (𝓞 K ⧸ I) × I,
        F p.1*f (mixedEmbedding K (idealResidueRepresentative I p.1:K)+mixedEmbedding K ((p.2:𝓞 K):K)) :=
      tsum_congr he
    _ = _ := by
      rw [hseq.tsum_prod,tsum_fintype]
      apply Finset.sum_congr rfl
      intro q _
      change (∑' y : I, F q*f (mixedEmbedding K (idealResidueRepresentative I q:K)+
        mixedEmbedding K ((y:𝓞 K):K))) = _
      rw [tsum_mul_left]

#print axioms idealResiduePoint_bijective
#print axioms schwartz_residue_decomposition
end WaringSiegel.WSL3Poisson

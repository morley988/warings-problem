import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Residue fields under a dense valuation-preserving embedding

An embedding of valued fields with dense image induces a surjection on residue
fields: approximate an integral element within valuation strictly below one.
This gives a proved finiteness transfer to the field completion.
-/

noncomputable section

open scoped NumberField WithZero
open IsLocalRing Topology

namespace WaringSiegel

section DenseEmbedding

variable {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Valued L Γ]
    (v : Valuation K Γ) (f : K →+* L)
    (hval : ∀ x, Valued.v (f x) = v x)

def valuationIntegerMap : v.integer →+* (Valued.v : Valuation L Γ).valuationSubring where
  toFun x := ⟨f x, by change Valued.v (f x) ≤ 1; rw [hval]; exact x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f (x : K) (y : K))
  map_mul' x y := Subtype.ext (map_mul f (x : K) (y : K))

instance valuationIntegerMap_isLocalHom : IsLocalHom (valuationIntegerMap v f hval) where
  map_nonunit x hx := by
    apply (Valuation.integer.integers v).isUnit_iff_valuation_eq_one.mpr
    have h := (Valuation.valuationSubring.integers
      (Valued.v : Valuation L Γ)).isUnit_iff_valuation_eq_one.mp hx
    change Valued.v (f x) = 1 at h
    change v x = 1
    rwa [hval] at h

theorem residueMap_surjective_of_dense
    (hdense : DenseRange f) :
    Function.Surjective (ResidueField.map (valuationIntegerMap v f hval)) := by
  intro a
  obtain ⟨y, rfl⟩ := residue_surjective a
  have hnhds : {z : L | Valued.v (z - (y : L)) < (1 : Γ)} ∈ 𝓝 (y : L) := by
    apply Valued.mem_nhds.mpr
    exact ⟨1, fun _ h => h⟩
  obtain ⟨x, hx⟩ := hdense.mem_nhds hnhds
  have hxi : v x ≤ 1 := by
    rw [← hval]
    have hle := (Valued.v : Valuation L Γ).map_add_le_max' (f x - y) y
    rw [sub_add_cancel] at hle
    exact hle.trans (max_le hx.le y.property)
  refine ⟨residue v.integer ⟨x, hxi⟩, ?_⟩
  rw [ResidueField.map_residue]
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  exact (Valuation.mem_maximalIdeal_iff L (Valued.v : Valuation L Γ)).mpr hx

include hval in
theorem finite_residueField_of_dense
    [Finite (ResidueField v.integer)] (hdense : DenseRange f) :
    Finite (ResidueField (Valued.v : Valuation L Γ).valuationSubring) :=
  Finite.of_surjective (ResidueField.map (valuationIntegerMap v f hval))
    (residueMap_surjective_of_dense v f hval hdense)

end DenseEmbedding

variable {K : Type*} [Field K] [NumberField K]

theorem finite_completionResidue_of_finite_valuationResidue
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    [Finite (ResidueField (v.valuation K).integer)] :
    Finite (ResidueField (v.adicCompletionIntegers K)) := by
  apply finite_residueField_of_dense (v.valuation K) (algebraMap K (v.adicCompletion K))
    (fun x : K => v.valuedAdicCompletion_eq_valuation' (K := K) x)
  exact UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K))

end WaringSiegel

#print axioms WaringSiegel.finite_completionResidue_of_finite_valuationResidue

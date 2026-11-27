import WaringSiegel.WSL4MajorRamanujamMonogenicKernel

/-! # The actual monogenic coefficient-ring map into a complete local ring -/
noncomputable section
set_option maxHeartbeats 1500000
open Polynomial IsLocalRing
open scoped Classical
namespace WaringSiegel.WSL4
variable (p : ℕ) [Fact p.Prime]
variable {A : Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A] [Algebra (ZMod p) (ResidueField A)]

theorem exists_monogenic_local_map (pb : PowerBasis (ZMod p) (ResidueField A))
    (F : ℤ[X]) (hF : F.map (Int.castRingHom (ZMod p))=minpoly (ZMod p) pb.gen) :
    ∃ f : AdjoinRoot F →+* A,
      (residue A).comp f=monogenicResidueHom p pb F hF := by
  let g : A[X] := F.map (Int.castRingHom A)
  have hc₁ : (residue A).comp (Int.castRingHom A)=Int.castRingHom (ResidueField A) :=
    RingHom.ext_int _ _
  have hc₂ : (algebraMap (ZMod p) (ResidueField A)).comp (Int.castRingHom (ZMod p))=
      Int.castRingHom (ResidueField A) := RingHom.ext_int _ _
  have hred : g.map (residue A)=
      (minpoly (ZMod p) pb.gen).map (algebraMap (ZMod p) (ResidueField A)) := by
    dsimp only [g]
    rw [Polynomial.map_map,hc₁,← hF,Polynomial.map_map,hc₂]
  have hroot : g.eval₂ (residue A) pb.gen=0 := by
    rw [eval₂_eq_eval_map,hred,eval_map]
    exact minpoly.aeval _ _
  have hsep : (minpoly (ZMod p) pb.gen).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible pb.isIntegral_gen)
  have hder : g.derivative.eval₂ (residue A) pb.gen ≠ 0 := by
    rw [eval₂_eq_eval_map,← derivative_map,hred,derivative_map,eval_map]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨b,hb,hbr⟩ := WSL4Weil.local_adic_simple_root_lift g pb.gen hroot hder
  have hbF : F.eval₂ (Int.castRingHom A) b=0 := by
    simpa only [g,eval_map] using hb
  let f : AdjoinRoot F →+* A := AdjoinRoot.lift (Int.castRingHom A) b hbF
  refine ⟨f,?_⟩
  ext a
  obtain ⟨Q,rfl⟩ := AdjoinRoot.mk_surjective a
  change residue A (AdjoinRoot.lift (Int.castRingHom A) b hbF (AdjoinRoot.mk F Q))=_
  rw [AdjoinRoot.lift_mk,monogenicResidueHom_mk,hom_eval₂,hc₁,hbr]

theorem exists_monogenic_coefficient_ring_of_powerBasis
    (pb : PowerBasis (ZMod p) (ResidueField A)) :
    ∃ F : ℤ[X], F.Monic ∧ F.natDegree=Module.finrank (ZMod p) (ResidueField A) ∧
      ∃ f : AdjoinRoot F →+* A,
        Function.Surjective ((residue A).comp f) ∧
        ∀ b : AdjoinRoot F,residue A (f b)=0 ↔ (p:AdjoinRoot F) ∣ b := by
  obtain ⟨F,hmon,hF,hdegree⟩ := exists_integer_monic_minpoly_lift p pb
  obtain ⟨f,hf⟩ := exists_monogenic_local_map p pb F hF
  refine ⟨F,hmon,hdegree,f,?_,?_⟩
  · rw [hf]
    exact monogenicResidueHom_surjective p pb F hF
  · intro b
    change ((residue A).comp f) b=0 ↔ _
    rw [hf,monogenicResidueHom_eq_zero_iff]

/-- Every finite residue field has an actual integral monogenic lift inside the
complete local ring, with surjective residue map and exact kernel p. -/
theorem exists_monogenic_coefficient_ring [Finite (ResidueField A)] :
    ∃ F : ℤ[X], F.Monic ∧ F.natDegree=Module.finrank (ZMod p) (ResidueField A) ∧
      ∃ f : AdjoinRoot F →+* A,
        Function.Surjective ((residue A).comp f) ∧
        ∀ b : AdjoinRoot F,residue A (f b)=0 ↔ (p:AdjoinRoot F) ∣ b := by
  letI : FiniteDimensional (ZMod p) (ResidueField A) := Module.Finite.of_finite
  exact exists_monogenic_coefficient_ring_of_powerBasis p
    (Field.powerBasisOfFiniteOfSeparable (ZMod p) (ResidueField A))

#print axioms exists_monogenic_local_map
#print axioms exists_monogenic_coefficient_ring
end WaringSiegel.WSL4

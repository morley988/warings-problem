import WaringSiegel.WSL4MixedCountEmbedding
import WaringSiegel.WSL2MomentMixedTransform

/-! # Injecting all congruent off-diagonal mixed solutions into the transformed count -/
noncomputable section
set_option maxHeartbeats 1600000
open NumberField
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def mixedCubicBoxPhase (X M Y : Finset (𝓞 K))
    (t : M × ((X × X) × ((Y × Y) × (Y × Y)))) : 𝓞 K :=
  (t.2.1.1.val^3-t.2.1.2.val^3)+t.1.val^3*
    ((t.2.2.1.1.val^3-t.2.2.1.2.val^3)+(t.2.2.2.1.val^3-t.2.2.2.2.val^3))

def MixedCongruentOffdiagonal (X M Y : Finset (𝓞 K)) :=
  {t : M × ((X × X) × ((Y × Y) × (Y × Y))) //
    t.2.1.1.val ≠ t.2.1.2.val ∧ t.1.val^3 ∣ t.2.1.2.val-t.2.1.1.val ∧
      mixedCubicBoxPhase X M Y t = 0}

instance mixedCongruentOffdiagonalFintype (X M Y : Finset (𝓞 K)) :
    Fintype (MixedCongruentOffdiagonal X M Y) := by
  unfold MixedCongruentOffdiagonal
  infer_instance

def mixedCongruentOffdiagonalCount (X M Y : Finset (𝓞 K)) : ℕ :=
  Fintype.card (MixedCongruentOffdiagonal X M Y)

theorem mixedCongruentOffdiagonalCount_le (X M Y H Z : Finset (𝓞 K))
    (hM : ∀ m ∈ M, m ≠ 0)
    (hH : ∀ m ∈ M, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → m^3 ∣ y-x →
      cubicCongruenceQuotient m x y ∈ H)
    (hZ : ∀ x ∈ X, ∀ y ∈ X, x+y ∈ Z) :
    mixedCongruentOffdiagonalCount X M Y ≤ mixedBoxCount H Z M Y := by
  let T := {t : H × ((Z × M) × ((Y × Y) × (Y × Y))) //
    mixedWeightedPhase (fun h : H => (h : 𝓞 K)) (fun z : Z => (z : 𝓞 K))
      (fun m : M => (m : 𝓞 K)) (fun y : Y => (y : 𝓞 K)) t = 0}
  let f : MixedCongruentOffdiagonal X M Y → T := fun t =>
    ⟨(⟨cubicCongruenceQuotient t.val.1.val t.val.2.1.1.val t.val.2.1.2.val,
        hH _ t.val.1.property _ t.val.2.1.1.property _ t.val.2.1.2.property
          t.property.1 t.property.2.1⟩,
      ((⟨t.val.2.1.1.val+t.val.2.1.2.val,
          hZ _ t.val.2.1.1.property _ t.val.2.1.2.property⟩,t.val.1),
        ((t.val.2.2.1.2,t.val.2.2.1.1),(t.val.2.2.2.2,t.val.2.2.2.1)))),by
      apply (mixedWeightedPhase_eq_zero_iff _ _ _ _ _).mpr
      have heq : t.val.2.1.1.val^3+t.val.1.val^3*
          (t.val.2.2.1.1.val^3+t.val.2.2.2.1.val^3) =
        t.val.2.1.2.val^3+t.val.1.val^3*
          (t.val.2.2.1.2.val^3+t.val.2.2.2.2.val^3) := by
        have hh := t.property.2.2
        dsimp only [mixedCubicBoxPhase] at hh
        linear_combination hh
      have ht := (mixed_cubic_transformed_iff t.val.1.val t.val.2.1.1.val t.val.2.1.2.val
        (t.val.2.2.1.1.val^3+t.val.2.2.2.1.val^3)
        (t.val.2.2.1.2.val^3+t.val.2.2.2.2.val^3)
        (hM _ t.val.1.property) t.property.2.1).mp heq
      convert ht using 1 <;> ring⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hm : a.val.1.val = b.val.1.val :=
      congrArg (fun t : T => t.val.2.1.2.val) hab
    have hh : cubicCongruenceQuotient a.val.1.val a.val.2.1.1.val a.val.2.1.2.val =
        cubicCongruenceQuotient b.val.1.val b.val.2.1.1.val b.val.2.1.2.val :=
      congrArg (fun t : T => t.val.1.val) hab
    have hz : a.val.2.1.1.val+a.val.2.1.2.val = b.val.2.1.1.val+b.val.2.1.2.val :=
      congrArg (fun t : T => t.val.2.1.1.val) hab
    have hxy : (a.val.2.1.1.val,a.val.2.1.2.val) = (b.val.2.1.1.val,b.val.2.1.2.val) := by
      apply cubicOffdiagonalCoordinates_injOn a.val.1.val a.property.2.1
        (by simpa only [hm] using b.property.2.1)
      exact Prod.ext (by simpa only [hm] using hh) hz
    have hy11 : a.val.2.2.1.1.val=b.val.2.2.1.1.val :=
      congrArg (fun t : T => t.val.2.2.1.2.val) hab
    have hy12 : a.val.2.2.1.2.val=b.val.2.2.1.2.val :=
      congrArg (fun t : T => t.val.2.2.1.1.val) hab
    have hy21 : a.val.2.2.2.1.val=b.val.2.2.2.1.val :=
      congrArg (fun t : T => t.val.2.2.2.2.val) hab
    have hy22 : a.val.2.2.2.2.val=b.val.2.2.2.2.val :=
      congrArg (fun t : T => t.val.2.2.2.1.val) hab
    apply Subtype.ext
    exact Prod.ext (Subtype.ext hm) (Prod.ext
      (Prod.ext (Subtype.ext (congrArg Prod.fst hxy)) (Subtype.ext (congrArg Prod.snd hxy)))
      (Prod.ext (Prod.ext (Subtype.ext hy11) (Subtype.ext hy12))
        (Prod.ext (Subtype.ext hy21) (Subtype.ext hy22))))
  exact Fintype.card_le_of_injective f hf

#print axioms mixedCongruentOffdiagonalCount_le
end WaringSiegel.WSL4Local

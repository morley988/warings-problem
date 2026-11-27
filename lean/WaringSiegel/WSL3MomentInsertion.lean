import WaringSiegel.WSL3MomentHuaWeighted
import WaringSiegel.WSL3MomentSystemEnergy
import WaringSiegel.WSL2MomentCubicWeyl

/-!
# Exact finite insertion of missing frequency coordinates

Every translated collision fiber is bounded by the zero-frequency energy.
Consequently a finite box of missing equations costs only its cardinality.
The proof uses actual probability Haar orthogonality, with no analytic kernel
or completion estimate introduced as an assumption.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {ι α : Type*} [Fintype ι] [Fintype α]

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

def shiftedFrequencyCount (v : α → ι → ℤ) (a : ι → ℤ) : ℕ :=
  (Finset.univ.filter (fun xy : α × α => v xy.1 - v xy.2 = a)).card

theorem norm_frequencySum_shift (v : α → ι → ℤ) (a : ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    ‖frequencySum (fun x => v x + a) (fun _ => 1) θ‖ =
      ‖frequencySum v (fun _ => 1) θ‖ := by
  simp only [frequencySum, one_mul, WaringSiegel.latticeCharacter_add,
    ← Finset.sum_mul, norm_mul, norm_latticeCharacter_eq_one, mul_one]

theorem shiftedFrequencyCount_le_energy (v : α → ι → ℤ) (a : ι → ℤ) :
    shiftedFrequencyCount v a ≤ frequencyEnergy v := by
  have hcorr : (∫ θ, frequencySum v (fun _ => 1) θ *
      conj (frequencySum (fun x => v x + a) (fun _ => 1) θ) ∂latticeHaar) =
      (shiftedFrequencyCount v a : ℂ) := by
    rw [integral_frequencySum_mul_conj]
    have heq (xy : α × α) : v xy.1 = v xy.2 + a ↔ v xy.1 - v xy.2 = a := by
      rw [sub_eq_iff_eq_add, add_comm]
    simp only [map_one, one_mul, heq, ← Finset.sum_filter]
    simp [shiftedFrequencyCount]
  have hnorm : (shiftedFrequencyCount v a : ℝ) ≤ (frequencyEnergy v : ℝ) := by
    calc
      (shiftedFrequencyCount v a : ℝ) =
          ‖∫ θ, frequencySum v (fun _ => 1) θ *
            conj (frequencySum (fun x => v x + a) (fun _ => 1) θ) ∂latticeHaar‖ := by
        rw [hcorr, Complex.norm_natCast]
      _ ≤ ∫ θ, ‖frequencySum v (fun _ => 1) θ *
            conj (frequencySum (fun x => v x + a) (fun _ => 1) θ)‖ ∂latticeHaar :=
        norm_integral_le_integral_norm _
      _ = ∫ θ, ‖frequencySum v (fun _ => 1) θ‖^2 ∂latticeHaar := by
        congr 1
        funext θ
        rw [norm_mul, Complex.norm_conj, norm_frequencySum_shift, pow_two]
      _ = _ := integral_norm_frequencySum_sq_one v
  exact_mod_cast hnorm

theorem frequencyEnergy_projection_bound (v : α → ι → ℤ)
    (T : Finset (α × α)) (D : Finset (ι → ℤ))
    (hcover : ∀ xy ∈ T, v xy.1 - v xy.2 ∈ D) :
    T.card ≤ D.card * frequencyEnergy v := by
  let f : α × α → ι → ℤ := fun xy => v xy.1 - v xy.2
  have hfiber (a : ι → ℤ) (ha : a ∈ T.image f) :
      (T.filter (fun xy => f xy = a)).card ≤ frequencyEnergy v := by
    apply le_trans (Finset.card_le_card (show T.filter (fun xy => f xy = a) ⊆
      Finset.univ.filter (fun xy => v xy.1 - v xy.2 = a) from ?_))
      (shiftedFrequencyCount_le_energy v a)
    intro xy hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hxy).2⟩
  have hi : T.image f ⊆ D := by
    intro a ha
    obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp ha
    exact hcover xy hxy
  calc
    T.card ≤ frequencyEnergy v * (T.image f).card :=
      Finset.card_le_mul_card_image T (frequencyEnergy v) hfiber
    _ ≤ frequencyEnergy v * D.card := Nat.mul_le_mul_left _ (Finset.card_le_card hi)
    _ = _ := Nat.mul_comm _ _

variable {R : Type*} [AddCommMonoid R]

def systemCoordinates (coord : R →+ (ι → ℤ)) (r : ℕ) :
    (Fin r → R) →+ (Fin r × ι → ℤ) where
  toFun f ji := coord (f ji.1) ji.2
  map_zero' := by ext ji; simp
  map_add' := by intro f g; ext ji; simp

theorem systemCoordinates_injective (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (r : ℕ) :
    Function.Injective (systemCoordinates coord r) := by
  intro f g h
  funext j
  apply hcoord
  funext i
  exact congrFun h (j,i)

theorem frequencyEnergy_systemCoordinates (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (r s : ℕ) (v : α → Fin r → R) :
    (frequencyEnergy (fun x : Fin s → α =>
      systemCoordinates coord r (∑ i, v (x i))) : ℝ) =
      weightedSystemEnergy s v (fun _ => 1) := by
  have hinj := systemCoordinates_injective coord hcoord r
  simp only [frequencyEnergy, weightedSystemEnergy, Finset.prod_const_one, one_mul,
    hinj.eq_iff, Nat.cast_sum, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

#print axioms shiftedFrequencyCount_le_energy
#print axioms frequencyEnergy_projection_bound

end WaringSiegel.WSL3

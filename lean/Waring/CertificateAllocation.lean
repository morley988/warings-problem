import Waring.CertificateHeight
import Waring.ResourceDifferencingCap
import Mathlib.Data.List.OfFn

/-!
# Frozen certificate resources as actual analytic Hölder allocations

Every frozen piece is checked directly for resource mass and per-factor
loads in the finite form used by the analytic theorem. The real saving of
the resulting allocation is exactly `pieceSavingReal`; no feasibility or
weighted-saving correspondence is left as an analytic premise.
-/

noncomputable section
open scoped BigOperators
namespace Waring.Certificate
open ResourceDifferencingCap

def resourceAt (piece : Piece) (r : Fin piece.resources.size) : Resource :=
  piece.resources[r.val]

def PieceAllocationValid (j : ℕ) (piece : Piece) : Prop :=
  (∀ r : Fin piece.resources.size, 0 ≤ (resourceAt piece r).weight ∧ (resourceAt piece r).factor ≤ j) ∧
  (∑ r : Fin piece.resources.size, (resourceAt piece r).weight) ≤ 1 ∧
  ∀ i : Fin (j+1),
    (∑ r : Fin piece.resources.size,
      if (resourceAt piece r).factor=i.val then
        (q (resourceAt piece r).order)*(resourceAt piece r).weight else 0) ≤ 1

instance (j : ℕ) (piece : Piece) : Decidable (PieceAllocationValid j piece) := by
  unfold PieceAllocationValid
  infer_instance

def allocationFactor (j n : ℕ) (hn : n ≤ j) : Option (Fin j) :=
  if h0 : n=0 then none else some ⟨n-1, by omega⟩

def factorIndex {j : ℕ} : Option (Fin j) → Fin (j+1)
  | none => 0
  | some i => i.succ

theorem allocationFactor_eq_iff (j n : ℕ) (hn : n ≤ j) (i : Option (Fin j)) :
    allocationFactor j n hn=i ↔ n=(factorIndex i).val := by
  cases i with
  | none => simp [allocationFactor, factorIndex]
  | some i =>
    unfold allocationFactor
    split_ifs with h0
    · simp [h0, factorIndex]
    · simp only [Option.some.injEq, Fin.ext_iff, factorIndex, Fin.val_succ]
      omega

def pieceAllocation (k : ℕ) (p : Policy) (coefficient : Curve) (piece : Piece) (height : ℝ)
    (hv : PieceAllocationValid p.phi.size piece)
    (K : Fin piece.resources.size → ℝ) (hK : ∀ r, 0 ≤ K r) :
    Allocation p.phi.size (Fin piece.resources.size) where
  factor r := allocationFactor p.phi.size (resourceAt piece r).factor (hv.1 r).2
  order r := (resourceAt piece r).order
  weight r := (resourceAt piece r).weight
  constant := K
  saving r := resourceReal k p coefficient (resourceAt piece r) height
  order_nonneg r := by positivity
  weight_nonneg r := by exact_mod_cast (hv.1 r).1
  constant_nonneg := hK
  mass_le := by exact_mod_cast hv.2.1
  load_le := by
    intro i
    simp only [Finset.sum_filter, allocationFactor_eq_iff]
    have hh := hv.2.2 (factorIndex i)
    simp only [q] at hh
    have hc := (Rat.cast_le (K:=ℝ)).mpr hh
    simpa only [Rat.cast_sum, apply_ite, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_zero, Rat.cast_one] using hc

theorem resourceAt_list (piece : Piece) :
    List.ofFn (resourceAt piece) = piece.resources.toList := by
  simpa only [resourceAt, Array.length_toList, Array.getElem_toList] using
    List.ofFn_getElem piece.resources.toList

theorem sum_resourceAt (piece : Piece) (f : Resource → ℝ) :
    (∑ r : Fin piece.resources.size, f (resourceAt piece r)) =
      (piece.resources.toList.map f).sum := by
  rw [← resourceAt_list, List.map_ofFn, List.sum_ofFn]
  rfl

theorem savingRealList_eq_sum_map (k : ℕ) (p : Policy) (coefficient : Curve)
    (height : ℝ) (resources : List Resource) :
    savingRealList k p coefficient height resources =
      (resources.map (fun r => (r.weight:ℝ)*resourceReal k p coefficient r height)).sum := by
  induction resources with
  | nil => rfl
  | cons r rs ih => simp only [savingRealList, List.map_cons, List.sum_cons, ih]

/-- The analytic saving in the cap theorem is precisely the real extension
of the certified resource evaluator, before the retained minimum with one. -/
theorem pieceAllocation_totalSaving (k : ℕ) (p : Policy) (coefficient : Curve)
    (piece : Piece) (height : ℝ) (hv : PieceAllocationValid p.phi.size piece)
    (K : Fin piece.resources.size → ℝ) (hK : ∀ r, 0 ≤ K r) :
    (pieceAllocation k p coefficient piece height hv K hK).totalSaving =
      pieceSavingReal k p coefficient piece height := by
  change (∑ r : Fin piece.resources.size,
    ((resourceAt piece r).weight:ℝ)*resourceReal k p coefficient (resourceAt piece r) height) = _
  rw [sum_resourceAt piece (fun r => (r.weight:ℝ)*resourceReal k p coefficient r height)]
  exact (savingRealList_eq_sum_map k p coefficient height piece.resources.toList).symm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies8_allocation_valid :
    ∀ i : Fin policies8.size, ∀ j : Fin (policies8[i.val].pieces.size),
      PieceAllocationValid policies8[i.val].phi.size (policies8[i.val].pieces[j.val]) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem policies9_allocation_valid :
    ∀ i : Fin policies9.size, ∀ j : Fin (policies9[i.val].pieces.size),
      PieceAllocationValid policies9[i.val].phi.size (policies9[i.val].pieces[j.val]) := by
  decide +kernel

#print axioms policies8_allocation_valid
#print axioms policies9_allocation_valid
#print axioms pieceAllocation_totalSaving

end Waring.Certificate

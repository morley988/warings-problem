import Waring.CertificateHeightApplications
import Waring.Recurrence

/-!
# The complete certificate objective at every real height

The fixed-data association checks below link the stored backward rows to their
original policy/curve formulas, verify the entire recurrence from the maximum
of all stored terminal endpoints, and include the exact upward-rounding bound.
Monotonicity then gives the full rounded bound for every real height of every
actual policy piece. These are algebraic exponent statements, not a claim that
the analytic estimates represented by those exponents have been proved.
-/

noncomputable section
namespace Waring.Certificate

def prefixTotal (p : Policy) (i : Nat) : Q :=
  (p.phi.toList.take i).foldl (· + ·) 0

def prefixLength (p : Policy) (i : Nat) : Q := 1 - prefixTotal p i

def prefixShift (k : Nat) (p : Policy) (i : Nat) : Q := q i - q k * prefixTotal p i

/-- Prefactor and diagonal at a single counted backward stage. -/
def recurrenceRow (k : Nat) (curve : Curve) (p : Policy) (i : Nat) : Q × Q :=
  let rr := p.path[i-1]!
  let u := p.path[i]!
  let h := 2*rr-u
  let lu := (moment curve (2*u)).getD 0
  let lh := (moment curve (2*h)).getD 0
  ((lh*prefixLength p i+prefixShift k p i+prefixTotal p i+
      (q (2*u)-1)*p.phi[i]!)/2,
    1+prefixShift k p i+prefixTotal p (i+1)+lu*prefixLength p (i+1))

def recurrenceRows (k : Nat) (curve : Curve) (p : Policy) : List (Q × Q) :=
  ((List.range (p.phi.size-1)).map (fun t => p.phi.size-(t+1))).map
    (recurrenceRow k curve p)

def firstOffset (p : Policy) : Q := (q (2*p.halfOrder)-3)*p.phi[0]!

def firstDiagonal (curve : Curve) (p : Policy) : Q :=
  1+p.phi[0]!+(moment curve (2*(p.halfOrder-1))).getD 0*prefixLength p 1

def runBackwardQ : List (Q × Q) → Q → Q
  | [], current => current
  | row :: rows, current => runBackwardQ rows (row.1+qmax row.2 current/2)

/-- The maximum is taken over precisely the major branch and every stored
endpoint exponent. -/
def terminalMaximum (e : Evaluation) : Q :=
  (e.pieces.toList.flatMap (fun piece => piece.endpoints.toList.map Endpoint.exponent)).foldl
    qmax e.major

def castRows (rows : List (Q × Q)) : List (ℝ × ℝ) :=
  rows.map (fun row => ((row.1 : ℝ), (row.2 : ℝ)))

theorem cast_qmax (a b : Q) : ((qmax a b : Q) : ℝ) = max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · have h' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    simp [qmax, h, max_eq_right h']
  · have h' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast le_of_not_ge h
    simp [qmax, h, max_eq_left h']

theorem runBackwardQ_cast (rows : List (Q × Q)) (current : Q) :
    (runBackwardQ rows current : ℝ) =
      Recurrence.runBackward (castRows rows) (current : ℝ) := by
  induction rows generalizing current with
  | nil => rfl
  | cons row rows ih =>
    simp only [runBackwardQ, castRows, List.map_cons, Recurrence.runBackward]
    rw [ih]
    simp [Recurrence.backward, castRows, cast_qmax]

/-- Exact consistency of the complete recurrence and the terminal maxima for
one fixed entry. The full replay separately checks every moment lookup. -/
def EntryRecurrenceAssociation (k : Nat) (curve : Curve) (p : Policy) (entry : Entry) : Prop :=
  entry.evaluation.backwards.toList.map (fun row => (row.prefactor, row.diagonal)) =
      recurrenceRows k curve p ∧
  entry.evaluation.major ≤ terminalMaximum entry.evaluation ∧
  (∀ i : Fin p.pieces.size,
    qmax entry.evaluation.pieces[i.val]!.endpoints[0]!.exponent
      entry.evaluation.pieces[i.val]!.endpoints[1]!.exponent ≤ terminalMaximum entry.evaluation) ∧
  entry.evaluation.raw = firstOffset p + qmax (firstDiagonal curve p)
    (runBackwardQ (recurrenceRows k curve p) (terminalMaximum entry.evaluation)) ∧
  entry.evaluation.raw ≤ entry.rounded

instance (k : Nat) (curve : Curve) (p : Policy) (entry : Entry) :
    Decidable (EntryRecurrenceAssociation k curve p entry) := by
  unfold EntryRecurrenceAssociation
  infer_instance

def RoundRecurrenceAssociation (k : Nat) (policies : Array Policy) (round : Round) : Prop :=
  ∀ i : Fin policies.size,
    EntryRecurrenceAssociation k round.interpolation.values policies[i.val]! round.entries[i.val]!

instance (k : Nat) (policies : Array Policy) (round : Round) :
    Decidable (RoundRecurrenceAssociation k policies round) := by
  unfold RoundRecurrenceAssociation
  infer_instance

/-- The complete terminal-to-first-step objective, using the exact static
constants obtained from the frozen policy and its common input curve. -/
def fullObjectiveReal (k : Nat) (curve coefficient : Curve) (p : Policy)
    (e : Evaluation) (piece : Piece) (height : ℝ) : ℝ :=
  let params := terminalParameters k curve p
  (firstOffset p : ℝ) + max (firstDiagonal curve p : ℝ)
    (Recurrence.runBackward (castRows (recurrenceRows k curve p))
      (max (e.major : ℝ)
        (pieceResidualReal k p coefficient piece params.base params.slope params.scale height)))

theorem entryRecurrenceAssociation_bound (k : Nat) (curve coefficient : Curve)
    (p : Policy) (entry : Entry)
    (hrec : EntryRecurrenceAssociation k curve p entry)
    (hheight : PolicyHeightAssociation k curve coefficient p entry.evaluation)
    (hguard : PolicyAnalyticGuards k p) (i : Fin p.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (p.pieces[i.val]!.lo : ℝ) (p.pieces[i.val]!.hi : ℝ)) :
    fullObjectiveReal k curve coefficient p entry.evaluation p.pieces[i.val]!
      (1+t*((terminalParameters k curve p).top-1)) ≤ (entry.rounded : ℝ) := by
  have hh := policyHeightAssociation_all_heights k curve coefficient p entry.evaluation
    hheight hguard i t ht
  have hend : max (entry.evaluation.pieces[i.val]!.endpoints[0]!.exponent : ℝ)
      (entry.evaluation.pieces[i.val]!.endpoints[1]!.exponent : ℝ) ≤
        (terminalMaximum entry.evaluation : ℝ) := by
    rw [← cast_qmax]
    exact_mod_cast hrec.2.2.1 i
  have hmajor : (entry.evaluation.major : ℝ) ≤ (terminalMaximum entry.evaluation : ℝ) := by
    exact_mod_cast hrec.2.1
  have hterm := max_le hmajor (hh.trans hend)
  have hback := Recurrence.runBackward_mono
    (castRows (recurrenceRows k curve p)) hterm
  have hfirst := Recurrence.first_step_mono (offset := (firstOffset p : ℝ))
    (diagonal := (firstDiagonal curve p : ℝ)) hback
  have hraw : (entry.evaluation.raw : ℝ) =
      (firstOffset p : ℝ) + max (firstDiagonal curve p : ℝ)
        (Recurrence.runBackward (castRows (recurrenceRows k curve p))
          (terminalMaximum entry.evaluation : ℝ)) := by
    rw [hrec.2.2.2.1]
    simp only [Rat.cast_add, cast_qmax, runBackwardQ_cast]
  have hround : (entry.evaluation.raw : ℝ) ≤ (entry.rounded : ℝ) := by
    exact_mod_cast hrec.2.2.2.2
  exact hfirst.trans (hraw ▸ hround)

theorem round8_01_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_01 := by decide +kernel

theorem round8_02_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_02 := by decide +kernel

theorem round8_03_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_03 := by decide +kernel

theorem round8_04_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_04 := by decide +kernel

theorem round8_05_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_05 := by decide +kernel

theorem round8_06_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_06 := by decide +kernel

theorem round8_07_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_07 := by decide +kernel

theorem round8_08_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_08 := by decide +kernel

theorem round8_09_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_09 := by decide +kernel

theorem round8_10_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_10 := by decide +kernel

theorem round8_11_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_11 := by decide +kernel

theorem round8_12_recurrence_association :
    RoundRecurrenceAssociation 8 policies8 round8_12 := by decide +kernel

theorem round9_01_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_01 := by decide +kernel

theorem round9_02_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_02 := by decide +kernel

theorem round9_03_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_03 := by decide +kernel

theorem round9_04_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_04 := by decide +kernel

theorem round9_05_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_05 := by decide +kernel

theorem round9_06_recurrence_association :
    RoundRecurrenceAssociation 9 policies9 round9_06 := by decide +kernel

theorem heightCheckedRounds8_recurrence :
    ∀ round ∈ heightCheckedRounds8, RoundRecurrenceAssociation 8 policies8 round := by
  simp only [heightCheckedRounds8, List.forall_mem_cons]
  exact ⟨round8_01_recurrence_association, round8_02_recurrence_association, round8_03_recurrence_association, round8_04_recurrence_association, round8_05_recurrence_association, round8_06_recurrence_association, round8_07_recurrence_association, round8_08_recurrence_association, round8_09_recurrence_association, round8_10_recurrence_association, round8_11_recurrence_association, round8_12_recurrence_association, by simp⟩

theorem certificate8_full_objective_all_real_heights
    (round : Round) (hr : round ∈ heightCheckedRounds8)
    (i : Fin policies8.size) (j : Fin policies8[i.val]!.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (policies8[i.val]!.pieces[j.val]!.lo : ℝ)
      (policies8[i.val]!.pieces[j.val]!.hi : ℝ)) :
    fullObjectiveReal 8 round.interpolation.values coefficient8.values policies8[i.val]!
      round.entries[i.val]!.evaluation policies8[i.val]!.pieces[j.val]!
      (1+t*((terminalParameters 8 round.interpolation.values policies8[i.val]!).top-1)) ≤
        (round.entries[i.val]!.rounded : ℝ) :=
  entryRecurrenceAssociation_bound 8 round.interpolation.values coefficient8.values
    policies8[i.val]! round.entries[i.val]!
    (heightCheckedRounds8_recurrence round hr i)
    ((heightCheckedRounds8_association round hr).2 i) (all_policies8_guards i) j t ht

#print axioms certificate8_full_objective_all_real_heights

theorem heightCheckedRounds9_recurrence :
    ∀ round ∈ heightCheckedRounds9, RoundRecurrenceAssociation 9 policies9 round := by
  simp only [heightCheckedRounds9, List.forall_mem_cons]
  exact ⟨round9_01_recurrence_association, round9_02_recurrence_association, round9_03_recurrence_association, round9_04_recurrence_association, round9_05_recurrence_association, round9_06_recurrence_association, by simp⟩

theorem certificate9_full_objective_all_real_heights
    (round : Round) (hr : round ∈ heightCheckedRounds9)
    (i : Fin policies9.size) (j : Fin policies9[i.val]!.pieces.size) (t : ℝ)
    (ht : t ∈ Set.Icc (policies9[i.val]!.pieces[j.val]!.lo : ℝ)
      (policies9[i.val]!.pieces[j.val]!.hi : ℝ)) :
    fullObjectiveReal 9 round.interpolation.values coefficient9.values policies9[i.val]!
      round.entries[i.val]!.evaluation policies9[i.val]!.pieces[j.val]!
      (1+t*((terminalParameters 9 round.interpolation.values policies9[i.val]!).top-1)) ≤
        (round.entries[i.val]!.rounded : ℝ) :=
  entryRecurrenceAssociation_bound 9 round.interpolation.values coefficient9.values
    policies9[i.val]! round.entries[i.val]!
    (heightCheckedRounds9_recurrence round hr i)
    ((heightCheckedRounds9_association round hr).2 i) (all_policies9_guards i) j t ht

#print axioms certificate9_full_objective_all_real_heights

end Waring.Certificate

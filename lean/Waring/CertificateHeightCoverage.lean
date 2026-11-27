import Waring.CertificateHeightApplications

/-!
# The frozen height pieces leave no gaps

The actual rational piece endpoints form a chain from zero to one. This finite
check and a real interval-cover lemma ensure that every normalized real height
is governed by one of the previously verified pieces.
-/

noncomputable section
namespace Waring.Certificate

def PieceChain (lo hi : Q) : List Piece → Prop
  | [] => lo = hi
  | piece :: pieces => piece.lo = lo ∧ piece.lo < piece.hi ∧ PieceChain piece.hi hi pieces

instance (lo hi : Q) (pieces : List Piece) : Decidable (PieceChain lo hi pieces) := by
  induction pieces generalizing lo with
  | nil => unfold PieceChain; infer_instance
  | cons piece pieces ih => unfold PieceChain; infer_instance

theorem pieceChain_covers {pieces : List Piece} {lo hi : Q}
    (hc : PieceChain lo hi pieces) (hlohi : lo < hi) {t : ℝ}
    (ht : t ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    ∃ piece ∈ pieces, t ∈ Set.Icc (piece.lo : ℝ) (piece.hi : ℝ) := by
  induction pieces generalizing lo with
  | nil =>
    have heq : lo = hi := hc
    exact (hlohi.ne heq).elim
  | cons piece pieces ih =>
    rcases hc with ⟨hstart, hlt, hrest⟩
    by_cases hle : t ≤ (piece.hi : ℝ)
    · refine ⟨piece, by simp, ?_⟩
      rw [hstart]
      exact ⟨ht.1, hle⟩
    · have hnext : piece.hi < hi := by
        exact_mod_cast ((lt_of_not_ge hle).trans_le ht.2)
      rcases ih hrest hnext ⟨(lt_of_not_ge hle).le, ht.2⟩ with ⟨p, hp, hb⟩
      exact ⟨p, by simp [hp], hb⟩

theorem policy_pieceChain_covers (p : Policy) (hc : PieceChain 0 1 p.pieces.toList)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin p.pieces.size, t ∈ Set.Icc (p.pieces[i.val]!.lo : ℝ)
      (p.pieces[i.val]!.hi : ℝ) := by
  rcases pieceChain_covers hc (by norm_num) (by simpa using ht) with ⟨piece, hp, hb⟩
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hp)
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa only [getElem!_pos p.pieces i hi, heq] using hb

theorem policies8_piece_chains :
    ∀ i : Fin policies8.size, PieceChain 0 1 policies8[i.val]!.pieces.toList := by decide +kernel

theorem policies9_piece_chains :
    ∀ i : Fin policies9.size, PieceChain 0 1 policies9[i.val]!.pieces.toList := by decide +kernel

theorem certificate8_every_height (round : Round) (hr : round ∈ heightCheckedRounds8)
    (i : Fin policies8.size) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin policies8[i.val]!.pieces.size,
      t ∈ Set.Icc (policies8[i.val]!.pieces[j.val]!.lo : ℝ)
        (policies8[i.val]!.pieces[j.val]!.hi : ℝ) ∧
      let p := policies8[i.val]!
      let params := terminalParameters 8 round.interpolation.values p
      pieceResidualReal 8 p coefficient8.values p.pieces[j.val]!
        params.base params.slope params.scale (1+t*((params.top : ℝ)-1)) ≤
          max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
            (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ) := by
  obtain ⟨j, hj⟩ := policy_pieceChain_covers policies8[i.val]! (policies8_piece_chains i) ht
  exact ⟨j, hj, certificate8_all_real_heights round hr i j t hj⟩

theorem certificate9_every_height (round : Round) (hr : round ∈ heightCheckedRounds9)
    (i : Fin policies9.size) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ j : Fin policies9[i.val]!.pieces.size,
      t ∈ Set.Icc (policies9[i.val]!.pieces[j.val]!.lo : ℝ)
        (policies9[i.val]!.pieces[j.val]!.hi : ℝ) ∧
      let p := policies9[i.val]!
      let params := terminalParameters 9 round.interpolation.values p
      pieceResidualReal 9 p coefficient9.values p.pieces[j.val]!
        params.base params.slope params.scale (1+t*((params.top : ℝ)-1)) ≤
          max (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[0]!.exponent : ℝ)
            (round.entries[i.val]!.evaluation.pieces[j.val]!.endpoints[1]!.exponent : ℝ) := by
  obtain ⟨j, hj⟩ := policy_pieceChain_covers policies9[i.val]! (policies9_piece_chains i) ht
  exact ⟨j, hj, certificate9_all_real_heights round hr i j t hj⟩

#print axioms certificate8_every_height
#print axioms certificate9_every_height
end Waring.Certificate

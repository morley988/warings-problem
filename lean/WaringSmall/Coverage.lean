import WaringSmall.Check
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Soundness of the small-degree conductor certificate

Every accepted union of intervals covers each *real* conductor exponent
between 1 and the chosen upper bound. Endpoints are scaled by the common
denominator used in Check.lean.
-/

namespace WaringSmall

def cellAt (den theta sigma j : ℕ) (u : ℝ) : Prop :=
  let y := 2^j*sigma
  2*y≤den ∧ (j=0 ∨ theta+y≤den) ∧
    ((j*theta+2*y:ℕ):ℝ)≤u ∧ u≤(((j+2)*den-(2^(j+2)-2)*sigma:ℕ):ℝ)

private theorem added_coverage (den theta sigma p j : ℕ) (u : ℝ)
    (hp : (p:ℝ)<u) (hu : u≤(addInterval den theta sigma p j:ℝ)) :
    cellAt den theta sigma j u := by
  unfold addInterval at hu
  dsimp only at hu
  split at hu
  next h =>
    simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at h
    refine ⟨h.1.1.1,h.1.1.2,?_,hu⟩
    exact (show ((j*theta+2*(2^j*sigma):ℕ):ℝ)≤p by exact_mod_cast h.1.2).trans hp.le
  next _ => linarith

private theorem folded_coverage (den theta sigma : ℕ) (L : List ℕ) (p : ℕ) (u : ℝ)
    (hp : (p:ℝ)<u) (hu : u≤((L.foldl (addInterval den theta sigma) p:ℕ):ℝ)) :
    ∃ j∈L, cellAt den theta sigma j u := by
  induction L generalizing p with
  | nil => simp only [List.foldl_nil] at hu; linarith
  | cons j L ih =>
    let n := addInterval den theta sigma p j
    by_cases h : u≤(n:ℝ)
    · exact ⟨j,List.mem_cons_self ..,added_coverage _ _ _ _ _ u hp h⟩
    · obtain ⟨i,hi,hcell⟩ := ih n (lt_of_not_ge h) hu
      exact ⟨i,List.mem_cons_of_mem _ hi,hcell⟩

/-- Continuous coverage in integer-scaled coordinates. At a conductor U,
the final argument of cellAt is U times the common denominator. -/
theorem conduct_covers {k : ℕ} {M z sig : Fr} (hc : conduct k M z sig=true)
    (U : ℝ) (hU : 1<U) (hM : U≤(M.n:ℝ)/M.d) :
    let d := M.d*k*10^6
    let den := d*sig.d
    let theta := (M.n*10^6+M.d*k)*sig.d
    ∃ j, j<k-1 ∧ cellAt den theta (sig.n*d) j (U*den) := by
  let d := M.d*k*10^6
  let den := d*sig.d
  let theta := (M.n*10^6+M.d*k)*sig.d
  let endp := (List.range (k-1)).foldl (addInterval den theta (sig.n*d)) den
  have h := hc
  simp only [conduct,valid,Bool.and_eq_true,decide_eq_true_eq] at h
  have hm : 0<M.d := h.1.1.1.1.1.1.1
  have hs : 0<sig.d := h.1.1.1.1.1.2
  have hk : 2≤k := h.1.1.1.1.2
  have hd : 0<(den:ℝ) := by dsimp [den,d]; positivity
  have hMd : 0<(M.d:ℝ) := by exact_mod_cast hm
  have hh : M.n*den<endp*M.d := h.2
  have hhr : (M.n:ℝ)*(den:ℝ)<(endp:ℝ)*M.d := by exact_mod_cast hh
  have hhi : U*(den:ℝ)≤(endp:ℝ) := by
    have hh' : (U*den)*M.d < (endp:ℝ)*M.d := calc
      (U*den)*M.d = (U*M.d)*den := by ring
      _ ≤ (M.n:ℝ)*den := mul_le_mul_of_nonneg_right ((le_div_iff₀ hMd).1 hM) hd.le
      _ < (endp:ℝ)*M.d := hhr
    exact (lt_of_mul_lt_mul_right hh' hMd.le).le
  have hlo : (den:ℝ)<U*den := by simpa using mul_lt_mul_of_pos_right hU hd
  obtain ⟨i,hi,cell⟩ := folded_coverage den theta (sig.n*d) (List.range (k-1))
    den (U*den) hlo hhi
  exact ⟨i,List.mem_range.mp hi,cell⟩

#print axioms conduct_covers
end WaringSmall

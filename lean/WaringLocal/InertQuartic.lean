import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Exact finite quotients for sums of fourth powers in the unramified
quadratic 2-adic extension. Coordinates use ω²+ω+1=0. -/
namespace WaringLocal.InertQuartic
abbrev Z := ZMod 16
abbrev C := Z × Z
abbrev A := QuadraticAlgebra Z (-1) (-1)

private def dirs : List C := [(0,0),(1,0),(9,0),(0,1),(0,9),(15,15),(7,7)]
private def prodC (p q : C) : C :=
  (p.1*q.1-p.2*q.2,p.1*q.2+p.2*q.1-p.2*q.2)
def fourth (p : C) : C := prodC (prodC p p) (prodC p p)

theorem fourth_coordinates (a : A) : ((a^4).re,(a^4).im) = fourth (a.re,a.im) := by
  rw [show a^4=(a*a)*(a*a) by ring]
  apply Prod.ext <;> simp [fourth,prodC,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul] <;> ring

set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

private theorem dir_mem : ∀ q : C, fourth q ∈ dirs := by decide +kernel
private theorem dir_surj : ∀ d ∈ dirs, ∃ q : C, fourth q=d := by
  decide +kernel

private def masks : List Nat := [1,
  57896044618658097711785492504343976227380855477441316013383516555848211038723,
  58350566026072337080570795787883067429870500024965943125053260047595579082375,
  88320712816618847999803299868885807052777718542599743068564911486235904020367,
  90363416677576684846417580474555323172536474292606013127904026612045387390943,
  108526620101572323760839208991274097635030905860845214222102502589018861993983,
  115792033806397162038426125146221572509647615951079043445706012350371717971967,
  115792089237316195423570985008687907853269984665640564039457584007913129639935]
private def present (n : Nat) (p : C) : Bool :=
  (masks[n]?.getD 0).testBit (p.1.val+16*p.2.val)

private theorem masks_zero : ∀ p : C, present 0 p = true ↔ p=0 := by decide +kernel

private theorem masks_step : ∀ n : Fin 7, ∀ p : C,
    present (n.val+1) p = (dirs.any (fun d => present n.val (p-d))) := by
  decide +kernel

/-- An ordinary sum of exactly n fourth powers in these coordinates. -/
def Represented : Nat → C → Prop
  | 0, p => p = 0
  | n+1, p => ∃ q : C, Represented n (p-fourth q)

theorem represented_iff (n : Nat) (hn : n≤7) (p : C) :
    Represented n p ↔ present n p = true := by
  induction n generalizing p with
  | zero => exact (masks_zero p).symm
  | succ n ih =>
    rw [masks_step ⟨n,by omega⟩ p,List.any_eq_true]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨fourth q,dir_mem q,(ih (by omega) _).mp hq⟩
    · rintro ⟨d,hd,hrest⟩
      obtain ⟨q,rfl⟩ := dir_surj d hd
      exact ⟨q,(ih (by omega) _).mpr hrest⟩

private def coords (a : A) : C := (a.re,a.im)

private theorem coords_add (a b : A) : coords (a+b)=coords a + coords b := rfl

/-- The coordinate recursion is exactly a sum of powers in the quadratic
algebra, including classes with no unit condition imposed. -/
theorem represented_in_algebra (n : Nat) (p : C) :
    Represented n p ↔ ∃ f : Fin n → A, coords (∑ i, f i ^ 4)=p := by
  classical
  induction n generalizing p with
  | zero => simpa [Represented,coords] using (eq_comm (a:=p) (b:=(0,0)))
  | succ n ih =>
    constructor
    · rintro ⟨q,hq⟩
      obtain ⟨g,hg⟩ := (ih _).mp hq
      let a : A := ⟨q.1,q.2⟩
      refine ⟨Fin.cons a g,?_⟩
      rw [Fin.sum_univ_succ,coords_add]
      simp only [Fin.cons_zero,Fin.cons_succ]
      have hpow : coords (a^4)=fourth q := fourth_coordinates a
      rw [hpow,hg]
      exact add_sub_cancel _ _
    · rintro ⟨f,hf⟩
      refine ⟨coords (f 0),(ih _).mpr ⟨fun i => f i.succ,?_⟩⟩
      rw [Fin.sum_univ_succ,coords_add] at hf
      have hz : coords (f 0 ^ 4) = fourth (coords (f 0)) := fourth_coordinates (f 0)
      rw [hz] at hf
      rw [←hf]
      exact (add_sub_cancel_left _ _).symm

theorem six_count : (Finset.univ.filter (fun p : C => present 6 p)).card = 226 := by
  decide +kernel

theorem six_count_exact :
    ∃ s : Finset C, (∀ p, p∈s ↔ Represented 6 p) ∧ s.card=226 := by
  refine ⟨Finset.univ.filter (fun p : C => present 6 p),?_,six_count⟩
  intro p
  simp [represented_iff 6 (by decide) p]

theorem seven_everywhere (p : C) : Represented 7 p := by
  apply (represented_iff 7 (by decide) p).mpr
  exact (by decide +kernel : ∀ x : C, present 7 x = true) p

#print axioms represented_in_algebra
#print axioms six_count_exact
#print axioms seven_everywhere
end WaringLocal.InertQuartic

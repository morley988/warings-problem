import WaringSiegel.WSL3MomentSparseCongruence
import WaringSiegel.WSL3MomentSparseResidues
import WaringSiegel.WSL3MomentSystemPartition

/-!
# The actual sparse modular critical mean

The integer source is partitioned into all p-adic annuli below H, and
then unit residue classes modulo p^c. Each regular class is normalized by
the proved Taylor construction and fed to the native polynomial theorem.
The exceptional class has at most one point. All partition loss is explicit.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

set_option maxHeartbeats 800000

theorem native_sparse_modular_energy_bound (k r p : ℕ)
    (hp : p.Prime) (hr : 1 ≤ r) (hrk : r ≤ k) (hkp : k < p)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ H c L : ℕ, B0 ≤ r*H → 1 ≤ c → τ*(r*H : ℕ) ≤ (c : ℝ) →
        r*H+k*(H+c) ≤ L → ∀ {α : Type*} [Fintype α] (labels : α → ℤ),
        Function.Injective (fun x => (labels x : ZMod (p^H))) →
        ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
        weightedSystemEnergy (wooleyTriangular r)
          (fun x => sparseValue k r (labels x : ZMod (p^L))) w ≤
          C * (1+(H : ℝ)*(p : ℝ)^c)^(2*wooleyTriangular r) *
            (p^(r*H) : ℝ)^δ * (∑ x, w x^2)^wooleyTriangular r := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨A,hA,B0,hmain⟩ := native_system_modular_energy_bound r p hp hr (hrk.trans_lt hkp) hτ hδ
  let C := 1+A
  have hC : 0 < C := by dsimp [C]; linarith
  have hCA : A ≤ C := by dsimp [C]; linarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,B0,?_⟩
  intro H c L hB hc hcscale hL α inst labels hinj w hw
  let s := wooleyTriangular r
  have hs : 1 ≤ s := by
    dsimp [s,wooleyTriangular]
    have : 2 ≤ r*(r+1) := by nlinarith
    omega
  let β := Option (Fin H × Fin (p^c))
  letI : DecidableEq β := Classical.decEq β
  obtain ⟨tag,z,hzero,hreg⟩ := integer_sparse_partition p H c hp hc labels
  let value : α → Fin r → ZMod (p^L) := fun x => sparseValue k r (labels x : ZMod (p^L))
  let mass : ℝ := ∑ x, w x^2
  let D : ℝ := C*(p^(r*H) : ℝ)^δ*mass^s
  have hm : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpbase : (1 : ℝ) ≤ (p : ℝ)^(r*H) := one_le_pow₀ (by exact_mod_cast hp.one_le)
  have hpδ : 1 ≤ (p^(r*H) : ℝ)^δ := Real.one_le_rpow hpbase hδ.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hblock (t : β) :
      weightedSystemEnergy s (fun x : {x // tag x=t} => value x) (fun x => w x) ≤ D := by
    cases t with
    | none =>
      letI : Subsingleton {x // tag x=none} := sparse_partition_zero_subsingleton p H c labels hinj tag hzero
      rw [weightedSystemEnergy_subsingleton s hs]
      calc
        _ ≤ mass^s := pow_le_pow_left₀ (by positivity) (fiber_mass_le tag w none) s
        _ ≤ C*(p^(r*H) : ℝ)^δ*mass^s := by
          have hfactor : 1 ≤ C*(p^(r*H) : ℝ)^δ := one_le_mul_of_one_le_of_one_le hC1 hpδ
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor (pow_nonneg hm s)
    | some t =>
      obtain ⟨e,ξ⟩ := t
      cases isEmpty_or_nonempty {x // tag x=some (e,ξ)} with
      | inl hempty =>
        letI : IsEmpty {x // tag x=some (e,ξ)} := hempty
        rw [weightedSystemEnergy_subsingleton s hs]
        simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_pow (by omega : s ≠ 0)] using hD
      | inr hnonempty =>
        obtain ⟨a,ha⟩ := hnonempty
        have hξ : Nat.Coprime p (ξ.val : ℤ).natAbs := by
          simpa only [Int.natAbs_natCast] using (hreg a e ξ ha).1
        obtain ⟨φ,hφ,hnorm⟩ := sparse_equations_normalize_on_progression
          k r p c (r*H) hp hkp hr hrk (ξ.val : ℤ) hξ
        have hPhi : φ.InPhiTau p (r*H) τ := ⟨c,hφ,hcscale⟩
        have hzinj := sparse_partition_coordinate_injective p H c labels hinj tag z
          (fun x e ξ hx => (hreg x e ξ hx).2) e ξ
        have hnative := hmain H φ hPhi
          (fun x : {x // tag x=some (e,ξ)} => z x) hB hzinj
          (fun x => w x) (fun x => hw x)
        have heq : ∀ x y : Fin s → {x // tag x=some (e,ξ)},
            (∑ i, value (x i)) = (∑ i, value (y i)) →
            (∑ i, fun j => (((φ j).eval (z (x i)) : ℤ) : ZMod (p^(r*H)))) =
              (∑ i, fun j => (((φ j).eval (z (y i)) : ℤ) : ZMod (p^(r*H)))) := by
          intro x y hh
          have hreg' (x : {x // tag x=some (e,ξ)}) :
              labels x=(p : ℤ)^e.val*((ξ.val : ℤ)+(p : ℤ)^c*z x) := (hreg x e ξ x.property).2
          apply hnorm e.val L s (le_trans (by nlinarith [e.isLt]) hL) (fun i => z (x i)) (fun i => z (y i))
          simpa only [value,hreg'] using hh
        calc
          _ ≤ weightedSystemEnergy s
              (fun x : {x // tag x=some (e,ξ)} => fun j => (((φ j).eval (z x) : ℤ) : ZMod (p^(r*H))))
              (fun x => w x) := weightedSystemEnergy_le_of_equations s _ _ heq _ (fun x => hw x)
          _ ≤ A*(p^(r*H) : ℝ)^δ*(∑ x : {x // tag x=some (e,ξ)}, w x^2)^s := hnative
          _ ≤ C*(p^(r*H) : ℝ)^δ*mass^s := by
            gcongr
            exact fiber_mass_le tag w (some (e,ξ))
  have hcard : (Fintype.card β : ℝ)=1+(H : ℝ)*(p : ℝ)^c := by
    simp only [β,Fintype.card_option,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]
    ring
  calc
    weightedSystemEnergy s value w ≤
        (Fintype.card β : ℝ)^(2*s-1)*∑ t : β,
          weightedSystemEnergy s (fun x : {x // tag x=t} => value x) (fun x => w x) :=
      weightedSystemEnergy_partition_le (p^L) r s hs value w tag
    _ ≤ (Fintype.card β : ℝ)^(2*s-1)*∑ _t : β, D := by gcongr with t; exact hblock t
    _ = (Fintype.card β : ℝ)^(2*s)*D := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc,← pow_succ]
      congr 2
      omega
    _ = _ := by rw [hcard]; dsimp [D,mass]; ring

#print axioms native_sparse_modular_energy_bound

end WaringSiegel.WSL3

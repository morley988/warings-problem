import WaringLinear.ShiftAveraging
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-! # Exact interval van der Corput A-step with an arithmetic shift -/
noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace WaringLinear

/-- A periodic shift with step B in an interval of X integers. The
diagonal contributes X, independently of B, whenever BH≤X. This is the
source of the conductor-menu diagonal width without an extra radical loss. -/
theorem rational_interval_A (X B H : ℕ) (hX : 0<X) (hH : 0<H) (hBH : B*H≤X)
    (f : ℤ→ℂ) (hs : ∀x∉Finset.Icc 1 (X:ℤ),f x=0) (hu : ∀x,‖f x‖≤1) :
    (H:ℝ)*‖∑x∈Finset.Icc 1 (X:ℤ),f x‖^2 ≤
      (2*(X:ℝ))*((X:ℝ)+∑h∈(Finset.Icc (-(H:ℤ)) H).erase 0,
        ‖∑x∈Finset.Icc 1 (X:ℤ),f (x+B*h)*conj (f x)‖) := by
  classical
  let I := Finset.Icc 1 (X:ℤ)
  let S := Finset.Icc 1 (H:ℤ)
  let D := Finset.Icc (-(H:ℤ)) H
  let Ω := Finset.Icc (1-(B:ℤ)*H) (X:ℤ)
  let φ : ℤ→+ℤ := AddMonoidHom.mulLeft (B:ℤ)
  have H0 : 0<(H:ℤ) := by exact_mod_cast hH
  have X0 : 0<(X:ℤ) := by exact_mod_cast hX
  have B0 : 0≤(B:ℤ) := by positivity
  have aS : S.Nonempty := ⟨1,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩
  have cov (s:ℤ) (hs:s∈S) (x:ℤ) (hx:x∈I) : x-φ s∈Ω := by
    obtain ⟨hs1,hs2⟩ := Finset.mem_Icc.mp hs
    obtain ⟨hx1,hx2⟩ := Finset.mem_Icc.mp hx
    change x-(B:ℤ)*s∈Finset.Icc _ _
    exact Finset.mem_Icc.mpr ⟨by nlinarith only [hx1,mul_le_mul_of_nonneg_left hs2 B0],
      by nlinarith only [hx2,mul_nonneg B0 (by omega:0≤s)]⟩
  have dif (s:ℤ) (hs:s∈S) (t:ℤ) (ht:t∈S) : s-t∈D := by
    obtain ⟨_,_⟩ := Finset.mem_Icc.mp hs
    obtain ⟨_,_⟩ := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have raw := shift_average_sq I Ω S D φ f hs aS cov dif
  have cardS : S.card=H := by simp [S,Int.card_Icc]
  have cardI : I.card=X := by simp [I,Int.card_Icc]
  have cardΩ : Ω.card=X+B*H := by
    simp only [Ω,Int.card_Icc]
    rw [show (X:ℤ)+1-(1-(B:ℤ)*H)=(X:ℤ)+B*H by ring]
    exact_mod_cast Int.toNat_natCast (X+B*H)
  let c (h:ℤ) := ‖∑x∈I,f (x+(B:ℤ)*h)*conj (f x)‖
  have diag : c 0≤X := by
    change ‖∑x∈I,f (x+(B:ℤ)*0)*conj (f x)‖≤_
    calc
      _ ≤ ∑x∈I,‖f (x+(B:ℤ)*0)*conj (f x)‖ := norm_sum_le _ _
      _ ≤ ∑_∈I,(1:ℝ) := Finset.sum_le_sum (fun x _ => by
        simp only [mul_zero,add_zero,norm_mul,RCLike.norm_conj]
        nlinarith only [mul_le_mul (hu x) (hu x) (norm_nonneg _) zero_le_one])
      _ = _ := by simp [cardI]
  have mem : (0:ℤ)∈D := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  change (S.card:ℝ)*_≤(Ω.card:ℝ)*(∑h∈D,c h) at raw
  rw [cardS,cardΩ,←Finset.sum_erase_add _ _ mem] at raw
  have hcard : ((X+B*H:ℕ):ℝ)≤2*X := by exact_mod_cast (by omega : X+B*H≤2*X)
  apply raw.trans
  apply mul_le_mul hcard _ (by positivity) (by positivity)
  linarith only [diag]

/-- A uniform correlation bound yields the classical square-root transform,
with the diagonal loss H^{-1} explicit. -/
theorem rational_interval_A_uniform (X B H : ℕ) (hX : 0<X) (hH : 0<H) (hBH:B*H≤X)
    (f:ℤ→ℂ) (hs:∀x∉Finset.Icc 1 (X:ℤ),f x=0) (hu:∀x,‖f x‖≤1)
    (Y:ℝ) (hY:0≤Y)
    (hOff:∀h∈(Finset.Icc (-(H:ℤ)) H).erase 0,
      ‖∑x∈Finset.Icc 1 (X:ℤ), f (x+B*h)*conj (f x)‖≤Y) :
    ‖∑x∈Finset.Icc 1 (X:ℤ),f x‖^2≤2*(X:ℝ)^2/H+4*X*Y := by
  have raw := rational_interval_A X B H hX hH hBH f hs hu
  let D := (Finset.Icc (-(H:ℤ)) H).erase 0
  have mem : (0:ℤ)∈Finset.Icc (-(H:ℤ)) H := by simp
  have hcard : D.card=2*H := by
    rw [show D=(Finset.Icc (-(H:ℤ)) H).erase 0 from rfl,Finset.card_erase_of_mem mem,Int.card_Icc]
    omega
  have ho := Finset.sum_le_sum hOff
  rw [Finset.sum_const,hcard,nsmul_eq_mul] at ho
  push_cast at ho
  have hh : 0 < (H:ℝ) := by exact_mod_cast hH
  have h := raw.trans (mul_le_mul_of_nonneg_left (add_le_add_left ho (X:ℝ)) (by positivity))
  calc
    _ ≤ (2*(X:ℝ)*(X+2*H*Y))/H := (le_div_iff₀ hh).mpr (by linarith only [h])
    _ = _ := by field_simp; ring

#print axioms rational_interval_A
#print axioms rational_interval_A_uniform
end WaringLinear

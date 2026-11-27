import Waring.PolicyCompletionPowerClasses
import Waring.CubicRootDivisorClasses

/-!
# Joint cubic and power denominator classes in the shallow estimate

The exact gcd reduction first sums the cube divisibility classes and then
the weighted power classes. This supplies the source exponent 2/d without
the stronger separation condition used in the deep basic estimate.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowClasses
open CubicDivisorClasses PolicyCompletionPowerClasses

theorem gcd_mul_reduction {q m : ℕ} (hq : 0<q) (h : ℕ) :
    q.gcd (h*m)=q.gcd m*((q/q.gcd m).gcd h) := by
  let u := q.gcd m
  have hu : 0<u := Nat.gcd_pos_of_pos_left m hq
  have hqeq : u*(q/u)=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hmeq : u*(m/u)=m := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hcop : (m/u).Coprime (q/u) := (Nat.coprime_div_gcd_div_gcd hu).symm
  calc
    q.gcd (h*m)=(u*(q/u)).gcd (u*(h*(m/u))) := by rw [hqeq,← mul_assoc,mul_comm u h,mul_assoc,hmeq]
    _ = u*((q/u).gcd (h*(m/u))) := Nat.gcd_mul_left _ _ _
    _ = _ := by rw [Nat.Coprime.gcd_mul_right_cancel_right h hcop]

theorem gcd_ratio_reduction {q m : ℕ} (hq : 0<q) (h : ℕ) :
    ((q.gcd (h*m) : ℕ) : ℝ)/q=
      ((((q/q.gcd m).gcd h : ℕ) : ℝ)/((q/q.gcd m : ℕ) : ℝ)) := by
  have hu : 0<q.gcd m := Nat.gcd_pos_of_pos_left m hq
  have hv : 0<q/q.gcd m := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left _ _)) hu
  have hqeq : (q.gcd m : ℝ)*((q/q.gcd m : ℕ) : ℝ)=q := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left q m)
  rw [gcd_mul_reduction hq,Nat.cast_mul,← hqeq]
  have huR : (q.gcd m : ℝ)≠0 := by exact_mod_cast hu.ne'
  field_simp

theorem gcd_cube_sum (q H : ℕ) (hq : 0<q) (hH : 0<H) {B : ℝ} (hB : 0≤B) :
    (∑h∈Finset.Icc 1 H,(((q.gcd (h^3) : ℕ) : ℝ)/q)/(1+B*(h : ℝ)^3))≤
      (q.divisors.card : ℝ)*(H : ℝ)/((q : ℝ)+B*(H : ℝ)^3*q)^(1/3 : ℝ)*(1+Real.log H) := by
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  let weight : ℕ→ℕ→ℝ := fun u h=>if u∣h^3 then ((u : ℝ)/q)/(1+B*(h : ℝ)^3) else 0
  have hw : ∀u h,0≤weight u h := by intro u h; dsimp [weight]; split_ifs <;> positivity
  have hpoint (h : ℕ) :
      (((q.gcd (h^3) : ℕ) : ℝ)/q)/(1+B*(h : ℝ)^3)≤∑u∈q.divisors,weight u h := by
    have hu : q.gcd (h^3)∈q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hq.ne'⟩
    have hh := Finset.single_le_sum (fun u _=>hw u h) hu
    simpa only [weight,if_pos (Nat.gcd_dvd_right q (h^3))] using hh
  have hclass (u : ℕ) : (∑h∈Finset.Icc 1 H,weight u h)=originalClassContribution H u B q := by
    dsimp [weight,originalClassContribution]
    rw [← Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  calc
    _ ≤ ∑h∈Finset.Icc 1 H,∑u∈q.divisors,weight u h := Finset.sum_le_sum fun h _=>hpoint h
    _ = ∑u∈q.divisors,originalClassContribution H u B q := by rw [Finset.sum_comm]; simp_rw [hclass]
    _ ≤ ∑_u∈q.divisors,(H : ℝ)/((q : ℝ)+B*(H : ℝ)^3*q)^(1/3 : ℝ)*(1+Real.log H) := by
      apply Finset.sum_le_sum
      intro u hu
      exact originalClassContribution_cube_root hH (Nat.pos_of_mem_divisors hu) hB hqR
        (by exact_mod_cast Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hu))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem weighted_gcd_power_sum (q N d : ℕ) (hq : 0<q) (hd : 6≤d)
    {L : ℝ} (hL : (q : ℝ)≤L) :
    (∑g∈Finset.Icc 1 N,((q.gcd (g^d) : ℕ) : ℝ)^(1/3 : ℝ)/((g : ℝ)^2*L^(1/3 : ℝ)))≤
      2*(q.divisors.card : ℝ)/L^(2/(d : ℝ)) := by
  have hL0 : 0≤L := (show (0 : ℝ)≤q by positivity).trans hL
  let weight : ℕ→ℕ→ℝ := fun u g=>if u∣g^d then
    (u : ℝ)^(1/3 : ℝ)/((g : ℝ)^2*L^(1/3 : ℝ)) else 0
  have hw : ∀u g,0≤weight u g := by intro u g; dsimp [weight]; split_ifs <;> positivity
  have hpoint (g : ℕ) :
      ((q.gcd (g^d) : ℕ) : ℝ)^(1/3 : ℝ)/((g : ℝ)^2*L^(1/3 : ℝ))≤
        ∑u∈q.divisors,weight u g := by
    have hu : q.gcd (g^d)∈q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,hq.ne'⟩
    have hh := Finset.single_le_sum (fun u _=>hw u g) hu
    simpa only [weight,if_pos (Nat.gcd_dvd_right q (g^d))] using hh
  calc
    _ ≤ ∑g∈Finset.Icc 1 N,∑u∈q.divisors,weight u g := Finset.sum_le_sum fun g _=>hpoint g
    _ = ∑u∈q.divisors,∑g∈Finset.Icc 1 N,weight u g := Finset.sum_comm
    _ ≤ ∑_u∈q.divisors,2/L^(2/(d : ℝ)) := by
      apply Finset.sum_le_sum
      intro u hu
      have huL : (u : ℝ)≤L :=
        (show (u : ℝ)≤q by exact_mod_cast Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hu)).trans hL
      simpa only [weight,← Finset.sum_filter] using
        weighted_powerClass_bound hd (Nat.pos_of_mem_divisors hu) N huL
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- The complete joint denominator average, including a real error taper.
All gcd classes, divisibility multiplicities and the 2/d saving are proved. -/
theorem gcd_cube_power_sum (q H N d : ℕ) (hq : 0<q) (hH : 0<H) (hd : 6≤d)
    {B : ℝ} (hB : 0≤B) :
    (∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*
      ∑h∈Finset.Icc 1 H,(((q.gcd (h^3*g^d) : ℕ) : ℝ)/q)/(1+B*(h : ℝ)^3))≤
      2*(q.divisors.card : ℝ)^2*(H : ℝ)*(1+Real.log H)/
        ((q : ℝ)+B*(H : ℝ)^3*q)^(2/(d : ℝ)) := by
  let L : ℝ := (q : ℝ)+B*(H : ℝ)^3*q
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hqL : (q : ℝ)≤L := by
    dsimp [L]
    exact le_add_of_nonneg_right (by positivity)
  have hLp : 0<L := hqR.trans_le hqL
  have hlog : 0≤1+Real.log H := by
    have hh := Real.log_nonneg (show (1 : ℝ)≤H by exact_mod_cast hH)
    linarith
  let K : ℝ := (q.divisors.card : ℝ)*(H : ℝ)*(1+Real.log H)
  have hK : 0≤K := by dsimp [K]; positivity
  have hpoint (g : ℕ) :
      (∑h∈Finset.Icc 1 H,(((q.gcd (h^3*g^d) : ℕ) : ℝ)/q)/(1+B*(h : ℝ)^3))≤
        K*((q.gcd (g^d) : ℕ) : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ) := by
    let u := q.gcd (g^d)
    let v := q/u
    have hu : 0<u := Nat.gcd_pos_of_pos_left _ hq
    have hv : 0<v := Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left _ _)) hu
    have huR : (0 : ℝ)<u := by exact_mod_cast hu
    have hvR : 0<(v : ℝ) := by exact_mod_cast hv
    have hvdiv : v∣q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    have hcard : (v.divisors.card : ℝ)≤q.divisors.card := by
      exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hq.ne' hvdiv)
    have hvr : (v : ℝ)=(q : ℝ)/(u : ℝ) := by
      apply (eq_div_iff huR.ne').mpr
      exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left q (g^d))
    have hden : (v : ℝ)+B*(H : ℝ)^3*v=L/(u : ℝ) := by rw [hvr]; dsimp [L]; ring
    have hroot : 1/((v : ℝ)+B*(H : ℝ)^3*v)^(1/3 : ℝ)=
        (u : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ) := by
      rw [hden,Real.div_rpow hLp.le huR.le]
      field_simp
    calc
      _ = ∑h∈Finset.Icc 1 H,((((v.gcd (h^3) : ℕ) : ℝ)/v)/(1+B*(h : ℝ)^3)) := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [gcd_ratio_reduction hq]
      _ ≤ (v.divisors.card : ℝ)*(H : ℝ)/((v : ℝ)+B*(H : ℝ)^3*v)^(1/3 : ℝ)*(1+Real.log H) :=
        gcd_cube_sum v H hv hH hB
      _ ≤ (q.divisors.card : ℝ)*(H : ℝ)/((v : ℝ)+B*(H : ℝ)^3*v)^(1/3 : ℝ)*(1+Real.log H) := by
        gcongr
      _ = K*((u : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ)) := by
        calc
          _ = K*(1/((v : ℝ)+B*(H : ℝ)^3*v)^(1/3 : ℝ)) := by dsimp [K]; ring
          _ = _ := by rw [hroot]
      _ = _ := by dsimp [u]; ring
  calc
    _ ≤ ∑g∈Finset.Icc 1 N,(1/(g : ℝ)^2)*(K*((q.gcd (g^d) : ℕ) : ℝ)^(1/3 : ℝ)/L^(1/3 : ℝ)) :=
      Finset.sum_le_sum fun g _=>mul_le_mul_of_nonneg_left (hpoint g) (by positivity)
    _ = K*∑g∈Finset.Icc 1 N,((q.gcd (g^d) : ℕ) : ℝ)^(1/3 : ℝ)/((g : ℝ)^2*L^(1/3 : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ ≤ K*(2*(q.divisors.card : ℝ)/L^(2/(d : ℝ))) :=
      mul_le_mul_of_nonneg_left (weighted_gcd_power_sum q N d hq hd hqL) hK
    _ = _ := by dsimp [K,L]; ring

#print axioms gcd_mul_reduction
#print axioms gcd_cube_power_sum
end Waring.PolicyCompletionShallowClasses

import Waring.RestrictedSmoothBlockMoments

/-! # Restricted smooth means with a freely chosen ordered-block scale -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

/-- All arithmetic, Holder, arc changes of variables and complete shorter
moments are discharged. Only the genuine admissible exponent and explicit
numeric scale/separation conditions enter this restricted mean estimate. -/
theorem smooth_arcs_admissible_unoptimized {k s : ℕ} (hs : 1 ≤ s) {lam B ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ S : Finset ℕ+,∀ Q δ R M : ℝ,
      1 ≤ Q → 0 ≤ δ → 1 ≤ R → R ≤ P^η → 1 ≤ M → M*R ≤ P →
      (∀ q ∈ S,(q : ℝ) ≤ Q) → (∀ q ∈ S,(q : ℝ) ≤ P^B) →
      (∀ b ∈ orderedBlocks M R,4*Q*((b.2 : ℝ)^k*δ) ≤ 1) →
      (∑ q ∈ S,rationalArcSum (q : ℕ) (fun x => ‖smoothWeyl k P R x‖^s) δ) ≤
        C*P^ε*(Q*δ*M^s+(M*R)^s*(P/M)^lam/M^k) := by
  obtain ⟨A,hA,hred⟩ := smooth_arcs_reduction_epsilon k hs hB (half_pos hε)
  obtain ⟨η,hη,D,hD,hbound⟩ := weighted_blockMomentSum_epsilon hs hadm hlam (half_pos hε)
  refine ⟨η,hη,A*(1+D),by positivity,?_⟩
  intro P hP S Q δ R M hQ1 hδ hR hRP hM hMR hQ hqP hsep
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hX0 : 0 ≤ Q*δ*M^s := by positivity
  have hY0 : 0 ≤ (M*R)^s*(P/M)^lam/M^k := by positivity
  have hp : P^(ε/2) ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hid : P^(ε/2)*P^(ε/2)=P^ε := by rw [← Real.rpow_add hPp,add_halves]
  have hweighted : (M*R)^(s-1)*blockMomentSum k s P R M ≤
      D*P^(ε/2)*((M*R)^s*(P/M)^lam/M^k) := by
    convert hbound P hP R hR hRP M hM hMR using 1 <;> ring
  have hcoeff : Q*δ*M^s+D*((M*R)^s*(P/M)^lam/M^k) ≤
      (1+D)*(Q*δ*M^s+(M*R)^s*(P/M)^lam/M^k) := by
    nlinarith [mul_nonneg hD.le hX0]
  calc
    _ ≤ A*P^(ε/2)*(Q*δ*M^s+(M*R)^(s-1)*blockMomentSum k s P R M) :=
      hred P hP S Q δ R M hQ1 hδ hR hM hMR hQ hqP hsep
    _ ≤ A*P^(ε/2)*(Q*δ*M^s+D*P^(ε/2)*((M*R)^s*(P/M)^lam/M^k)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hweighted _) (by positivity)
    _ = A*P^(ε/2)*(Q*δ*M^s)+A*D*(P^(ε/2)*P^(ε/2))*((M*R)^s*(P/M)^lam/M^k) := by ring
    _ = A*P^(ε/2)*(Q*δ*M^s)+A*D*P^ε*((M*R)^s*(P/M)^lam/M^k) := by rw [hid]
    _ ≤ A*P^ε*(Q*δ*M^s)+A*D*P^ε*((M*R)^s*(P/M)^lam/M^k) := by
      gcongr
    _ = A*P^ε*(Q*δ*M^s+D*((M*R)^s*(P/M)^lam/M^k)) := by ring
    _ ≤ A*P^ε*((1+D)*(Q*δ*M^s+(M*R)^s*(P/M)^lam/M^k)) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = _ := by ring

#print axioms smooth_arcs_admissible_unoptimized
end Waring.RestrictedSmoothArcs

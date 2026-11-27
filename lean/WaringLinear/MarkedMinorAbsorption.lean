import WaringLinear.FieldDifferencingOrder

/-! # Paying a field moment defect on the marked roots

One ordinary factor is retained for the comparison on major arcs. Each
of the remaining spare factors uses the pointwise estimate on the
restricted sum, available from the bilinear rank-one argument. -/
noncomputable section
open MeasureTheory WaringSiegel WaringSiegel.WSL2 WaringEnvelope
open scoped NumberField BigOperators
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

/-- Finite-scale absorption from a saving on d marked factors and a
trivial estimate on one ordinary factor. -/
theorem TraceSumFamily.marked_minor_absorb (W : TraceSumFamily K) (k r d X : ℕ)
    (he : Even (r+d+1)) (M : Set (ArchimedeanTraceTorus K)) (hM : MeasurableSet M)
    (C B A D ρ E : ℝ) (hX : 1≤X) (hC : 0≤C) (hB : 0≤B) (hD : 0≤D)
    (hpaid : E≤d*ρ)
    (marked : ∀ q∈Mᶜ, ‖W.restricted k X q‖≤C*(X:ℝ)^(1-ρ))
    (ordinary : ∀ q∈Mᶜ, ‖W.ordinary k X q‖≤B*X)
    (major : (∫ q in M, ‖W.ordinary k X q‖^(r+d+1) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+d+1-k))
    (old : (∫ q, ‖W.restricted k X q‖^r ∂traceHaar)≤D*(X:ℝ)^((r:ℝ)-k+E)) :
    (∫ q, ‖W.restricted k X q‖^(r+d+1) ∂traceHaar)≤
      2*((2:ℝ)^(r+d+1)*A+B*C^d*D)*(X:ℝ)^((r:ℝ)+d+1-k) := by
  let F := fun q => ‖W.restricted k X q‖
  let f := fun q => ‖W.ordinary k X q‖
  have hc (w : Fin (W.count X) → ℂ) : Continuous (traceWeylSum k (W.point X) w) :=
    (continuous_frequencySum (fun i => integerCoordinates K ((W.point X i)^k)) w).comp
      (archimedeanTraceTorusContinuousAddEquiv (K:=K)).continuous
  have hF : Continuous F := (hc _).norm
  have hf : Continuous f := (hc _).norm
  have hi (s : ℕ) : Integrable (fun q => F q^s) traceHaar :=
    (hF.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (s : ℕ) : Integrable (fun q => f q^s) traceHaar :=
    (hf.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : Integrable (fun q => f q*F q^(r+d)) traceHaar :=
    (hf.mul (hF.pow _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨s,hs⟩ := he
  have h1 : 2*((s-1)+1)=r+d+1 := by omega
  have h2 : 2*(s-1)+1=r+d := by omega
  have hsup := trace_even_moment_le_one_mixed k (W.point X) (W.small X) (W.full X)
    (W.nonnegative X) (W.nested X) (s-1)
  rw [h1,h2] at hsup
  have hbase : (1:ℝ)≤X := by exact_mod_cast hX
  have hp : (0:ℝ)<X := zero_lt_one.trans_le hbase
  have habs := absorb_mixed_moment traceHaar M hM F f (fun q => norm_nonneg _)
    (fun q => norm_nonneg _) r d (C*(X:ℝ)^(1-ρ)) (B*X) (by positivity)
    marked ordinary (hi _) (hn _) (hi _) hm hsup
  have hsub : (∫ q in Mᶜ, F q^r ∂traceHaar)≤D*(X:ℝ)^((r:ℝ)-k+E) :=
    (setIntegral_le_integral (hi r) (Filter.Eventually.of_forall
      (fun q => pow_nonneg (norm_nonneg _) r))).trans old
  have hpowers : (X:ℝ)*(((X:ℝ)^(1-ρ))^d)*(X:ℝ)^((r:ℝ)-k+E) ≤
      (X:ℝ)^((r:ℝ)+d+1-k) := by
    rw [← Real.rpow_natCast ((X:ℝ)^(1-ρ)) d, ← Real.rpow_mul hp.le]
    nth_rw 1 [← Real.rpow_one (X:ℝ)]
    rw [← Real.rpow_add hp,← Real.rpow_add hp]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    linarith only [hpaid]
  have hscaled : (B*X)*(C*(X:ℝ)^(1-ρ))^d*(D*(X:ℝ)^((r:ℝ)-k+E)) ≤
      B*C^d*D*(X:ℝ)^((r:ℝ)+d+1-k) := by
    rw [mul_pow]
    calc
      _ = (B*C^d*D)*((X:ℝ)*(((X:ℝ)^(1-ρ))^d)*(X:ℝ)^((r:ℝ)-k+E)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpowers (by positivity)
  have ha := mul_le_mul_of_nonneg_left major (by positivity : 0≤(2:ℝ)^(r+d+1))
  have hb := (mul_le_mul_of_nonneg_left hsub
    (by positivity : 0≤(B*X)*(C*(X:ℝ)^(1-ρ))^d)).trans hscaled
  change (∫ q, F q^(r+d+1) ∂traceHaar) ≤ _
  change (2:ℝ)^(r+d+1)*(∫ q in M, f q^(r+d+1) ∂traceHaar)≤_ at ha
  linarith only [habs,ha,hb]

/-- The constants in this loss-free trace moment may depend on the
selected cutoff and on the constants in the broad-arc estimates. -/
def uniformMarkedMomentAt (W : TraceSumFamily K) (k r a : ℕ) (ρ : ℝ) : Prop :=
  ∀ (M : ℕ → Set (ArchimedeanTraceTorus K)) (A B C : ℝ),
    (∀ X, MeasurableSet (M X)) → 0≤B → 0≤C →
    (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.restricted k X q‖≤C*(X:ℝ)^(1-ρ)) →
    (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.ordinary k X q‖≤B*X) →
    (∀ X : ℕ, 1≤X → (∫ q in M X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)) →
    ∃ E : ℝ, ∀ X : ℕ, 1≤X → (∫ q, ‖W.restricted k X q‖^(r+a) ∂traceHaar)≤E*(X:ℝ)^((r:ℝ)+a-k)

theorem cutoff_marked_loss_free_at (W : ℝ → TraceSumFamily K) (k r a : ℕ) (x ρ : ℝ)
    (er : Even r) (ea : Even a) (ha : 0<a) (had : cutoffAdmissible W k r x)
    (gap : (k:ℝ)*x<((a:ℝ)-1)*ρ) :
    ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMarkedMomentAt (W η) k r a ρ := by
  let ε := (((a:ℝ)-1)*ρ-k*x)/2
  have hε : 0<ε := by unfold ε;linarith
  obtain ⟨η₀,hη₀,hwin⟩ := had ε hε
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hle M A B C hM hB hC hmarked hbox hmajor
  obtain ⟨D,hD,hold⟩ := hwin η hη hle
  have hd : r+(a-1)+1=r+a := by omega
  have had' : ((a-1:ℕ):ℝ)=(a:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤a),Nat.cast_one]
  have hexp : (r:ℝ)+((a-1:ℕ):ℝ)+1-k=(r:ℝ)+a-k := by rw [had'];ring
  refine ⟨2*((2:ℝ)^(r+a)*A+B*C^(a-1)*D),?_⟩
  intro X hX
  have h := (W η).marked_minor_absorb k r (a-1) X (hd ▸ er.add ea) (M X) (hM X)
    C B A D ρ (k*x+ε) hX hC hB hD (by rw [had'];unfold ε;linarith)
    (hmarked X hX) (hbox X hX) (by simpa only [hd,hexp] using hmajor X hX)
    (by simpa only [add_assoc] using hold X hX)
  simpa only [hd,hexp] using h

#print axioms TraceSumFamily.marked_minor_absorb
#print axioms cutoff_marked_loss_free_at
end WaringLinear

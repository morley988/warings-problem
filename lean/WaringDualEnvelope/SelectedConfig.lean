import WaringDualEnvelope.AllDegrees
import WaringEnvelope.TerminalCosts

/-! # Simple size constraints on the selected numerical menus -/
namespace WaringDualEnvelope
open WaringEnvelope

def SizeFacts (c : WaringDualEnvelope.Config) : Prop :=
  T≤20*c.heightTop ∧ 2*c.heightTop≤T ∧ 0<(fee c.toConfig).1 ∧
  0<(fee c.toConfig).2 ∧ (fee c.toConfig).1≤(fee c.toConfig).2 ∧
  (c.last=0 → c.first=1000000000000)

instance (c : WaringDualEnvelope.Config) : Decidable (SizeFacts c) := by
  unfold SizeFacts; infer_instance

theorem selected_6874 (k : ℕ) (hk : 21≤k) :
    ∃ c : WaringDualEnvelope.Config, c.first≤k ∧ (c.last=0 ∨ k≤c.last) ∧
      SizeFacts c ∧ WaringDualEnvelope.Certified c (6874*D/1000) := by
  by_cases hBand00 : k ≤ 33
  · exact ⟨Band00.cfg, by change 21 ≤ _; omega, Or.inr hBand00, by decide +kernel, Band00.checked⟩
  by_cases hBand01 : k ≤ 54
  · exact ⟨Band01.cfg, by change 34 ≤ _; omega, Or.inr hBand01, by decide +kernel, Band01.checked⟩
  by_cases hBand02 : k ≤ 88
  · exact ⟨Band02.cfg, by change 55 ≤ _; omega, Or.inr hBand02, by decide +kernel, Band02.checked⟩
  by_cases hBand03 : k ≤ 142
  · exact ⟨Band03.cfg, by change 89 ≤ _; omega, Or.inr hBand03, by decide +kernel, Band03.checked⟩
  by_cases hBand04 : k ≤ 228
  · exact ⟨Band04.cfg, by change 143 ≤ _; omega, Or.inr hBand04, by decide +kernel, Band04.checked⟩
  by_cases hBand05 : k ≤ 366
  · exact ⟨Band05.cfg, by change 229 ≤ _; omega, Or.inr hBand05, by decide +kernel, Band05.checked⟩
  by_cases hBand06 : k ≤ 587
  · exact ⟨Band06.cfg, by change 367 ≤ _; omega, Or.inr hBand06, by decide +kernel, Band06.checked⟩
  by_cases hBand07 : k ≤ 940
  · exact ⟨Band07.cfg, by change 588 ≤ _; omega, Or.inr hBand07, by decide +kernel, Band07.checked⟩
  by_cases hBand08 : k ≤ 1505
  · exact ⟨Band08.cfg, by change 941 ≤ _; omega, Or.inr hBand08, by decide +kernel, Band08.checked⟩
  by_cases hBand09 : k ≤ 2409
  · exact ⟨Band09.cfg, by change 1506 ≤ _; omega, Or.inr hBand09, by decide +kernel, Band09.checked⟩
  by_cases hBand10 : k ≤ 3856
  · exact ⟨Band10.cfg, by change 2410 ≤ _; omega, Or.inr hBand10, by decide +kernel, Band10.checked⟩
  by_cases hBand11 : k ≤ 6171
  · exact ⟨Band11.cfg, by change 3857 ≤ _; omega, Or.inr hBand11, by decide +kernel, Band11.checked⟩
  by_cases hBand12 : k ≤ 9875
  · exact ⟨Band12.cfg, by change 6172 ≤ _; omega, Or.inr hBand12, by decide +kernel, Band12.checked⟩
  by_cases hBand13 : k ≤ 15801
  · exact ⟨Band13.cfg, by change 9876 ≤ _; omega, Or.inr hBand13, by decide +kernel, Band13.checked⟩
  by_cases hBand14 : k ≤ 25283
  · exact ⟨Band14.cfg, by change 15802 ≤ _; omega, Or.inr hBand14, by decide +kernel, Band14.checked⟩
  by_cases hBand15 : k ≤ 40454
  · exact ⟨Band15.cfg, by change 25284 ≤ _; omega, Or.inr hBand15, by decide +kernel, Band15.checked⟩
  by_cases hBand16 : k ≤ 64728
  · exact ⟨Band16.cfg, by change 40455 ≤ _; omega, Or.inr hBand16, by decide +kernel, Band16.checked⟩
  by_cases hBand17 : k ≤ 103566
  · exact ⟨Band17.cfg, by change 64729 ≤ _; omega, Or.inr hBand17, by decide +kernel, Band17.checked⟩
  by_cases hBand18 : k ≤ 165707
  · exact ⟨Band18.cfg, by change 103567 ≤ _; omega, Or.inr hBand18, by decide +kernel, Band18.checked⟩
  by_cases hBand19 : k ≤ 265132
  · exact ⟨Band19.cfg, by change 165708 ≤ _; omega, Or.inr hBand19, by decide +kernel, Band19.checked⟩
  by_cases hBand20 : k ≤ 424212
  · exact ⟨Band20.cfg, by change 265133 ≤ _; omega, Or.inr hBand20, by decide +kernel, Band20.checked⟩
  by_cases hBand21 : k ≤ 678740
  · exact ⟨Band21.cfg, by change 424213 ≤ _; omega, Or.inr hBand21, by decide +kernel, Band21.checked⟩
  by_cases hBand22 : k ≤ 1085985
  · exact ⟨Band22.cfg, by change 678741 ≤ _; omega, Or.inr hBand22, by decide +kernel, Band22.checked⟩
  by_cases hBand23 : k ≤ 1737577
  · exact ⟨Band23.cfg, by change 1085986 ≤ _; omega, Or.inr hBand23, by decide +kernel, Band23.checked⟩
  by_cases hBand24 : k ≤ 2780124
  · exact ⟨Band24.cfg, by change 1737578 ≤ _; omega, Or.inr hBand24, by decide +kernel, Band24.checked⟩
  by_cases hBand25 : k ≤ 4448200
  · exact ⟨Band25.cfg, by change 2780125 ≤ _; omega, Or.inr hBand25, by decide +kernel, Band25.checked⟩
  by_cases hBand26 : k ≤ 7117121
  · exact ⟨Band26.cfg, by change 4448201 ≤ _; omega, Or.inr hBand26, by decide +kernel, Band26.checked⟩
  by_cases hBand27 : k ≤ 11387395
  · exact ⟨Band27.cfg, by change 7117122 ≤ _; omega, Or.inr hBand27, by decide +kernel, Band27.checked⟩
  by_cases hBand28 : k ≤ 18219833
  · exact ⟨Band28.cfg, by change 11387396 ≤ _; omega, Or.inr hBand28, by decide +kernel, Band28.checked⟩
  by_cases hBand29 : k ≤ 29151734
  · exact ⟨Band29.cfg, by change 18219834 ≤ _; omega, Or.inr hBand29, by decide +kernel, Band29.checked⟩
  by_cases hBand30 : k ≤ 46642776
  · exact ⟨Band30.cfg, by change 29151735 ≤ _; omega, Or.inr hBand30, by decide +kernel, Band30.checked⟩
  by_cases hBand31 : k ≤ 74628443
  · exact ⟨Band31.cfg, by change 46642777 ≤ _; omega, Or.inr hBand31, by decide +kernel, Band31.checked⟩
  by_cases hBand32 : k ≤ 119405510
  · exact ⟨Band32.cfg, by change 74628444 ≤ _; omega, Or.inr hBand32, by decide +kernel, Band32.checked⟩
  by_cases hBand33 : k ≤ 191048817
  · exact ⟨Band33.cfg, by change 119405511 ≤ _; omega, Or.inr hBand33, by decide +kernel, Band33.checked⟩
  by_cases hBand34 : k ≤ 305678108
  · exact ⟨Band34.cfg, by change 191048818 ≤ _; omega, Or.inr hBand34, by decide +kernel, Band34.checked⟩
  by_cases hBand35 : k ≤ 489084974
  · exact ⟨Band35.cfg, by change 305678109 ≤ _; omega, Or.inr hBand35, by decide +kernel, Band35.checked⟩
  by_cases hBand36 : k ≤ 782535960
  · exact ⟨Band36.cfg, by change 489084975 ≤ _; omega, Or.inr hBand36, by decide +kernel, Band36.checked⟩
  by_cases hBand37 : k ≤ 1252057537
  · exact ⟨Band37.cfg, by change 782535961 ≤ _; omega, Or.inr hBand37, by decide +kernel, Band37.checked⟩
  by_cases hBand38 : k ≤ 2003292060
  · exact ⟨Band38.cfg, by change 1252057538 ≤ _; omega, Or.inr hBand38, by decide +kernel, Band38.checked⟩
  by_cases hBand39 : k ≤ 3205267297
  · exact ⟨Band39.cfg, by change 2003292061 ≤ _; omega, Or.inr hBand39, by decide +kernel, Band39.checked⟩
  by_cases hBand40 : k ≤ 5128427676
  · exact ⟨Band40.cfg, by change 3205267298 ≤ _; omega, Or.inr hBand40, by decide +kernel, Band40.checked⟩
  by_cases hBand41 : k ≤ 8205484283
  · exact ⟨Band41.cfg, by change 5128427677 ≤ _; omega, Or.inr hBand41, by decide +kernel, Band41.checked⟩
  by_cases hBand42 : k ≤ 13128774854
  · exact ⟨Band42.cfg, by change 8205484284 ≤ _; omega, Or.inr hBand42, by decide +kernel, Band42.checked⟩
  by_cases hBand43 : k ≤ 21006039768
  · exact ⟨Band43.cfg, by change 13128774855 ≤ _; omega, Or.inr hBand43, by decide +kernel, Band43.checked⟩
  by_cases hBand44 : k ≤ 33609663630
  · exact ⟨Band44.cfg, by change 21006039769 ≤ _; omega, Or.inr hBand44, by decide +kernel, Band44.checked⟩
  by_cases hBand45 : k ≤ 53775461809
  · exact ⟨Band45.cfg, by change 33609663631 ≤ _; omega, Or.inr hBand45, by decide +kernel, Band45.checked⟩
  by_cases hBand46 : k ≤ 86040738896
  · exact ⟨Band46.cfg, by change 53775461810 ≤ _; omega, Or.inr hBand46, by decide +kernel, Band46.checked⟩
  by_cases hBand47 : k ≤ 137665182235
  · exact ⟨Band47.cfg, by change 86040738897 ≤ _; omega, Or.inr hBand47, by decide +kernel, Band47.checked⟩
  by_cases hBand48 : k ≤ 220264291577
  · exact ⟨Band48.cfg, by change 137665182236 ≤ _; omega, Or.inr hBand48, by decide +kernel, Band48.checked⟩
  by_cases hBand49 : k ≤ 352422866524
  · exact ⟨Band49.cfg, by change 220264291578 ≤ _; omega, Or.inr hBand49, by decide +kernel, Band49.checked⟩
  by_cases hBand50 : k ≤ 563876586440
  · exact ⟨Band50.cfg, by change 352422866525 ≤ _; omega, Or.inr hBand50, by decide +kernel, Band50.checked⟩
  by_cases hBand51 : k ≤ 902202538305
  · exact ⟨Band51.cfg, by change 563876586441 ≤ _; omega, Or.inr hBand51, by decide +kernel, Band51.checked⟩
  by_cases hBand52 : k ≤ 999999999999
  · exact ⟨Band52.cfg, by change 902202538306 ≤ _; omega, Or.inr hBand52, by decide +kernel, Band52.checked⟩
  exact ⟨Band53.cfg, by change 1000000000000 ≤ _; omega, Or.inl rfl, by decide +kernel, Band53.checked⟩

#print axioms selected_6874
end WaringDualEnvelope

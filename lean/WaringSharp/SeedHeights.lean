import WaringSharp.Finite
namespace WaringSharp
open WaringEnvelope WaringDualEnvelope
theorem selected_heights_6873 (k : ℕ) (hl : 21≤k) (hu : k<180000^2) :
    ∃ c : WaringDualEnvelope.Config, c.first≤k ∧ k≤c.last ∧ c.last≠0 ∧
    3*c.heightTop≤T ∧ SizeFacts c ∧ WaringDualEnvelope.Certified c (6873*D/1000-ceilDiv D c.first) := by
  by_cases h0 : k≤33
  · exact ⟨Band00.cfg, by change 21≤_;omega, h0, by decide, by decide, by decide +kernel, Band00.checked⟩
  by_cases h1 : k≤54
  · exact ⟨Band01.cfg, by change 34≤_;omega, h1, by decide, by decide, by decide +kernel, Band01.checked⟩
  by_cases h2 : k≤88
  · exact ⟨Band02.cfg, by change 55≤_;omega, h2, by decide, by decide, by decide +kernel, Band02.checked⟩
  by_cases h3 : k≤142
  · exact ⟨Band03.cfg, by change 89≤_;omega, h3, by decide, by decide, by decide +kernel, Band03.checked⟩
  by_cases h4 : k≤228
  · exact ⟨Band04.cfg, by change 143≤_;omega, h4, by decide, by decide, by decide +kernel, Band04.checked⟩
  by_cases h5 : k≤366
  · exact ⟨Band05.cfg, by change 229≤_;omega, h5, by decide, by decide, by decide +kernel, Band05.checked⟩
  by_cases h6 : k≤587
  · exact ⟨Band06.cfg, by change 367≤_;omega, h6, by decide, by decide, by decide +kernel, Band06.checked⟩
  by_cases h7 : k≤940
  · exact ⟨Band07.cfg, by change 588≤_;omega, h7, by decide, by decide, by decide +kernel, Band07.checked⟩
  by_cases h8 : k≤1505
  · exact ⟨Band08.cfg, by change 941≤_;omega, h8, by decide, by decide, by decide +kernel, Band08.checked⟩
  by_cases h9 : k≤2409
  · exact ⟨Band09.cfg, by change 1506≤_;omega, h9, by decide, by decide, by decide +kernel, Band09.checked⟩
  by_cases h10 : k≤3856
  · exact ⟨Band10.cfg, by change 2410≤_;omega, h10, by decide, by decide, by decide +kernel, Band10.checked⟩
  by_cases h11 : k≤6171
  · exact ⟨Band11.cfg, by change 3857≤_;omega, h11, by decide, by decide, by decide +kernel, Band11.checked⟩
  by_cases h12 : k≤9875
  · exact ⟨Band12.cfg, by change 6172≤_;omega, h12, by decide, by decide, by decide +kernel, Band12.checked⟩
  by_cases h13 : k≤15801
  · exact ⟨Band13.cfg, by change 9876≤_;omega, h13, by decide, by decide, by decide +kernel, Band13.checked⟩
  by_cases h14 : k≤25283
  · exact ⟨Band14.cfg, by change 15802≤_;omega, h14, by decide, by decide, by decide +kernel, Band14.checked⟩
  by_cases h15 : k≤40454
  · exact ⟨Band15.cfg, by change 25284≤_;omega, h15, by decide, by decide, by decide +kernel, Band15.checked⟩
  by_cases h16 : k≤64728
  · exact ⟨Band16.cfg, by change 40455≤_;omega, h16, by decide, by decide, by decide +kernel, Band16.checked⟩
  by_cases h17 : k≤103566
  · exact ⟨Band17.cfg, by change 64729≤_;omega, h17, by decide, by decide, by decide +kernel, Band17.checked⟩
  by_cases h18 : k≤165707
  · exact ⟨Band18.cfg, by change 103567≤_;omega, h18, by decide, by decide, by decide +kernel, Band18.checked⟩
  by_cases h19 : k≤265132
  · exact ⟨Band19.cfg, by change 165708≤_;omega, h19, by decide, by decide, by decide +kernel, Band19.checked⟩
  by_cases h20 : k≤424212
  · exact ⟨Band20.cfg, by change 265133≤_;omega, h20, by decide, by decide, by decide +kernel, Band20.checked⟩
  by_cases h21 : k≤678740
  · exact ⟨Band21.cfg, by change 424213≤_;omega, h21, by decide, by decide, by decide +kernel, Band21.checked⟩
  by_cases h22 : k≤1085985
  · exact ⟨Band22.cfg, by change 678741≤_;omega, h22, by decide, by decide, by decide +kernel, Band22.checked⟩
  by_cases h23 : k≤1737577
  · exact ⟨Band23.cfg, by change 1085986≤_;omega, h23, by decide, by decide, by decide +kernel, Band23.checked⟩
  by_cases h24 : k≤2780124
  · exact ⟨Band24.cfg, by change 1737578≤_;omega, h24, by decide, by decide, by decide +kernel, Band24.checked⟩
  by_cases h25 : k≤4448200
  · exact ⟨Band25.cfg, by change 2780125≤_;omega, h25, by decide, by decide, by decide +kernel, Band25.checked⟩
  by_cases h26 : k≤7117121
  · exact ⟨Band26.cfg, by change 4448201≤_;omega, h26, by decide, by decide, by decide +kernel, Band26.checked⟩
  by_cases h27 : k≤11387395
  · exact ⟨Band27.cfg, by change 7117122≤_;omega, h27, by decide, by decide, by decide +kernel, Band27.checked⟩
  by_cases h28 : k≤18219833
  · exact ⟨Band28.cfg, by change 11387396≤_;omega, h28, by decide, by decide, by decide +kernel, Band28.checked⟩
  by_cases h29 : k≤29151734
  · exact ⟨Band29.cfg, by change 18219834≤_;omega, h29, by decide, by decide, by decide +kernel, Band29.checked⟩
  by_cases h30 : k≤46642776
  · exact ⟨Band30.cfg, by change 29151735≤_;omega, h30, by decide, by decide, by decide +kernel, Band30.checked⟩
  by_cases h31 : k≤74628443
  · exact ⟨Band31.cfg, by change 46642777≤_;omega, h31, by decide, by decide, by decide +kernel, Band31.checked⟩
  by_cases h32 : k≤119405510
  · exact ⟨Band32.cfg, by change 74628444≤_;omega, h32, by decide, by decide, by decide +kernel, Band32.checked⟩
  by_cases h33 : k≤191048817
  · exact ⟨Band33.cfg, by change 119405511≤_;omega, h33, by decide, by decide, by decide +kernel, Band33.checked⟩
  by_cases h34 : k≤305678108
  · exact ⟨Band34.cfg, by change 191048818≤_;omega, h34, by decide, by decide, by decide +kernel, Band34.checked⟩
  by_cases h35 : k≤489084974
  · exact ⟨Band35.cfg, by change 305678109≤_;omega, h35, by decide, by decide, by decide +kernel, Band35.checked⟩
  by_cases h36 : k≤782535960
  · exact ⟨Band36.cfg, by change 489084975≤_;omega, h36, by decide, by decide, by decide +kernel, Band36.checked⟩
  by_cases h37 : k≤1252057537
  · exact ⟨Band37.cfg, by change 782535961≤_;omega, h37, by decide, by decide, by decide +kernel, Band37.checked⟩
  by_cases h38 : k≤2003292060
  · exact ⟨Band38.cfg, by change 1252057538≤_;omega, h38, by decide, by decide, by decide +kernel, Band38.checked⟩
  by_cases h39 : k≤3205267297
  · exact ⟨Band39.cfg, by change 2003292061≤_;omega, h39, by decide, by decide, by decide +kernel, Band39.checked⟩
  by_cases h40 : k≤5128427676
  · exact ⟨Band40.cfg, by change 3205267298≤_;omega, h40, by decide, by decide, by decide +kernel, Band40.checked⟩
  by_cases h41 : k≤8205484283
  · exact ⟨Band41.cfg, by change 5128427677≤_;omega, h41, by decide, by decide, by decide +kernel, Band41.checked⟩
  by_cases h42 : k≤13128774854
  · exact ⟨Band42.cfg, by change 8205484284≤_;omega, h42, by decide, by decide, by decide +kernel, Band42.checked⟩
  by_cases h43 : k≤21006039768
  · exact ⟨Band43.cfg, by change 13128774855≤_;omega, h43, by decide, by decide, by decide +kernel, Band43.checked⟩
  by_cases h44 : k≤33609663630
  · exact ⟨Band44.cfg, by change 21006039769≤_;omega, h44, by decide, by decide, by decide +kernel, Band44.checked⟩
  omega
#print axioms selected_heights_6873
end WaringSharp

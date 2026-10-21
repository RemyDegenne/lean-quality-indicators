namespace OAI

open Set MeasureTheory

namespace BorsukNine.FiniteObstruction

attribute [local instance] Classical.propDecidable

variable {T Q : Family}

theorem c32646 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 3, 5, 8} → ¬ T {0, 4, 7} → False := by
  classical
  intro a177 n24
  have u0_304 : ¬ Q {3, 4, 7, 9} := by
    intro hv
    exact c32583 h h0 hv
  have u1_210 : ¬ Q {1, 2, 3, 9} := by
    intro hv
    exact c32640 h h0 hv
  have u2_189 : ¬ Q {0, 4, 6, 7} := by
    intro hv
    exact c356 h hv n24
  have u3_172 : ¬ Q {0, 3, 4, 7} := by
    intro hv
    exact c352 h hv n24
  have u4_17 : T {0, 3, 5} := by
    by_contra hv
    exact c253 h a177 hv
  have u5_20 : T {0, 3, 8} := by
    by_contra hv
    exact c294 h a177 hv
  have u6_29 : T {0, 5, 8} := by
    by_contra hv
    exact c427 h a177 hv
  have u7_93 : T {3, 5, 8} := by
    by_contra hv
    exact c1383 h a177 hv
  have u8_40 : T {1, 2, 6} := by
    by_contra hv
    exact c32599 h h0 a177 hv
  have u9_280 : ¬ Q {2, 4, 6, 7} := by
    intro hv
    exact c32211 h h0 hv u5_20 u4_17
  have u10_245 : ¬ Q {1, 4, 6, 7} := by
    intro hv
    exact c32011 h h0 u5_20 u4_17 hv
  have u11_109 : ¬ T {4, 7, 9} := by
    intro hv
    exact c9645 h a177 u8_40 hv
  have u12_105 : ¬ T {4, 6, 7} := by
    intro hv
    exact c31281 h h0 u9_280 u10_245 hv u2_189
  have u13_300 : ¬ Q {3, 4, 6, 7} := by
    intro hv
    exact c31558 h h0 hv u10_245 u2_189 u9_280
  have u14_112 : T {5, 6, 8} := by
    by_contra hv
    exact c31643 h h0 u11_109 hv
  have u15_108 : T {4, 7, 8} := by
    by_contra hv
    exact c31669 h h0 hv u11_109 u12_105
  have u16_116 : T {5, 8, 9} := by
    by_contra hv
    exact c31635 h h0 u12_105 hv
  have u17_43 : T {1, 2, 9} := by
    by_contra hv
    exact c9648 h a177 hv u12_105
  have u18_224 : ¬ Q {1, 2, 7, 9} := by
    intro hv
    exact c16349 h hv u6_29 u7_93 u14_112
  have u19_263 : ¬ Q {2, 3, 4, 7} := by
    intro hv
    exact c21787 h hv u6_29 u14_112 u16_116
  have u20_228 : ¬ Q {1, 3, 4, 7} := by
    intro hv
    exact c16887 h hv u6_29 u14_112 u16_116
  have u21_215 : ¬ Q {1, 2, 4, 9} := by
    intro hv
    exact c15071 h hv u6_29 u7_93 u14_112
  have u22_222 : ¬ Q {1, 2, 6, 9} := by
    intro hv
    exact c15945 h hv u4_17 u15_108
  have u23_303 : ¬ Q {3, 4, 7, 8} := by
    intro hv
    exact c32446 h h0 hv u17_43 u8_40
  have u24_297 : ¬ Q {3, 4, 5, 7} := by
    intro hv
    exact c32385 h h0 hv u17_43 u8_40
  have u25_88 : ¬ T {3, 4, 7} := by
    intro hv
    exact c1307 h hv u3_172 u20_228 u19_263 u24_297 u13_300 u23_303 u0_304
  have u26_225 : ¬ Q {1, 2, 8, 9} := by
    intro hv
    exact c16472 h hv n24 u25_88 u12_105
  have u27_219 : ¬ Q {1, 2, 5, 9} := by
    intro hv
    exact c15622 h hv n24 u25_88 u12_105
  exact c31390 h u22_222 u17_43 u26_225 u18_224 u21_215 u1_210 u27_219

end BorsukNine.FiniteObstruction
end OAI

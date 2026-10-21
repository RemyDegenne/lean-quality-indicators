namespace OAI

section

namespace MaximalSeshadri.Geometry

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventual_seshadri_equality (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) : EventualSeshadriEquality S L := by
  obtain ⟨r₀,hr₀,h⟩ := S.eventual_very_general_curve_lower L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,hC⟩ := h r hr
  exact ⟨Z,hZ,hne,fun p hp => S.seshadri_eq_of_curve_lower L hL (hr₀.trans_le hr) p (hC p hp)⟩

end
end MaximalSeshadri.Geometry
end
end OAI

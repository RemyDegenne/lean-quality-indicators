@[expose] public section

namespace SimpleGraph

variable {α : Type*} {G G' : SimpleGraph α}

section radius

lemma ediam_eq_top_iff_radius_eq_top [Nonempty α] : G.ediam = ⊤ ↔ G.radius = ⊤ := by
  refine ⟨?_, fun hr ↦ eq_top_iff.mpr (hr ▸ radius_le_ediam)⟩
  contrapose
  intro hr
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  have hdiam : G.ediam ≤ 2 * G.eccent w := ediam_le_two_mul_eccent w
  exact ne_top_of_lt <| lt_of_le_of_lt hdiam <| WithTop.mul_lt_top (ENat.natCast_lt_top 2) <|
    lt_top_iff_ne_top.mpr (hw ▸ hr)

end radius
end SimpleGraph
end

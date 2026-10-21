namespace OAI

section

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

open SSet.modelCategoryQuillen

noncomputable section

theorem horn_generators_kanWeak : J.{0} ≤ kanWeakMonomorphisms := by
  intro A B i hi
  refine ⟨J_le_monomorphisms i hi, ?_⟩
  simp only [J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact horn_kanBaseChangeWeak n k

end
end Thomason.Construction
end
end OAI

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix Blueprint.Fischer Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec tvTabs

theorem rep_tvP (m : Fin 693) : Rep 693 tvTabs[m.val]! (tvP m) := by
  rw [tvTabs_get]
  intro i hi
  have h := rep_tvTable (uVec m) (uVec_iso ptsFacts m.2)
  rw [codeOf_uVec ptsFacts m.2] at h
  rw [h i hi, idx_of_lt _ hi, idx_of_lt _ hi]
  rfl

end CFSG.Fischer
end

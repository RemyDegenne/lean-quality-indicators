public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem exists_rootModel
    (v : CVert) : ∃ M : RootModel v, M.LabelCompat := by
  obtain ⟨θ, -, hθ⟩ := native_coset_graph_exact_root_local_geometry
  obtain ⟨s, hs, iv, H1, H2, H3, H4, -⟩ := hθ v
  refine ⟨⟨iv, H2, fun γ => ?_, fun y hy => ?_⟩, orderOf_clabel_mul_of_root θ hs iv H1⟩
  · obtain ⟨y, rfl⟩ := H4 γ
    exact ⟨y, y.2, fun u => ⟨(stabAct y u).2, H3 y u⟩⟩
  · exact ⟨rhoV θ hs ⟨y, hy⟩, fun u => ⟨(stabAct ⟨y, hy⟩ u).2, H3 ⟨y, hy⟩ u⟩⟩

end CFSG.Monster.B.TwoA.Amalgam
end

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_isAltType_three {L : Subgroup G} (h : IsAltType L 3) :
    Group.IsSolvable ↥L := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  have hA : Group.IsSolvable ↥(alternatingGroup (Fin 3)) := inferInstance
  have hO : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := by
    have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).isNilpotent
    infer_instance
  refine Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥L).subtype α ?_
  rw [hαk, Subgroup.range_subtype]

end CFSG.Quasithin.H13.A5
end

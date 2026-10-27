public section

namespace CFSG.ASVolI

open CFSG.Open

section PartBurnsideF4j

section RestrictChart

open CFSG.ASVolI.ChF

theorem burnsideF4j_map_trans {A B C : Type} [Group A] [Group B] [Group C] (f : A ≃* B)
    (e : B ≃* C) (X : Subgroup A) :
    X.map (f.trans e).toMonoidHom = (X.map f.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

end RestrictChart
end PartBurnsideF4j
end CFSG.ASVolI
end

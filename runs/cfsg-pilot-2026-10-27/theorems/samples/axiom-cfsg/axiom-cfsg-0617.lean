public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

open scoped commutatorElement

section Aux

theorem isL2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {P : ℕ → Prop}
    (h : IsL2 X P) : IsL2 Y P := by
  obtain ⟨F, _, _, hP, ⟨e'⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hP, ⟨e.symm.trans e'⟩⟩

end Aux
end CFSG.GH74.GLS.Stage2.Local.P27.QId
end

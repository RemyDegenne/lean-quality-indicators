@[expose] public section

namespace Supernatural

theorem finiteAddSubgroupOrder_le_torsionOrder (A : Type*) [AddCommGroup A]
    (hA : IsAddTorsion A) (B : FiniteAddSubgroup A) :
    @ofFiniteCard B.1 B.2 (inferInstanceAs (Nonempty B.1)) ≤ torsionOrder A hA :=
  le_iSup (fun C : FiniteAddSubgroup A ↦
    @ofFiniteCard C.1 C.2 (inferInstanceAs (Nonempty C.1))) B

end Supernatural
end

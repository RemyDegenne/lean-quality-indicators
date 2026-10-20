@[expose] public section

open Set Function

open CategoryTheory

open scoped Pointwise

noncomputable section

local instance GraphCoveringTheory.Kurosh.kuroshActiveDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

/-- Include a nontrivial stabilizer in the active product, collapsing trivial ones. -/
noncomputable def treeVertexComponentToActive {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    TreeKuroshComponent G H (Sum.inl a) →*
      KuroshActiveProduct G H := by
  by_cases htriv : treeVertexStabilizer G H a = ⊥
  · exact
      { toFun := fun _ => 1
        map_one' := by simp
        map_mul' := by intro x y; simp }
  · let j : KuroshActiveVertexIndex G H := ⟨a, htriv⟩
    exact
      { toFun := fun x => Monoid.CoprodI.of
          (show KuroshActiveComponent G H (Sum.inl j) from
            ULift.up x.down)
        map_one' := by
          change Monoid.CoprodI.of
            (show KuroshActiveComponent G H (Sum.inl j) from
              ULift.up (1 : treeVertexStabilizer G H a)) = 1
          exact (Monoid.CoprodI.of :
            KuroshActiveComponent G H (Sum.inl j) →*
              KuroshActiveProduct G H).map_one
        map_mul' := by
          intro x y
          change Monoid.CoprodI.of
              (show KuroshActiveComponent G H (Sum.inl j) from
                ULift.up (x.down * y.down)) =
            Monoid.CoprodI.of
              (show KuroshActiveComponent G H (Sum.inl j) from
                ULift.up x.down) *
              Monoid.CoprodI.of
                (show KuroshActiveComponent G H (Sum.inl j) from
                  ULift.up y.down)
          rw [← (Monoid.CoprodI.of :
            KuroshActiveComponent G H (Sum.inl j) →*
              KuroshActiveProduct G H).map_mul]
          rfl }

end GraphCoveringTheory.Kurosh
end
end

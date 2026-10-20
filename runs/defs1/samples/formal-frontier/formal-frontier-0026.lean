@[expose] public section

open CategoryTheory TopRep

open scoped ZeroObject

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G]

variable {A B C : TopRep.{max v w} k G}

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The first seven objects and six maps of the algebraic long exact sequence:
`0 → Aᴳ → Bᴳ → Cᴳ → H¹(G,A) → H¹(G,B) → H¹(G,C)`.
The invariant maps come from Mathlib's functor, and the boundary is precisely
the existing degree-zero connecting map transported along `zeroIso`. -/
noncomputable def initialInvariantsSequence [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    ComposableArrows (ModuleCat.{max v w} k) 6 :=
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  (ComposableArrows.mk₅
    (F.map ((invariantsFunctor k G).map i))
    (F.map ((invariantsFunctor k G).map p))
    (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0)
    (F.map (map (ContinuousMonoidHom.id G) i 1))
    (F.map (map (ContinuousMonoidHom.id G) p 1))).precomp
      (0 : (0 : ModuleCat.{max v w} k) ⟶ F.obj ((invariantsFunctor k G).obj A))

end ContinuousCohomology
end

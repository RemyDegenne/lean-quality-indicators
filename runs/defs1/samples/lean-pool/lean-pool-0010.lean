@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

section ClosedCut

variable {L : Type} {V : Fragment L} {i j : L}
  (hij : i ≠ j)
  (hclosed : V.pairing (V.boundaryFlag i) = V.boundaryFlag j)
  (t : Finset (SurvivingFlag V i j))
  (hct : ∀ f ∈ t, (V.gluePairClosed i j hclosed).pairing f ∈ t)

section ClosedTrue

variable (hcT : ∀ f ∈ liftSubsetClosed t true,
  V.pairing f ∈ liftSubsetClosed t true)

/-- **Even colourings agree across a closing cut the subset
carries.** -/
noncomputable def evenColourEquivClosedTrue (k : ℕ) :
    (EdgeSubset.mk (liftSubsetClosed t true) hcT :
        EdgeSubset V).EvenColouring k
      ≃ (EdgeSubset.mk t hct :
        EdgeSubset (V.gluePairClosed i j hclosed)).EvenColouring
          k where
  toFun ψ :=
    ⟨fun g => ψ.val ⟨g.val.val,
        notMem_liftClosed_true_of_notMem t g.prop⟩,
      fun g =>
        Eq.trans
          (congrArg ψ.val (Subtype.ext
            (gluePairClosed_pairing_val hclosed g.val)))
          (ψ.prop ⟨g.val.val,
            notMem_liftClosed_true_of_notMem t g.prop⟩)⟩
  invFun ψ' :=
    ⟨fun f => ψ'.val ⟨survOfNotLiftClosedTrue hij t f.prop,
        survOfNotLiftClosedTrue_notMem hij t f.prop⟩,
      fun f => by
        refine Eq.trans ?_ (ψ'.prop
          ⟨survOfNotLiftClosedTrue hij t f.prop,
            survOfNotLiftClosedTrue_notMem hij t f.prop⟩)
        exact congrArg ψ'.val (Subtype.ext (Subtype.ext
          (gluePairClosed_pairing_val hclosed
            (survOfNotLiftClosedTrue hij t f.prop)).symm))⟩
  left_inv _ := rfl
  right_inv _ := rfl

end ClosedTrue
end ClosedCut
end EdgeSubset
end RS
end

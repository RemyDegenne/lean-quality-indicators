@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

variable {α : Type} {W : Fragment α} {i j : α}

section ClosedGlue

variable (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (b : Bool)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

/-- The `val`-bijection between the periodic flags of the two
sides (closed case). -/
noncomputable def periodicEquivGlueClosed
    (κ' : (Fg).RelTransitionSystem) :
    {f : W.Flag // f ∈ (RelTransitionSystem.unglueClosed hclosed
      b s' hc' hc κ').periodicFlags} ≃
      {g : (W.gluePairClosed i j hclosed).Flag //
        g ∈ κ'.periodicFlags} where
  toFun f := ⟨(⟨f.val,
      (internal_surviving i j ((RelTransitionSystem.unglueClosed
        hclosed b s' hc' hc κ').periodicFlags_sub f.prop)).1,
      (internal_surviving i j ((RelTransitionSystem.unglueClosed
        hclosed b s' hc' hc κ').periodicFlags_sub f.prop)).2⟩ :
        SurvivingFlag W i j),
    periodicFlags_of_val_glueClosed hclosed b s' hc' hc κ'
      f.prop⟩
  invFun g := ⟨g.val.val,
    periodicFlags_val_of_glueClosed hclosed b s' hc' hc κ'
      g.prop⟩
  left_inv _f := Subtype.ext rfl
  right_inv _g := Subtype.ext (Subtype.ext rfl)

end ClosedGlue
end EdgeSubset
end RS
end

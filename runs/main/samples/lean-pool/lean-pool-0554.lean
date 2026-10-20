@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

section ClosedEngine

variable {α : Type} {W : Fragment α} {i j : α}
  (hij : i ≠ j)
  (hclosed : W.pairing (W.boundaryFlag i) = W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (b : Bool)
  (hc' : ∀ f ∈ s', (W.gluePairClosed i j hclosed).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetClosed s' b,
    W.pairing f ∈ liftSubsetClosed s' b)

local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairClosed i j hclosed))

local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetClosed s' b) hc : EdgeSubset W)

variable
  (κ' : (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairClosed i j hclosed)).RelTransitionSystem)
  (o' : κ'.Orientation)

local notation "κW" =>
  RelTransitionSystem.unglueClosed hclosed b s' hc' hc κ'

local notation "oW" =>
  unglueOrientationClosed hclosed b s' hc' hc κ' o'

theorem evenColoursAt_transport_closed {k : ℕ}
    (ψW : (Fl).EvenColouring k) (ψ' : (Fg).EvenColouring k)
    (hψ : ∀ (g : SurvivingFlag W i j)
      (h1 : g.val ∉ liftSubsetClosed s' b) (h2 : g ∉ s'),
      ψW.val ⟨g.val, h1⟩ = ψ'.val ⟨g, h2⟩)
    (v : W.Vertex) :
    (Fl).evenColoursAt ψW v = (Fg).evenColoursAt ψ' v := by
  have hemb : ∀ x : {f' : (W.gluePairClosed i j hclosed).Flag //
      f' ∉ (Fg).flags},
      x.val.val ∉ (Fl).flags := by
    intro x hmem
    exact x.prop ((surviving_val_mem_liftClosed_iff s' b
      x.val).mp hmem)
  have hinj : Function.Injective
      (fun x : {f' : (W.gluePairClosed i j hclosed).Flag //
          f' ∉ (Fg).flags} =>
        (⟨x.val.val, hemb x⟩ : {f : W.Flag // f ∉ (Fl).flags}))
      := by
    intro x y hxy
    have hxy' : (⟨x.val.val, hemb x⟩ :
        {f : W.Flag // f ∉ (Fl).flags}) = ⟨y.val.val, hemb y⟩ :=
      hxy
    have hval : x.val.val = y.val.val := congrArg
      (fun z : {f : W.Flag // f ∉ (Fl).flags} => z.val) hxy'
    exact Subtype.ext (Subtype.ext hval)
  unfold EdgeSubset.evenColoursAt
  refine multiset_map_eq_of_bij _ _
    (fun x => ⟨x.val.val, hemb x⟩) hinj ?_ ?_ ψW.val ψ'.val ?_
  · intro y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact glueAttach_inl_iff y.val v
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hsurv := vertex_flag_surviving (i := i) (j := j)
      x.val v hx
    have hnot : (⟨x.val, hsurv.1, hsurv.2⟩ :
        SurvivingFlag W i j) ∉ s' := by
      intro hmem
      exact x.prop ((surviving_val_mem_liftClosed_iff s' b
        ⟨x.val, hsurv.1, hsurv.2⟩).mpr hmem)
    exact ⟨⟨⟨x.val, hsurv.1, hsurv.2⟩, hnot⟩, Subtype.ext rfl⟩
  · intro y _
    exact hψ y.val (hemb y) y.prop

end ClosedEngine
end EdgeSubset
end RS
end

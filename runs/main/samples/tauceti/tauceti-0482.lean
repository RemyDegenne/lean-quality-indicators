public section

namespace TauCeti.BipartiteRibbonGraph

universe u

variable {n : ℕ}

@[simp]
theorem connectedIsoClassEquiv_symm_mk (t : ConnectedTriple n) :
    (connectedIsoClassEquiv.{u} n).symm (ConnectedIsoClass.mk t) =
      Quotient.mk (connectedIsoSetoid n)
        ⟨⟨t.1.ribbonGraph.ulift, t.1.ribbonGraph.card_E_ulift.trans t.1.card_E_ribbonGraph⟩,
          t.1.ribbonGraph.uliftIso.isConnected_iff.mpr
            (t.1.isConnected_ribbonGraph.mpr t.2)⟩ := by
  apply (connectedIsoClassEquiv n).injective
  rw [Equiv.apply_symm_apply, connectedIsoClassEquiv_mk _
    (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n)))]
  symm
  apply ConnectedIsoClass.mk_eq_mk_iff_equivalent.mpr
  simpa only [PermutationTriple.toPermutationTriple_ribbonGraph] using
    equivalent_toPermutationTriple_of_iso t.1.ribbonGraph.uliftIso
      (t.1.ribbonGraph.uliftIso.edge.trans (Equiv.refl (Fin n))) (Equiv.refl (Fin n))

end TauCeti.BipartiteRibbonGraph
end

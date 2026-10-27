@[expose] public section

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall

namespace GeneralGrushko

universe u v

variable {G H : Type u} [Group G] [Group H]

/-- A graph-level formulation of the one point still missing from the fold
argument.  The graph is assumed to be generating, connected, reverse-free,
and to satisfy the Euler bound.  At least one non-base vertex must admit a
null path whose first edge can be folded without reusing either orientation
in the complementary path. -/
def HasSafeNullFold : Prop :=
  ∀ (n : ℕ) (V : Type) [Fintype V] [qV : Quiver.{0, 0} V]
    [_hV : HasInvolutiveReverse V]
    [_hHom : ∀ a b : V, Fintype (a ⟶ b)]
    (M : MarkedBinaryGraph (G := G) (H := H) (V := V) n),
    ReverseFree (V := V) → M.IsGenerating → M.WeaklyConnected →
      Fintype.card (AllArrow (V := V)) ≤
        2 * (n + Fintype.card V - 1) →
      1 < Fintype.card V →
      ∃ v : V, v ≠ M.base ∧
        ∃ p : @Quiver.Path (Symmetrify V)
            (@Quiver.symmetrifyQuiver V qV)
            (show Symmetrify V from M.base) (show Symmetrify V from v),
          M.labeling.symmPathRead p = 1 ∧
          ∃ c : Symmetrify V,
            ∃ e : @Quiver.Hom (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV)
              (show Symmetrify V from M.base) c,
            ∃ q : @Quiver.Path (Symmetrify V)
              (@Quiver.symmetrifyQuiver V qV) c
              (show Symmetrify V from v),
              p = e.toPath.comp q ∧
                foldSymmPathAvoid (symmOrientedArrow e) q

end GeneralGrushko
end MarshallHall
end
end

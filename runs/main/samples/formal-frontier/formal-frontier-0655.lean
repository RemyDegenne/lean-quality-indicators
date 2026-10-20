public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace Topology

universe u v

noncomputable section

namespace SpectralStoneDuality

theorem nonempty_limit_of_spectral {J : Type v} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ TopCat.{max v u})
    (hX : ∀ j, SpectralSpace (F.obj j))
    (hmap : ∀ {i j : J} (f : i ⟶ j), IsSpectralMap (F.map f))
    (hne : ∀ j, Nonempty (F.obj j)) :
    Nonempty (TopCat.limitCone F).pt := by
  let G := constructibleDiagram F hmap
  let _ (j : J) : SpectralSpace (F.obj j) := hX j
  let _ (j : J) : Nonempty (G.obj j) := by
    change Nonempty (WithConstructibleTopology (F.obj j))
    exact Nonempty.map (WithTopology.toTopology _) (hne j)
  let _ (j : J) : CompactSpace (G.obj j) :=
    compactSpace_withConstructibleTopology
  let _ (j : J) : T2Space (G.obj j) := by
    change T2Space (WithConstructibleTopology (F.obj j))
    exact t2Space_constructible (F.obj j)
  have hG : Nonempty (TopCat.limitCone G).pt :=
    TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system G
  obtain ⟨x⟩ := hG
  refine ⟨⟨fun j ↦ WithTopology.ofTopology (x.1 j), ?_⟩⟩
  intro i j f
  have hx := x.2 f
  dsimp [G, constructibleDiagram] at hx
  exact congrArg WithTopology.ofTopology hx

end SpectralStoneDuality
end
end

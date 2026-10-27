@[expose] public section

namespace ErdosProblems.MulticolourTriangleRamsey

open Filter Finset SimpleGraph

open scoped Topology

/-- The palette consisting of the selected coordinate in every block. -/
noncomputable def transversalPalette (j t : ℕ) (choice : Fin t → Fin j) :
    Finset (Fin (j * t)) :=
  Finset.univ.map (transversalCoordinateEmbedding j t choice)

end ErdosProblems.MulticolourTriangleRamsey
end

@[expose] public section

namespace Utilities.Certificate.SubdivisionGraph.Spec

open Finset

open Utilities.Gonality

variable {n p : ℕ}

variable (spec : Spec n p) (hlen : ∀ e : Fin p, spec.length e = 1)

theorem regularSubdivisionGonality_graph (spec : Spec n p)
    (hlen : ∀ e : Fin p, spec.length e = 1) :
    Utilities.Gonality.regularSubdivisionGonality spec.graph
      = spec.regularSubdivisionGonality := by
  unfold Utilities.Gonality.regularSubdivisionGonality
    Spec.regularSubdivisionGonality
  congr 1
  ext d
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (divisorialGonality_regularSubdivision spec hlen k hk).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, divisorialGonality_regularSubdivision spec hlen k hk⟩

end Utilities.Certificate.SubdivisionGraph.Spec
end

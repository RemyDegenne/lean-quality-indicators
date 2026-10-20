public section

namespace TauCeti

open CategoryTheory

universe u t

variable {k : Type u} [Field k] {m : ℕ}

/-- **A representation of the four subspace quiver, stretched along the spine of
`TauCeti.Quiver.AffineD m`**: the centre space of `M` sits at every spine vertex, with the identity
on every spine arrow, and the outer space indexed by `i` at the leaf indexed by `i`, whose arrow
acts as the arrow of `M` from that outer vertex. -/
@[expose]
noncomputable def affineDStretchRep (m : ℕ)
    (M : QuiverRep.{u, 0, 1, t} k (Quiver.Subspace (Fin 4))) :
    QuiverRep.{u, 0, 0, t} k (Quiver.AffineD m) :=
  affineDCollapseFunctor m ⋙ M

end TauCeti
end

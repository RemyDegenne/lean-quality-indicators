public section

namespace TauCeti

open CategoryTheory

open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

section ReflectRep

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

/-- **The reflection of a representation at a sink** `i`: the representation `C⁺ᵢ M` of the
reflected quiver `TauCeti.Quiver.Reflect Q i` that agrees with `M` away from `i`, puts the kernel
of `TauCeti.incomingSum` at `i`, and lets each reversed arrow act by the matching coordinate
projection out of that kernel. -/
noncomputable def reflectRep (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q}
    (hi : IsSink i) : QuiverRep k (Reflect Q i) :=
  Paths.lift (reflectPrefunctor M hi)

end ReflectRep
end TauCeti
end

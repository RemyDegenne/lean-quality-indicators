@[expose] public section

universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}

variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]

variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Fin

namespace LHom

@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

end LHom
end Language
end FirstOrder
end

public section

open CategoryTheory

namespace TauCeti

universe u v

namespace FGCommGrpCat

/-- Construct an object of `FGCommGrpCat` from a finitely generated commutative group. -/
abbrev of (G : Type v) [CommGroup G] [Group.FG G] : FGCommGrpCat.{v} :=
  ⟨CommGrpCat.of G, (CommGrpCat.isFG_iff _).2 inferInstance⟩

end FGCommGrpCat
end TauCeti
end

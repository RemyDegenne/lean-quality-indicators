@[expose] public section

namespace CategoryTheory.Limits

universe t w w' v u

namespace MultispanIndex

variable {C : Type u} [Category.{v} C] {J : MultispanShape.{w, w'}}
    (I : MultispanIndex J C)

/-- The induced map `∐ I.left ⟶ ∐ I.right` via `I.snd` for colimiting cofans. -/
def sndSigmaMapOfIsColimit {c : Cofan I.left} (d : Cofan I.right) (hc : IsColimit c) :
    c.pt ⟶ d.pt :=
  Cofan.IsColimit.desc hc fun i ↦ I.snd i ≫ d.inj _

end MultispanIndex
end CategoryTheory.Limits
end

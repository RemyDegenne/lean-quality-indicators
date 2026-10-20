@[expose] public section

universe w v u

open Opposite CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {F F' : Cᵒᵖ ⥤ Type w} (G G' : Subfunctor F)

theorem Subfunctor.le_sheafify : G ≤ G.sheafify J := by
  intro U s hs
  change _ ∈ J _
  convert J.top_mem U.unop
  rw [eq_top_iff]
  rintro V i -
  exact G.map i.op hs

end CategoryTheory
end

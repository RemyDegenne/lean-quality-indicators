@[expose] public section

universe w v u

namespace CategoryTheory

namespace Cat

/-- Assigning to each category `C` the small category `AsSmall C` induces a functor `Cat ⥤ Cat`. -/
@[simps]
def asSmallFunctor : Cat.{v, u} ⥤ Cat.{max w v u, max w v u} where
  obj C := ↧(AsSmall C)
  map F := (AsSmall.down ⋙ F.toFunctor ⋙ AsSmall.up).toCatHom

end Cat
end CategoryTheory
end

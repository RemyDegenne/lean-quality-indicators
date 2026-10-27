@[expose] public section

open CategoryTheory

namespace ProfiniteGrp.FiniteQuotientHom

universe u v

/-- A bundled function between quotient-homomorphism stages. -/
structure HomStageHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F]
    (U V : StageIndex G) where
  /-- The underlying function. -/
  toFun : HomStage G F U → HomStage G F V

end ProfiniteGrp.FiniteQuotientHom
end

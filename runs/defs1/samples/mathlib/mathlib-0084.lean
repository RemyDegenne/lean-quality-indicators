@[expose] public section

universe w v u u₁ u₂ u₃

namespace CategoryTheory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

namespace EnrichedCat

variable {V} {C : Type u} [EnrichedCategory V C] {D : Type u₁} [EnrichedCategory V D]
  {E : Type u₂} [EnrichedCategory V E] {E' : Type u₃} [EnrichedCategory V E']

/-- Composing any `V`-enriched functor with the identity functor is isomorphic to the former
functor. -/
@[simps!]
def rightUnitor (F : EnrichedFunctor V C D) :
    EnrichedFunctor.comp V F (EnrichedFunctor.id V _) ≅ F :=
  EnrichedFunctor.isoMk <| F.forgetComp _ ≪≫
    Functor.isoWhiskerLeft _ (EnrichedFunctor.forgetId V D) ≪≫ Functor.rightUnitor F.forget

end EnrichedCat
end CategoryTheory
end

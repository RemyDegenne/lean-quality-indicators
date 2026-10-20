@[expose] public section

namespace ProfiniteGrp

open CategoryTheory

universe u

/-- Compatible Sylow subgroups of the canonical finite open-normal quotient diagram. -/
noncomputable def compatibleSylow (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime) :
    OpenNormalSubgroup G ⥤ Type u :=
  CompatibleSylow.system p hp G.toFiniteQuotientFunctor
    (G.quotientSylowTransition_surjective)

end ProfiniteGrp
end

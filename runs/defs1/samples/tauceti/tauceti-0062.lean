public noncomputable section

open IsLocalRing IsManifold

open scoped Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

variable {I J}

namespace nodeLocalRing

variable (I J) (p : X) (q : Y)

variable {I J p q}

/-- Two branch germs with equal values glue to a germ at the node. -/
def mk (f : (holomorphicStructureSheaf I X).presheaf.stalk p)
    (g : (holomorphicStructureSheaf J Y).presheaf.stalk q)
    (h : holomorphicStructureSheaf.eval I X p f = holomorphicStructureSheaf.eval J Y q g) :
    nodeLocalRing I J p q :=
  ⟨(f, g), h⟩

end nodeLocalRing
end TauCeti.holomorphicStructureSheaf
end

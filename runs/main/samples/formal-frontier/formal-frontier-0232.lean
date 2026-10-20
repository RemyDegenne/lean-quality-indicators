public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

lemma Scheme.Hom.ker_radical_of_isReduced_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] :
    f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, f.ker_apply]
  exact (Ideal.isRadical_bot.comap (f.app U).hom).radical

end AlgebraicGeometry
end
end

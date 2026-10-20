public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CircleBouquet

theorem positiveGenerator_eq_loop {I : Type v} (i : I) :
    positiveGenerator.{u, v} i = FundamentalGroup.fromPath
      ⟦((Circle.loop 1).map (inclusion.{u, v} i).continuous).cast
        (inclusion_basepoint.{u, v} i).symm (inclusion_basepoint.{u, v} i).symm⟧ := by
  rw [positiveGenerator, FundamentalGroup.mapOfEq_apply]
  rfl

end CircleBouquet
end
end

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory Set

theorem curveArea_cyclic_cut_sum
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) +
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) := by
  rw [curveArea_eq_restriction_add_restriction hab x s, add_comm]

end MovingSofa
end
end
end
end
end
end
end
end
end
end
end

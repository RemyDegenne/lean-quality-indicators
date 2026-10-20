@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem continuous_oppositeSurfaceData_snd (K : ConvexBody Point) :
    Continuous (oppositeSurfaceData K).2 :=
  (continuous_supportValue K).comp (continuous_id.add continuous_const)

end MovingSofa
end
end
end
end
end
end
end
end

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa

open RatInterval

namespace Romik

/-- Second switching angle. -/
def thetaDual : AngleDual 22 vectorBox where
  dual := inputDual 21
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).2.1

end Romik
end GerverSofa
end
end
end
end
end
end
end
end

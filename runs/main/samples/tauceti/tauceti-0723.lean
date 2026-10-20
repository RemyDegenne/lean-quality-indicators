public section

noncomputable section

namespace TauCeti

variable (X : Type*) [MeasurableSpace X]

namespace BoundedBorelFunction

variable {X}

@[simp] theorem coe_algebraMap (c : ℂ) :
    ⇑(algebraMap ℂ (BoundedBorelFunction X) c) = fun _ => c := (rfl)

end BoundedBorelFunction
end TauCeti
end
end

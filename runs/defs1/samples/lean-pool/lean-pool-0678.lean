@[expose] public section

noncomputable section

open Function Cardinal

namespace SetTheory

namespace KunenBoundParams

variable [KunenBoundParams]

open KunenBoundParams

/-- The `κωEquinumerousSubsets` declaration. -/
def κωEquinumerousSubsets := {x : M // x ⊆ κω ∧ #x = #κω}

end KunenBoundParams
end SetTheory
end
end

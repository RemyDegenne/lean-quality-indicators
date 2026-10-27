@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core

open LeanCert.Engine

/-- Check if interval is strictly positive -/
def isStrictlyPositive (I : IntervalRat) : Bool := I.lo > 0

end LeanCert.Engine.Optimization
end
end
end
end

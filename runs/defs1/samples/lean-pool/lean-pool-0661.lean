@[expose] public section

noncomputable section

section

@[expose] public section

namespace LeanCert.Engine.Optimization

open LeanCert.Core

open LeanCert.Engine

/-- An n-dimensional box as a list of intervals.
    The i-th element is the interval for variable i. -/
abbrev Box := List IntervalRat

end LeanCert.Engine.Optimization
end
end
end
end

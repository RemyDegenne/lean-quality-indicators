@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}

namespace Kernel

section Copy

/-- The deterministic kernel that maps `x : α` to the Dirac measure at `(x, x) : α × α`. -/
noncomputable
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) :=
  Kernel.deterministic Function.diag (measurable_id.prod measurable_id)

end Copy
end Kernel
end ProbabilityTheory
end

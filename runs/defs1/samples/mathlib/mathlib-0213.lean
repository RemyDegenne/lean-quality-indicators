@[expose] public section

open MeasurableSpace Set

open scoped MeasureTheory

variable {α β : Type*}

namespace MeasurableSpace

open scoped Function

variable {α : Type*}

namespace DynkinSystem

variable (d : DynkinSystem α)

/-- The least Dynkin system containing a collection of basic sets. -/
def generate (s : Set (Set α)) : DynkinSystem α where
  Has := GenerateHas s
  has_empty := GenerateHas.empty
  has_compl {_} := GenerateHas.compl
  has_iUnion_nat {_} := GenerateHas.iUnion

end DynkinSystem
end MeasurableSpace
end

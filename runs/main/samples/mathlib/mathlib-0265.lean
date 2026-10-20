@[expose] public section

open Set Matroid

variable {α : Type*}

section IndepMatroid

section IsBase

namespace Matroid

@[simp] theorem ofIsBaseOfFinite_isBase {E : Set α} (hE : E.Finite) IsBase exists_isBase
    isBase_exchange subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).IsBase = IsBase := rfl

end Matroid
end IsBase
end IndepMatroid
end

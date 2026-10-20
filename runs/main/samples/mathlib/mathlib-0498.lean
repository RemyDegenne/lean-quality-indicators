@[expose] public section

open Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

@[simp]
protected theorem not_isSuccLimit_zero : ¬ IsSuccLimit (0 : Cardinal) :=
  not_isSuccLimit_bot

end Cardinal
end
end

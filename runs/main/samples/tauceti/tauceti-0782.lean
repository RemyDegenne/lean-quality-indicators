public section

namespace TauCeti

open Multiplicative

open WreathC2

@[simp]
theorem toAdd_wreathTautological (g : wreathBase) :
    toAdd (wreathTautological g) = coordA (g : WreathC2) := (rfl)

end TauCeti
end

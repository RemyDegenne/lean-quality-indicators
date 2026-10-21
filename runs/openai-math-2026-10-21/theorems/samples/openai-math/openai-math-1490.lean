namespace OAI

universe uVariable1 uVariable2

namespace VariableWL.Computation.Stack.PolyRecipe

open Recipe

variable {n m : ℕ}

namespace PortListing

theorem port_number (D : PortListing n) (I : Expr n) (v : Env n) :
    (D.port I).number v=(D.eval v).port (I.number v) := by
  simp only [port,mod_number,div_number,stride_number,numeral_number,Descriptor.PortData.port]

end PortListing
end VariableWL.Computation.Stack.PolyRecipe
end OAI

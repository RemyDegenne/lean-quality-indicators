@[expose] public section

namespace Lean4GlCoalgebras

namespace Split

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isBox : RuleApp → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

end Split
end Lean4GlCoalgebras
end

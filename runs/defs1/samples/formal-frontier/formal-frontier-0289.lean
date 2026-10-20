@[expose] public section

namespace Supernatural

/-- Additive subgroups carrying a proof that their underlying type is finite. -/
def FiniteAddSubgroup (A : Type*) [AddGroup A] :=
  {B : AddSubgroup A // Finite B}

end Supernatural
end

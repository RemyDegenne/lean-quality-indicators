@[expose] public section

namespace FirstOrder.Language

open FirstOrder

variable {α : Type}

variable (L : Language.{0, 0})

/-- Right-witness function symbols inside `KLang L`. -/
def rightFuns : Set (Σ n, (KLang L).Functions n) :=
  Set.range fun p : Σ n, WitnessLang.Functions n => ⟨p.1, (rightWitnessEmb L).onFunction p.2⟩

end FirstOrder.Language
end

@[expose] public section

universe u v u' v' w w'

namespace FirstOrder

namespace Language

open Structure Cardinal

variable (L : Language.{u, v}) (L' : Language.{u', v'}) {M : Type w} [L.Structure M]

@[inherit_doc FirstOrder.Language.LHom]
infixl:10 " →ᴸ " => LHom

variable {L L'}

namespace LHom

variable (ϕ : L →ᴸ L')

variable (L L')

variable {L L'} {L'' : Language}

@[inherit_doc]
local infixl:60 " ∘ᴸ " => LHom.comp

section SumMap

variable {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂)

@[simp]
theorem sumMap_comp_inl : ϕ.sumMap ψ ∘ᴸ LHom.sumInl = LHom.sumInl ∘ᴸ ϕ :=
  LHom.funext (funext fun _ => rfl) (funext fun _ => rfl)

end SumMap
end LHom
end Language
end FirstOrder
end

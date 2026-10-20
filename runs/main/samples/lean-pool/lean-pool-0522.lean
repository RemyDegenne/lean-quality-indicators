@[expose] public section

namespace LO

namespace FirstOrder

namespace Arith

open LO.Arith

variable {ξ : Type*} {n : ℕ}

variable {V : Type*} [ORingStruc V]

variable {ℌ : HierarchySymbol} {Γ Γ' : SigmaPiDelta}

variable (ℌ)

variable {ℌ}

variable [V ⊧ₘ* 𝐏𝐀⁻]

lemma _root_.LO.FirstOrder.Arith.HierarchySymbol.BoldfaceFunction₃.bcomp {k} {F :
    V → V → V → V} {f₁ f₂ f₃ :
    (Fin k → V) → V}
    (hF : ℌ.BoldfaceFunction₃ F)
    (hf₁ : BoldfaceBoundedFunction f₁) (hf₂ : BoldfaceBoundedFunction f₂)
    (hf₃ : BoldfaceBoundedFunction f₃) :
    ℌ.BoldfaceFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  HierarchySymbol.BoldfaceFunction.bcomp (f :=
    ![f₁, f₂, f₃]) hF (by simp [forall_fin_iff_zero_and_forall_succ, *])

end Arith
end FirstOrder
end LO
end

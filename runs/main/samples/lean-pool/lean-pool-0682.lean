@[expose] public section

namespace LO

namespace FirstOrder

namespace Theory

open LO.Arith

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {T : Theory L} [T.Delta1Definable]

variable (T V)

variable {T V}

variable (T V)

variable {T V}

variable {U : Theory L}

namespace Delta1Definable

open Arith.HierarchySymbol.Semiformula LO.FirstOrder.Theory

omit [V ⊧ₘ* 𝐈Sg1] [T.Delta1Definable] in
lemma add_subset_left (dT : T.Delta1Definable) (dU : U.Delta1Definable) :
    haveI := dT.add dU
    T.codeIn V ⊆ (T + U).codeIn V := by
  intro p hp
  apply FirstOrder.Semiformula.curve_mem_left
  simp only [val_sigma] at hp ⊢; exact hp

end Delta1Definable
end Theory
end FirstOrder
end LO
end

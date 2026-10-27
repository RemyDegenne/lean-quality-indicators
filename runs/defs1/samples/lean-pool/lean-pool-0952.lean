@[expose] public section

namespace FirstOrder.Language

variable (s₀ : LocalStage)

section Structures

variable {M : Type} [s₀.Lang.Structure M] [Nonempty M]

/-- The **colimit structure**: an `L_Γ`-symbol is interpreted through any stage representative,
well-defined by the (definitional) stage coherence above. -/
@[implicit_reducible] noncomputable def localColimStructure : (localColim s₀).Structure M where
  funMap {m} f x :=
    Quot.lift
      (fun p => @Structure.funMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_funMap_succ s₀ a.2 x).symm) f
  RelMap {m} r x :=
    Quot.lift
      (fun p => @Structure.RelMap (Llocal s₀ p.1) M (localStageStructure s₀ p.1) m p.2 x)
      (fun a b hab => by subst hab; exact (localStageStructure_relMap_succ s₀ a.2 x).symm) r

end Structures
end FirstOrder.Language
end

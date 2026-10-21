namespace OAI

section

universe u v w

namespace SourceBurnside.RawFixedPoint

noncomputable section

open Structured Structured.Program Structured.Binary Structured.Device Structured.Device.Formula

theorem source_predicate_selfpoint (β g D : ℕ) (c : Tableau.Circuit (3*β) g)
    (output : Fin β → Tableau.Wire (3*β+g)) (blank initial accept : Fin β → Bool)
    (encoding : Bool → Fin β → Bool) :
    ∃t : List Bool, ∀(h l : ℕ) (z : Bool) (data : List Bool),
      ∃(N : ℕ) (b : Bool), ∃r front back,
        Add.bit b=(RawFit.body β g D c output blank initial accept encoding).eval
          (RawPreparedInputs.semantic (WrappedInput.specialize t t) h l z data) ∧
        StackMachine.exec (WrappedInput.machine LiteralCompiler.src LiteralCompiler.dst)
          (WrappedInput.config LiteralCompiler.src LiteralCompiler.dst .reverse
            (WrappedInput.envelope (WrappedInput.specialize t t) (RawHeader.request h l z data)) [] [] [] 0) N=
          WrappedInput.liftConfig (UniversalInput.liftConfig
            (UniversalStack.config (.stopped b) r front back 0)) :=
  construct _ D (body_exponents β g D c output blank initial accept encoding)
    (body_boolean β g D c output blank initial accept encoding)

end
end SourceBurnside.RawFixedPoint
end
end OAI

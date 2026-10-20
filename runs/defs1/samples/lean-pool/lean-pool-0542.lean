@[expose] public section

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

namespace Pattern

/-- A natural-number serialization retaining every application argument. -/
noncomputable def signatureNatCode {T : Signature} [Encodable T.Sym] :
    Pattern T Nat → Nat
  | .var x => Nat.pair 0 x
  | .app sigma args => Nat.pair 1 (Nat.pair (Encodable.encode sigma)
      (Encodable.encode (List.ofFn fun i => (args i).signatureNatCode)))
  | .imp phi psi => Nat.pair 2 (Nat.pair phi.signatureNatCode psi.signatureNatCode)
  | .bot => Nat.pair 3 0
  | .ex x phi => Nat.pair 4 (Nat.pair x phi.signatureNatCode)

end Pattern
end MatchingLogic
end

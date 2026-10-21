namespace OAI

namespace SimpleFInftyOvergroups.BoundedEncoding.NamedAction

open FiniteAlgebraicEnvelopes FiniteAlgebraicEnvelopes.Bootstrap

namespace Operations

variable {G X K L : Type*} (N : Operations G X) [DecidableEq L]

variable {P : Type*} [Primcodable P] [Primcodable G] [Primcodable X]
  [Primcodable K] [Primcodable L]

variable {fg : P → G → Part K} {fx : P → X → Part L}

omit [Primcodable P] [Primcodable G] [Primcodable X] [Primcodable L] in
theorem run_eq_fold (p : P) (w : List (Letter G X)) (f : Form G X) :
    N.run (fx p) w f = EffectiveNames.PartialFold.right
      (fun s : P × Letter G X × Form G X => N.step (fx s.1) s.2.1 s.2.2) p w f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [run,EffectiveNames.PartialFold.right,ih]

end Operations
end SimpleFInftyOvergroups.BoundedEncoding.NamedAction
end OAI

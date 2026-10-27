@[expose] public section

open Encodable Primrec Nat.Partrec Part

variable {α β σ : Type*}

/-- A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles
`O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`. -/
def RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

end

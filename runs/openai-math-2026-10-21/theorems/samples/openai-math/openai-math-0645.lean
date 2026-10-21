namespace OAI

namespace Fifths

namespace Circuit

open Bin Modulus Fifths.Comp

variable {I X U : Type}

section Independent

variable {C : I → Circuit} {x : I → List X} {S a : I → ℕ}

theorem chooseSlot {R : ∀ i, (C i).Pool}
    (p : Comp x S a (fun i => (C i).packPool (R i)))
    {q : I → Slot}
    (h : Comp x S a (fun i => (q i).val)) :
    Comp x S a (fun i => (C i).P.packed (C i).width (R i (q i))) :=
  chooseCase Fin.val Fin.val_injective (fun i k => (C i).P.packed (C i).width (R i k)) h (which p)

end Independent
end Circuit
end Fifths
end OAI

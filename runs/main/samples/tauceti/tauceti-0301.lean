public section

noncomputable section

open Finset ContinuousCohomology QuadraticMap

namespace TauCeti

universe u

section SecondClass

variable {K : Type} [Field K] [Invertible (2 : K)] {n : ℕ}

theorem sw2Class_mk_binary (a b : Kˣ) :
    sw2Class (Quotient.mk (regularFormSetoid K) ⟨2, ![a, b]⟩) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) := by
  simp [sw2Class_mk]

end SecondClass
end TauCeti
end
end

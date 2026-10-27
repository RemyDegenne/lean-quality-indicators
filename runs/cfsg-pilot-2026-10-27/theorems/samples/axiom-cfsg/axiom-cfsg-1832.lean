public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section D132

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.LieType.Universal.Unitary

section HunitRefl

variable {n : ℕ} {F : Type} [Field F]

theorem hunit_refl (e : Equiv.Perm (Fin (n + n))) (he : ∀ t, e (Fin.rev t) = Fin.rev (e t))
    (g : spinGroup (quadPlus n F)) (a b : Fin (n + n)) :
    ∑ t, (RingEquiv.refl F) (matDe e g t a) * matDe e g (Fin.rev t) b =
      if b = Fin.rev a then 1 else 0 := by
  simpa using matDe_unit e he g a b

end HunitRefl
end D132
end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
end

@[expose] public section

universe u v

namespace Ideal

@[simp]
theorem piQuotientRingEquiv_mk {ι : Type u} {R : ι → Type v}
    [∀ i, CommRing (R i)] (I : ∀ i, Ideal (R i))
    (x : ∀ i, R i) :
    piQuotientRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x) =
      fun i ↦ Ideal.Quotient.mk (I i) (x i) := by
  funext i
  exact piQuotientRingEquiv_mk_apply I x i

end Ideal
end

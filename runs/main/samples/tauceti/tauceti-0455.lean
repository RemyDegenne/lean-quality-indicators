public section

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable [CharZero R] (b : P.Base)

@[simp]
lemma mem_posRoots (i : ι) : i ∈ posRoots P b ↔ b.IsPos i := Iff.rfl

end TauCeti
end

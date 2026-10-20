@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem integerCompletionResidueAt_cast
    {n d : Nat.PowerIndex (Set.univ : Set Nat.Primes)} (f : n ⟶ d)
    (x : integerCompletion.{u}) :
    ZMod.cast (integerCompletionResidueAt n x) =
      integerCompletionResidueAt d x := by
  let _ : NeZero n.val := ⟨n.pos.ne'⟩
  let _ : NeZero d.val := ⟨d.pos.ne'⟩
  change ZMod.cast (integerCompletionResidue.{u} n.val x).toAdd.down =
    (integerCompletionResidue.{u} d.val x).toAdd.down
  exact integerCompletionResidue_cast (Nat.PowerIndex.dvd_of_hom f) x

end ProfiniteGrp
end

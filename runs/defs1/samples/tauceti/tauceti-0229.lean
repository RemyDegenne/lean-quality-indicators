public section

namespace TauCeti

namespace FinitaryPerm

/-- Package a finitely supported permutation of `ℕ` as an element of `FinitaryPerm`. -/
@[expose]
def ofPerm (π : Equiv.Perm ℕ) (hπ : (MulAction.fixedBy ℕ π)ᶜ.Finite) : FinitaryPerm :=
  equivFinitary.symm ⟨π, Equiv.Perm.mem_finitary.mpr hπ⟩

end FinitaryPerm
end TauCeti
end

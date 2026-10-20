public section

noncomputable section

namespace TauCeti

variable (p : ℕ) (A : Type*) [AddCommGroup A]

/-- The `p`-adic Tate module of an abelian group: compatible families of `p^n`-torsion points. -/
def TateModule : Type _ :=
  tateModuleSubgroup p A

end TauCeti
end
end

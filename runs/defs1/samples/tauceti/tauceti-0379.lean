public section

noncomputable section

namespace TauCeti

variable (p : ℕ) (A : Type*) [AddCommGroup A]

namespace TateModule

variable {p A}

section Map

variable {B : Type*} [AddCommGroup B]

/-- An additive homomorphism induces an additive homomorphism of Tate modules, componentwise. -/
def map (f : A →+ B) : TateModule p A →+ TateModule p B :=
  (AddMonoidHom.pi fun n ↦ (levelMap (p := p) f n).comp (proj (p := p) n)).codRestrict
    (tateModuleSubgroup p B) fun x n ↦ by
      apply Subtype.ext
      -- Coercing both torsion levels to their ambient groups exposes naturality of `nsmul`.
      change p • f (proj (n + 1) x : A) = f (proj n x : A)
      rw [← map_nsmul]
      exact congrArg f (congrArg Subtype.val (proj_succ x n))

end Map
end TateModule
end TauCeti
end
end

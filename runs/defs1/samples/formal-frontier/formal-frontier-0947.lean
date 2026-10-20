@[expose] public section

universe u v w x z

/-- The linear maps from `A` to `B`, equipped with a chosen discrete topology
independent of any topology on a space of continuous linear maps. -/
def DiscreteLinHom (k : Type u) (A : Type v) (B : Type w)
    [CommSemiring k] [AddCommMonoid A] [Module k A]
    [AddCommMonoid B] [Module k B] := A →ₗ[k] B

end

@[expose] public section

namespace CategoryTheory

universe v u

variable {T : Type u} [Category.{v} T]

namespace Arrow

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps!]
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom := by cat_disch) : f ≅ g :=
  Comma.isoMk l r h

end Arrow
end CategoryTheory
end

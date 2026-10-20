@[expose] public section

open CategoryTheory Limits

universe v v'

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

namespace mappingCone

open HomComplex

section

variable {K : CochainComplex C ℤ}

variable (α : Cochain F K (-1)) (β : G ⟶ K) (eq : δ (-1) 0 α = Cochain.ofHom (φ ≫ β))

lemma desc_f (p q : ℤ) (hpq : p + 1 = q) :
    (desc φ α β eq).f p = (fst φ).1.v p q hpq ≫ α.v q p (by lia) +
      (snd φ).v p p (add_zero p) ≫ β.f p := by
  simp [ext_from_iff _ _ _ hpq]

end
end mappingCone
end CochainComplex
end

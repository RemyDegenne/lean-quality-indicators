namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections

set_option autoImplicit false

set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open NeronModelInfra AlgebraicGeometry.RelPicard

p2m_reactivate

noncomputable section

namespace ExZar

open NeronModelInfra AlgebraicGeometry.RelPicard CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Datum

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
  {ι : Type u} {U : ι → Scheme.{u}} {u : ∀ i, U i ⟶ Spec (CommRingCat.of R)}
  (f : ∀ i, SchemeHomOver (u i) t) (M : ∀ i, RigidifiedLineBundle c ε (u i))
  (hM : ∀ (i j : ι) (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (p₁ : SchemeHomOver z (u i)) (p₂ : SchemeHomOver z (u j)),
    p₁.1 ≫ (f i).1 = p₂.1 ≫ (f j).1 → Nonempty (((M i).pullbackAlong p₁).L ≅ ((M j).pullbackAlong p₂).L))

p2m_reactivate

def δ (i : ι) : SchemeHomOver (u i) (strMap₁₂ (f i) (f i)) :=
  ⟨pullback.lift (𝟙 _) (𝟙 _) rfl, by rw [pullback.lift_fst_assoc, Category.id_comp]⟩

end Datum
end ExZar
end
end P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_gluing_openCover_of_bijective_sections

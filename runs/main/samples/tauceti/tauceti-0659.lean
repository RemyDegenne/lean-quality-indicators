public section

open CategoryTheory Limits MorphismProperty Topology

universe w u

namespace TauCeti.TopCat

section Pushout

variable {A B X P : TopCat.{u}} {g : A ⟶ X} {m : A ⟶ B} {f : X ⟶ P} {g₂ : B ⟶ P}

theorem exists_disjoint_isOpen_of_isPushout (sq : IsPushout g m f g₂) {U V : Set X}
    (hU : IsOpen U) (hV : IsOpen V) (h : Disjoint U V) {U' V' : Set B} (hU' : IsOpen U')
    (hV' : IsOpen V') (h' : Disjoint U' V') (hUU' : g ⁻¹' U = m ⁻¹' U')
    (hVV' : g ⁻¹' V = m ⁻¹' V') :
    ∃ W W' : Set P, IsOpen W ∧ IsOpen W' ∧ Disjoint W W' ∧ f ⁻¹' W = U ∧ f ⁻¹' W' = V ∧
      g₂ ⁻¹' W = U' ∧ g₂ ⁻¹' W' = V' := by
  have w : g ≫ classify hU hV h = m ≫ classify hU' hV' h' :=
    hom_ext_classifier
      (by rw [← preimage_setOf_fst, ← preimage_setOf_fst, setOf_classify_fst,
        setOf_classify_fst, hUU'])
      (by rw [← preimage_setOf_snd, ← preimage_setOf_snd, setOf_classify_snd,
        setOf_classify_snd, hVV'])
  let σ := sq.desc _ _ w
  exact ⟨_, _, isOpen_setOf_fst σ, isOpen_setOf_snd σ, disjoint_setOf σ,
    by rw [preimage_setOf_fst, sq.inl_desc, setOf_classify_fst],
    by rw [preimage_setOf_snd, sq.inl_desc, setOf_classify_snd],
    by rw [preimage_setOf_fst, sq.inr_desc, setOf_classify_fst],
    by rw [preimage_setOf_snd, sq.inr_desc, setOf_classify_snd]⟩

end Pushout
end TauCeti.TopCat
end

namespace P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u v w z

namespace NilYonedaHom

p2m_open

variable {R : Type u} [CommRing R] {d h : ℕ}

variable (F : MvFormalGroup d R) (G : MvFormalGroup h R)
  (t : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → (Fin h → C))
  (ht_mem : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x : Fin d → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J)
  (ht_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
    (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
    ∀ φ : C →ₐ[R] C', (∀ s ∈ J, φ s ∈ J') →
      ∀ x : Fin d → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x)
  (ht_add : ∀ (C : Type u) [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ x y : Fin d → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
      t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) =
        fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (G.toPowerSeries i))

def comp (i : Fin h) : ∀ (C : Type u) [CommRing C] [Algebra R C], Ideal C → (Fin d → C) → C :=
  fun C _ _ J x => t C J x i

end NilYonedaHom
end
end P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent

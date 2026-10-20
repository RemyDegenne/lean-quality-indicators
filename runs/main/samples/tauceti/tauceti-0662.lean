public section

namespace TauCeti

open Subgroup Submodule

open scoped commutatorElement

universe u

attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

section Two

variable (ρ : gradedPiece 2 (freeProP 2 (Fin n)) 1)

theorem exists_continuousMulEquiv_gradedMap_eq_of_not_isAlt
    (T : gradedPiece 2 (freeProP 2 (Fin n)) 1)
    (hnd : (degreeOneForm ρ).Nondegenerate) (hnalt : ¬ (degreeOneForm ρ).IsAlt)
    (hTnd : (degreeOneForm T).Nondegenerate) (hTnalt : ¬ (degreeOneForm T).IsAlt) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      gradedMap 2 (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
        (e : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1 ρ = T := by
  obtain ⟨φ⟩ := (isSymm_degreeOneForm_of_two rfl ρ).equivalent_of_finrank_eq
    (fun a ↦ isSquare_of_charTwo' a) hnd (fun h ↦ (hnalt h).elim)
    (isSymm_degreeOneForm_of_two rfl T) hTnd (fun h ↦ (hTnalt h).elim) rfl
  obtain ⟨e, he⟩ := exists_continuousMulEquiv_degreeOneForm_gradedMap_dualBasis ρ
    ((dualBasis 2 (Fin n)).map φ.toLinearEquiv.symm)
  refine ⟨e, degreeOneForm_injective_of_two rfl
    (LinearMap.BilinForm.ext_basis (dualBasis 2 (Fin n)) fun i j ↦ ?_)⟩
  have hφ (x : continuousZModDual 2 (freeProP 2 (Fin n))) :
      φ (φ.toLinearEquiv.symm x) = x :=
    φ.toLinearEquiv.apply_symm_apply x
  rw [he, Module.Basis.map_apply, Module.Basis.map_apply, ← φ.map_app, hφ, hφ]

end Two
end freeProP
end TauCeti
end

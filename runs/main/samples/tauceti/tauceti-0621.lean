public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Field

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

attribute [local instance] preprojectiveGradedAlgebra

variable {k}

variable (k Q)

theorem finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner (m : ℕ)
    (i : Symmetrify Q) (v : Q) :
    Module.finrank k (preprojectiveCorner k Q (m + 2) i (Symmetrify.of.obj v)) +
        Module.finrank k (preprojectiveCorner k Q m i (Symmetrify.of.obj v)) =
      ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) i w) +
        Module.finrank k ↥(preprojectiveCorner k Q m i (Symmetrify.of.obj v) ⊓
          ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            LinearMap.ker
              (LinearMap.mulLeft k (preprojectiveMk k Q (ofArrow (Quiver.reverse b))))) := by
  have hΦ := LinearMap.finrank_range_add_finrank_ker (koszulSum (k := k) (m + 1) i v)
  rw [range_koszulSum, ker_koszulSum_succ, finrank_koszulSum_domain] at hΦ
  have hΨ := LinearMap.finrank_range_add_finrank_ker (koszulDiff (k := k) m i v)
  have hK : (LinearMap.ker (koszulDiff (k := k) m i v)).map
      (preprojectiveCorner k Q m i (Symmetrify.of.obj v)).subtype =
        preprojectiveCorner k Q m i (Symmetrify.of.obj v) ⊓
          ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            LinearMap.ker
              (LinearMap.mulLeft k (preprojectiveMk k Q (ofArrow (Quiver.reverse b)))) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun w b => LinearMap.mem_ker.2 ((mem_ker_koszulDiff_iff m i v y).1 hy w b)⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, (mem_ker_koszulDiff_iff m i v _).2 fun w b => LinearMap.mem_ker.1 (hy w b),
        rfl⟩
  rw [← hK, Submodule.finrank_map_subtype_eq]
  -- `simp` cannot reach the degree `m + 1 + 1`, which sits inside the type of a `finrank`.
  rw [Nat.add_assoc, one_add_one_eq_two] at hΦ
  omega

end Field
end TauCeti
end

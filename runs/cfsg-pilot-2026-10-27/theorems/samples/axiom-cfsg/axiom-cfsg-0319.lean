public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise

section PermSurj

variable {W : Type*} [CommGroup W] {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Subgroup W}

theorem exists_smul_eq_perm (hF : PlaneFamily I) (σ : Equiv.Perm ι) :
    ∃ g : MulAut W, ∀ i, g • I i = I (σ i) := by
  classical
  let φ : ∀ i, ↥(I i) ≃* ↥(I (σ i)) := fun i =>
    haveI := hF.klein i
    haveI := hF.klein (σ i)
    (IsKleinFour.nonempty_mulEquiv (G₁ := ↥(I i)) (G₂ := ↥(I (σ i)))).some
  let g : MulAut W := hF.coordEquiv.symm.trans
    ((MulEquiv.piCongrRight φ).trans ((piPermEquiv (fun j => ↥(I j)) σ).trans hF.coordEquiv))
  have hgx : ∀ i, ∀ x : ↥(I i), g (x : W) = ((φ i x : ↥(I (σ i))) : W) := by
    intro i x
    have h : hF.coordEquiv.symm (x : W) = Pi.mulSingle i x := by
      rw [MulEquiv.symm_apply_eq, hF.coordEquiv_mulSingle]
    show hF.coordEquiv (piPermEquiv (fun j => ↥(I j)) σ
      (MulEquiv.piCongrRight φ (hF.coordEquiv.symm (x : W)))) = _
    rw [h]
    have h2 : piPermEquiv (fun j => ↥(I j)) σ (MulEquiv.piCongrRight φ (Pi.mulSingle i x)) =
        Pi.mulSingle (σ i) (φ i x) := by
      funext j
      obtain ⟨k, rfl⟩ := σ.surjective j
      rw [piPermEquiv_apply]
      show φ k ((Pi.mulSingle i x : ∀ k, ↥(I k)) k) = _
      by_cases hk : k = i
      · subst hk
        simp
      · have hk' : σ k ≠ σ i := fun h => hk (σ.injective h)
        rw [Pi.mulSingle_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk', map_one]
    rw [h2, hF.coordEquiv_mulSingle]
  refine ⟨g, fun i => ?_⟩
  ext z
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show g x ∈ I (σ i)
    rw [hgx i ⟨x, hx⟩]
    exact (φ i ⟨x, hx⟩).2
  · intro hz
    obtain ⟨y, hy⟩ := (φ i).surjective ⟨z, hz⟩
    refine ⟨(y : W), y.2, ?_⟩
    show g (y : W) = z
    rw [hgx i y]
    exact congrArg Subtype.val hy

end PermSurj
end CFSG.QuasithinUnique.Setup.Wreath
end

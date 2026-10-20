@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

set_option backward.isDefEq.respectTransparency false in
theorem denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsOpen, hs⟩ ⟨⟨spc, hspc⟩, hmem⟩
  rw [← hs, Set.mem_preimage] at hmem
  rcases (isOpen_pi_iff.mp hsOpen) _ hmem with ⟨J, fJ, hJ1, hJ2⟩
  let N : Subgroup (Abstract G) :=
    iInf fun j : J ↦ j.val.toFiniteIndexNormalSubgroup.toSubgroup
  have hNNormal : N.Normal := Subgroup.normal_iInf_normal fun j ↦ inferInstance
  have hNFinite : N.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : AdmissibleQuotient G :=
    { toFiniteIndexNormalSubgroup :=
        { toSubgroup := N
          isNormal' := hNNormal
          isFiniteIndex' := hNFinite }
      isOpen_comap' := fun i ↦ by
        rw [show
          (((N.comap
            (Monoid.CoprodI.of (M := fun j ↦ G j) : G i →* Abstract G)) :
              Subgroup (G i)) : Set (G i)) =
            ⋂ j : J,
              ((j.val.toFiniteIndexNormalSubgroup.toSubgroup.comap
                (Monoid.CoprodI.of (M := fun k ↦ G k) : G i →* Abstract G) :
                  Subgroup (G i)) : Set (G i)) by
            ext x
            simp [N]]
        exact isOpen_iInter_of_finite fun j ↦ j.val.isOpen_comap' i }
  rcases QuotientGroup.mk'_surjective N (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hs]
  apply hJ2
  intro a ha
  let mToA : m ⟶ a :=
    (iInf_le (fun j : J ↦
      j.val.toFiniteIndexNormalSubgroup.toSubgroup) ⟨a, ha⟩).hom
  rw [← (etaFn G origin).property mToA]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc mToA) (hJ1 a ha).2

end ProfiniteGrp.FreeProduct
end

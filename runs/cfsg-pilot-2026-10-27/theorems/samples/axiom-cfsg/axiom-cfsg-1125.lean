public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

theorem bijOn_prod_relRootGroup
    {k : ℕ} (e : Fin k → Fin Tag.F4.rank → ℤ)
    (he : Function.Injective e) (hrange : Set.range e = {r | IsRoot Tag.F4 r ∧ 0 < height r}) :
    Set.BijOn (fun u : (j : Fin k) → relRootGroup (e j) =>
        (List.ofFn fun j => (u j : ModGL TwistTag.E6.tag K)).prod)
      Set.univ (graphFixedPosUnipotent TwistTag.E6 K barHom) := by
  have hpos : ∀ j, IsRoot Tag.F4 (e j) ∧ 0 < height (e j) := fun j => by
    have h : e j ∈ Set.range e := Set.mem_range_self j
    rw [hrange] at h
    exact h
  obtain ⟨O, hO⟩ : ∃ O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ),
      ∀ j, (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) = relFibre (e j) :=
    ⟨fun j => (relFibre_finite (e j)).toFinset, fun j => Set.Finite.coe_toFinset _⟩
  have hOinj : Function.Injective O := by
    intro i j hij
    obtain ⟨β, hβ, hβr, -⟩ := exists_relProj_fibre (hpos i).1
    have hmem : β ∈ relFibre (e i) := ⟨hβ, hβr⟩
    rw [← hO i, hij, hO j] at hmem
    exact he (hβr.symm.trans hmem.2)
  have hOrange : Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
      (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSet} := by
    ext O'
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨α, hα, hαr, hfib⟩ := exists_relFibre_eq (hpos j).1
      refine ⟨⟨α, hα, Finset.coe_injective ((hfib.symm.trans (hO j).symm))⟩, fun β hβ => ?_⟩
      rw [hO j] at hβ
      refine ⟨hβ.1, ?_⟩
      rw [← height_relProj, hβ.2]
      exact (hpos j).2
    · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
      have hαpos := (hsub (TwistTag.E6.self_mem_diagramOrbit α)).2
      have hr : relProj α ∈ Set.range e := by
        rw [hrange]
        exact ⟨isRoot_relProj hα, by rw [height_relProj]; exact hαpos⟩
      obtain ⟨j, hj⟩ := hr
      exact ⟨j, Finset.coe_injective (by rw [hO j, hj, relFibre_relProj hα])⟩
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => hα) posRootSet_perm posRootSet_closed O hOinj hOrange
  have hfam : (fun j => rootSpan TwistTag.E6.tag K (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.E6 K barHom) = fun j => relRootGroup (e j) :=
    funext fun j => by rw [hO j]
  exact bijOn_prod_congr hfam hbij

end CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
end

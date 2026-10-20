public section

open CategoryTheory

open unitInterval

namespace TauCeti

section

universe u v

variable {E F G : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace X]
  {p : E → X} {q : F → X} {r : G → X}

section BaseHomeomorph

variable {Y : Type v} [TopologicalSpace Y]

-- Not a `simp` lemma: `simp` normalises the coercion `⇑h.toEquiv` inside the type of the fibre
-- equivalence to `⇑h`, so the left-hand side is not in simp normal form.
theorem _root_.IsCoveringMap.compFiberEquiv_monodromy
    (hp : _root_.IsCoveringMap p)
    (h : X ≃ₜ Y) {x y : Y} (a : Path.Homotopic.Quotient x y)
    (e : (h ∘ p) ⁻¹' {x}) :
    Equiv.compFiberEquiv (p := p) h.toEquiv y ((hp.homeomorph_comp h).monodromy a e) =
      hp.monodromy (a.map (h.symm : C(Y, X)))
        (Equiv.compFiberEquiv (p := p) h.toEquiv x e) := by
  obtain ⟨γ⟩ := a
  apply Subtype.ext
  rw [Equiv.compFiberEquiv_apply_coe]
  set ex := Equiv.compFiberEquiv (p := p) h.toEquiv x e
  have hex : (ex : E) = e := Equiv.compFiberEquiv_apply_coe h.toEquiv x e
  let Γ : C(I, E) := hp.liftPath (γ.map h.symm.continuous) ex (by simpa using ex.2.symm)
  have hΓ : Γ = (hp.homeomorph_comp h).liftPath γ e (by
      simpa using e.2.symm) := by
    refine ((hp.homeomorph_comp h).eq_liftPath_iff' (γ_0 := by
      simpa using e.2.symm)).2 ⟨?_, ?_⟩
    · funext t
      -- Expose the composite projection so the lift equation for `Γ` can be applied pointwise.
      change h (p (Γ t)) = γ t
      have hΓt : p (Γ t) = h.symm (γ t) :=
        congrFun (hp.liftPath_lifts (γ.map h.symm.continuous) ex _) t
      rw [hΓt, h.apply_symm_apply]
    · exact (hp.liftPath_zero (γ.map h.symm.continuous) ex _).trans hex
  exact congrArg (fun q : C(I, E) ↦ q 1) hΓ.symm

end BaseHomeomorph
end
end TauCeti
end

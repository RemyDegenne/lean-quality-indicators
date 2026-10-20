namespace P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open MeasureTheory MeasureTheory.Measure TopologicalSpace Function

noncomputable section

namespace P2mTwistedShiftDescent

open AutomorphicForm

section Straighten

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (θ : G →* G) {m : ℕ} (δ : Fin (m + 1) → G)
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]

theorem exists_straighten :
    ∃ (e : sigmaCentralizer (rho θ m) δ ≃ₜ* sigmaCentralizer θ (listProd δ))
      (X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G)),
      (∀ t, ((e t : sigmaCentralizer θ (listProd δ)) : G) = (t : Fin (m + 1) → G) 0) ∧
      MeasurePreserving X (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) ∧
      (∀ p : G × (Fin m → G), X p 0 = p.1) ∧
      (∀ p : G × (Fin m → G),
        (X p)⁻¹ * δ * rho θ m (X p) = string p.2 (p.1⁻¹ * listProd δ * θ p.1)) ∧
      (∀ (t : sigmaCentralizer (rho θ m) δ) (p : G × (Fin m → G)),
        (t : Fin (m + 1) → G) * X p = X (((e t : sigmaCentralizer θ (listProd δ)) : G) * p.1, p.2)) := by

  obtain ⟨Θ, hΘmp, hΘ⟩ :=
    MeasureTheory.exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul μ δ
  have hΘ0 : ∀ x, Θ x 0 = x 0 := fun x => (hΘ x).1
  have hΘs : ∀ x (k : Fin m), Θ x k.succ = (x k.castSucc)⁻¹ * δ k.castSucc * x k.succ :=
    fun x k => (hΘ x).2 k
  have hΘ' : ∀ y, Θ (Θ.symm y) = y := fun y => Θ.apply_symm_apply y
  have hΘc : Continuous Θ := continuous_theta δ Θ hΘ0 hΘs
  have hΘsc : Continuous Θ.symm := continuous_symm δ Θ hΘ0 hΘs Θ.symm hΘ'

  let X : G × (Fin m → G) ≃ₜ (Fin (m + 1) → G) :=
    { toFun := fun p => Θ.symm (Fin.cons p.1 p.2)
      invFun := fun x => (Θ x 0, Fin.tail (Θ x))
      left_inv := fun p => by
        simp only [hΘ', Fin.cons_zero, Fin.tail_cons]
      right_inv := fun x => by
        simp only [Fin.cons_self_tail, MeasurableEquiv.symm_apply_apply]
      continuous_toFun := hΘsc.comp continuous_cons
      continuous_invFun :=
        ((continuous_apply 0).comp hΘc).prodMk ((continuous_pi fun k => continuous_apply _).comp hΘc) }
  have hXapply : ∀ p : G × (Fin m → G), X p = Θ.symm (Fin.cons p.1 p.2) := fun p => rfl
  have hΘX : ∀ p : G × (Fin m → G), Θ (X p) = Fin.cons p.1 p.2 := fun p => by rw [hXapply, hΘ']
  have hX0 : ∀ p : G × (Fin m → G), X p 0 = p.1 := fun p => by
    rw [← hΘ0 (X p), hΘX, Fin.cons_zero]
  have hXtail : ∀ p : G × (Fin m → G), Fin.tail (Θ (X p)) = p.2 := fun p => by
    rw [hΘX, Fin.tail_cons]
  refine ⟨baseEquivₜ δ, X, fun t => rfl, ?_, hX0, fun p => ?_, fun t p => ?_⟩
  ·
    set e₀ := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0 with he₀
    have he₀mp : MeasurePreserving e₀.symm (μ.prod (Measure.pi fun _ => μ)) (Measure.pi fun _ => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have hcomp : (X : G × (Fin m → G) → Fin (m + 1) → G) = Θ.symm ∘ e₀.symm := by
      funext p
      rw [Function.comp_apply, hXapply, he₀, MeasurableEquiv.piFinSuccAbove_symm_apply]
      congr 1
      funext j
      rw [Fin.insertNthEquiv_apply, Fin.insertNth_zero']
    rw [hcomp]
    exact hΘmp.symm.comp he₀mp
  ·
    rw [twistedConj_eq_string θ δ Θ hΘs (X p), hXtail, hX0]
  ·
    apply Θ.injective
    change Θ ((t : Fin (m + 1) → G) * X p) = Θ (X (((t : Fin (m + 1) → G) 0) * p.1, p.2))
    rw [theta_mul_of_mem θ δ Θ hΘ0 hΘs t.2 (X p), hXtail, hX0, hΘX]

end Straighten
end P2mTwistedShiftDescent
end
end P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift

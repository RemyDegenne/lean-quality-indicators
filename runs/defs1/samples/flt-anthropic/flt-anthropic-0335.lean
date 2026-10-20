namespace P2MW.S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

namespace P2mKcBassSerreH1

section Datum

variable {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
  (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
  [DecidableEq (QuotEdge G 𝒯)]
  {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
  (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
  (eV : V ≃ QuotVert G W)

variable (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
  (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)

open Classical in

noncomputable def Bb (w : W) : V → ℤ :=
  fun v => if τ w ≠ 0 ∧ eV v = Quotient.mk (orbitRel G W) w then 1 else 0

end Datum
end P2mKcBassSerreH1
end P2MW.S_CerednikDrinfeld_Mumford_surjective_and_apply_eq_zero_iff_mem_closure_stabilizer_of_apply_eq_pathCycle

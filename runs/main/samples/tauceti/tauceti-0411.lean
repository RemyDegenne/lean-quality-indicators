public section

open Bundle Manifold

open scoped ContDiff Manifold TauCeti

namespace TauCeti.RiemannianIsometry

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [RiemannianBundle (fun y : N' ↦ TangentSpace J' y)]

theorem exists_prodCongr_iff
    (Q : RiemannianIsometry (I.prod J) (I'.prod J') (M × N) (M' × N'))
    [Nonempty M] [Nonempty N] :
    (∃ (Φ : RiemannianIsometry I I' M M') (Ψ : RiemannianIsometry J J' N N'),
      Φ.prodCongr Ψ = Q) ↔ ∃ (f : M → M') (g : N → N'), ⇑Q = Prod.map f g := by
  constructor
  · rintro ⟨Φ, Ψ, rfl⟩
    exact ⟨Φ, Ψ, coe_prodCongr Φ Ψ⟩
  · rintro ⟨f, g, hQ⟩
    exact Q.exists_prodCongr_of_eq_prodMap f g hQ

end TauCeti.RiemannianIsometry
end

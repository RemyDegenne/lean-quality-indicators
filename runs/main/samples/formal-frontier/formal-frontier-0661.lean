public section

open Bundle Set

universe uκ uB uC uF uG uE uE'

namespace Bundle.Trivialization

section IdentityBase

variable {κ : Type uκ} [Semiring κ]
  {B : Type uB} [TopologicalSpace B]
  {F : Type uF} [TopologicalSpace F] [AddCommMonoid F] [Module κ F]
  {G : Type uG} [TopologicalSpace G] [AddCommMonoid G] [Module κ G]
  {E : B → Type uE} [∀ b, AddCommMonoid (E b)] [∀ b, Module κ (E b)]
  {E' : B → Type uE'} [∀ b, AddCommMonoid (E' b)] [∀ b, Module κ (E' b)]
  [TopologicalSpace (TotalSpace F E)] [TopologicalSpace (TotalSpace G E')]

theorem continuousOn_linearMapAt_comp_apply
    (e : Trivialization F (π F E)) [e.IsLinear κ]
    (e' : Trivialization G (π G E')) [e'.IsLinear κ]
    (φ : ∀ b, E b →ₗ[κ] E' b)
    (hφ : Continuous (fun p : TotalSpace F E ↦
      TotalSpace.mk' G p.proj (φ p.proj p.snd))) :
    ContinuousOn (fun p : B × F ↦
      e'.linearMapAt κ p.1 (φ p.1 (e.symmₗ κ p.1 p.2)))
      ((e.baseSet ∩ e'.baseSet) ×ˢ (univ : Set F)) :=
  continuousOn_linearMapAt_comp_apply_over e e' id φ hφ

end IdentityBase
end Bundle.Trivialization
end

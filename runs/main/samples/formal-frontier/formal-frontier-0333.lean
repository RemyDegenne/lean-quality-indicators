set_option warningAsError true

@[expose] public section

noncomputable section

universe uA uB uC uQ uN uE uE'

namespace TopologicalModN

variable {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [IsTopologicalAddGroup C]

omit [IsTopologicalAddGroup B] in
theorem hom_ext (n : ℕ) {f g : TopologicalModN A n →ₜ+ B}
    (h : f.comp (mkQ n) = g.comp (mkQ n)) : f = g := by
  apply ContinuousAddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact DFunLike.congr_fun h a

end TopologicalModN
end
end

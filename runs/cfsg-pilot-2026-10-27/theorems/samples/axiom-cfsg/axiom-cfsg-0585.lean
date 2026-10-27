set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min TensorProduct

theorem isSimpleRep_comp {G H : Type*} [Group G] [Group H] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] {ρ : Representation k H V} (hρ : IsSimpleRep ρ) {π : G →* H}
    (hπ : Function.Surjective π) : IsSimpleRep (ρ.comp π) :=
  ⟨hρ.1, fun W hW => hρ.2 W fun g w hw => by
    obtain ⟨g', rfl⟩ := hπ g
    exact hW g' w hw⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
end

@[expose] public section

namespace Lean4GlCoalgebras

attribute [local implicit_reducible] proof_type

/-- Define the list of premises from a Builder move. -/
def builderMovePremises {Γ : Sequent} {strat : Strategy coalgebraGame Prover}
    (g : proof_type Γ strat) (h : winning strat (startPos Γ)) :
    List (proof_type Γ strat) := match g_def : g with
  | ⟨⟨Sum.inl _, _, _⟩, x, y⟩ => False.elim (by unfold Game.turn at y; simp at y)
  | ⟨⟨Sum.inr R, Γs, Rs⟩, _⟩ =>
    match R with
      | RuleApp.top _ _ => []
      | RuleApp.ax _ _ _ => []
      | RuleApp.or Δ φ1 φ2 φ_in =>
        if rep : (Δ \ {φ1 v φ2}) ∪ {φ1, φ2} ∈ Γs
          then [repNext (Δ := (Δ \ {φ1 v φ2}) ∪ {φ1, φ2}) Γ g (by convert rep; grind)]
              else
                [nextNext (Δ := (Δ \ {φ1 v φ2}) ∪ {φ1, φ2}) g h (by convert rep; grind)
                  (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
      | RuleApp.and Δ φ1 φ2 φ_in =>
        if rep1 : (Δ \ {φ1 & φ2}) ∪ {φ1} ∈ Γs
          then
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then
                [repNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ1}) Γ g (by convert rep1; grind),
                  repNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ2}) Γ g (by convert rep2; grind)]
              else
                [repNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ1}) Γ g (by convert rep1; grind),
                  nextNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ2}) g h (by convert rep2; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
          else
            if rep2 : (Δ \ {φ1 & φ2}) ∪ {φ2} ∈ Γs
              then
                [nextNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ1}) g h (by convert rep1; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp]),
                  repNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ2}) Γ g (by convert rep2; grind)]
              else
                [nextNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ1}) g h (by convert rep1; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp]),
                  nextNext (Δ := (Δ \ {φ1 & φ2}) ∪ {φ2}) g h (by convert rep2; grind)
                    (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]
      | RuleApp.box Δ φ φ_in =>
        if rep : (Δ \ {□φ}).D ∪ {φ} ∈ Γs
          then [repNext (Δ := (Δ \ {□φ}).D ∪ {φ}) Γ g (by convert rep; grind)]
          else
            [nextNext (Δ := (Δ \ {□φ}).D ∪ {φ}) g h (by convert rep; grind)
              (by subst g_def; simp [RuleApp.sequents, builderRuleApp])]

end Lean4GlCoalgebras
end

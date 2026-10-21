namespace OAI

namespace PureTypeSystem

universe u

namespace ContextTower

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

theorem profile_sort (s : S) : Ω.profile (.sort s) = AxProfile P s := by
  ext t
  change (∃ n, PureTypeSystem.HasType P (Ω.context n) ((Expr.sort s).normalForm.rename (Expr.reverseIndex n))
    ((Expr.sort t).rename (Expr.reverseIndex n))) ↔ P.axioms s t
  simp only [Expr.normalForm_of_normal (Normal.sort s),Expr.rename]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨u,ha,hc⟩ := hn.generation
    exact hc.sort_inj ▸ ha
  · intro h; exact ⟨0,PureTypeSystem.HasType.sort_of_valid (Ω.valid 0) h⟩

end ContextTower
end PureTypeSystem
end OAI

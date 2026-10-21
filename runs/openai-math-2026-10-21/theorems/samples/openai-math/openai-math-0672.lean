namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula

universe u

variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_uniformEqualityFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Realize M.sets uniformEqualityFormula
      (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s)))) ↔
      Name.ForcesEq p σ τ := by
  rw [M.forcesEq_iff_exists_certificate s pairing unions powers separation collection carrier order p σ τ hσ hτ,
    uniformEqualityFormula, realize_ex]
  apply exists_congr
  intro S
  apply and_congr_right
  intro hS
  let env := extend S (extend (s.encode p) (extend σ.val (extend τ.val (equalityParameters s))))
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [realize_atomicApplication,
    M.realize_tripleMembershipFormula pairing 1 2 3 0 env
      (M.transitive carrier (s.encode_mem p)) hσ hτ hS, map_empty]
  rfl

end PartitionPilot.Forcing.TransitiveGround
end OAI

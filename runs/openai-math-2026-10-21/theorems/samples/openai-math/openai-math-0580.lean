namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.MapEuler

section

open scoped Classical

open PermutationCycles

variable {O : Type} [Fintype O] (σ α : Equiv.Perm O) (ha : Function.Involutive α)

omit [Fintype O] in
lemma realizeDart_snd (d : (graph σ α ha).Dart) :
    cycle σ (α (realizeDart σ α ha d))=d.snd := d.adj.2.choose_spec.2

end
end TorsionFreeZeroDivisors.MapEuler
end
end OAI

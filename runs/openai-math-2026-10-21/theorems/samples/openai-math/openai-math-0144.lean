namespace OAI

section

namespace ExactQuantumFactoring.TrialControlEmission

open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits OrderTrial

variable {α : Type} {ea : α→List Bool} {k w n : α→ℕ}

lemma reverse {e : ∀x,BooleanNetwork (k x) (w x)}
    (hw : Emits ea unaryCode w) (he : NetEmits ea e) :
    NetEmits ea (fun x=>(e x).rewire Fin.rev):=by
  apply he.rewire (fun _=>Fin.rev)
  apply ofFnDep 0 hw
  have hx:=(BitStackProgram.Emits.id (prodCode unaryCode ea)).precompose
    (fun x:Σa,Fin (w a)=>(x.2.val,x.1))
  exact (((hw.comp hx.snd).unaryNat.natSub (const _ _ 1)).natSub hx.fst.unaryNat).congr (by intro x; change w x.1 - 1 - x.2.val = w x.1 - (x.2.val+1); omega)

end ExactQuantumFactoring.TrialControlEmission
end
end OAI

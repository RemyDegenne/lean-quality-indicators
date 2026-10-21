namespace OAI

noncomputable section

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram

open scoped Classical Matrix

open OccurrenceIncidence VertexTable MatrixExpression HomTransport

variable {F S V R K : Type} {arity : S → ℕ} [CommRing R] [Field K]
    (D : Diagram F S V arity) (s : S) (φ : R →+* K)
    (g : (e : D.Generator) →
      (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) K)ˣ)
    {α β : Type*} [Fintype α] [Fintype β]

lemma childWord_coordinates {m : ℕ} (d : Fin m → ℕ)
    (c : Fin m ≃ Fin (arity s))
    (hc : ∀ i,d i=D.childDim s (c i))
    (old : (i : Fin m) → (Matrix (Fin (d i)) (Fin (d i)) K)ˣ)
    (ho : ∀ i,rebaseUnit (hc i).symm (g (.side ⟨s,some (c i)⟩))=old i)
    (e : ((i : Fin m) × Fin (d i)) ≃ Fin (D.seamDim s))
    (he : e=(Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm) :
    ((MatrixIso.unit ((Term.block (D.childDim s)
      (fun j => Term.inv (D.childWord s j))).eval φ g)).reindex e e).linearEquiv=
      (MatrixIso.block (fun i=>MatrixIso.unit (old i)⁻¹)).linearEquiv := by
  simp only [Term.eval,childWord,sideWord]
  erw [MatrixIso.unit_block,MatrixIso.reindex_reindex_eq,he]
  have he' : ((Equiv.sigmaCongr c (fun i=>finCongr (hc i))).trans
      (blockIndex (D.childDim s)).symm).trans (blockIndex (D.childDim s))=
      Equiv.sigmaCongr c (fun i=>finCongr (hc i)) := by
    rw [Equiv.trans_assoc,Equiv.symm_trans_self,Equiv.trans_refl]
  erw [he',MatrixIso.block_reindex_sigma]
  have hb (i : Fin m) : (MatrixIso.unit (g (.side ⟨s,some (c i)⟩))⁻¹).reindex
      (finCongr (hc i)) (finCongr (hc i))=MatrixIso.unit (old i)⁻¹ := by
    have hh := congrArg (fun z => MatrixIso.unit z⁻¹) (ho i)
    erw [←map_inv,rebaseUnit_iso] at hh
    convert! hh using 1
  convert! congrArg (fun B : (i : Fin m) → MatrixIso K (Fin (d i)) (Fin (d i)) =>
    (MatrixIso.block B).linearEquiv) (funext hb) using 1

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end
end OAI

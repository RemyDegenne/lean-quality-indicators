@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

namespace Formalized

variable {T : LOR.TTheory (V := V)} [R₀Theory T]

namespace TProof

open Language.Theory.TProof Entailment

variable (T)

/-- Imported declaration from the Incompleteness formalization. -/
noncomputable def termEqComplete {n : ℕ} (e : Fin n → V) :
    (t : Semiterm ℒₒᵣ Empty n) → T ⊢ ⌜Rew.embs t⌝^ᵗ/[toNumVec e] =' ↑(t.valbm V e)
  | #z                                 => by simpa using eqRefl T (e z)
  | &x                                 => Empty.elim x
  | Semiterm.func Language.Zero.zero v => by simpa using eqRefl T _
  | Semiterm.func Language.One.one v   => by simpa using eqRefl T _
  | Semiterm.func Language.Add.add v   => by
      simp only [Rew.func, Semiterm.codeIn'_add, Fin.isValue, subst_add, Semiterm.val_func,
        Structure.add_eq_of_lang]
      have ih :
          T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] + ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) ='
              (↑((v 0).valbm V e) + ↑((v 1).valbm V e)) :=
        addExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have :
          T ⊢ ((v 0).valbm V e + (v 1).valbm V e : ⌜ℒₒᵣ⌝[V].Semiterm 0) ='
              ↑((v 0).valbm V e + (v 1).valbm V e) :=
        addComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this
  | Semiterm.func Language.Mul.mul v   => by
      simp only [Rew.func, Semiterm.codeIn'_mul, Fin.isValue, subst_mul, Semiterm.val_func,
        Structure.mul_eq_of_lang]
      have ih :
          T ⊢ (⌜Rew.embs (v 0)⌝^ᵗ/[toNumVec e] * ⌜Rew.embs (v 1)⌝^ᵗ/[toNumVec e]) ='
              (↑((v 0).valbm V e) * ↑((v 1).valbm V e)) :=
        mulExt T _ _ _ _ ⨀ termEqComplete e (v 0) ⨀ termEqComplete e (v 1)
      have :
          T ⊢ ((v 0).valbm V e * (v 1).valbm V e : ⌜ℒₒᵣ⌝[V].Semiterm 0) ='
              ↑((v 0).valbm V e * (v 1).valbm V e) :=
        mulComplete T _ _
      exact eqTrans T _ _ _ ⨀ ih ⨀ this

end TProof
end Formalized
end Arith
end LO
end «lp_nc_section_1»
end

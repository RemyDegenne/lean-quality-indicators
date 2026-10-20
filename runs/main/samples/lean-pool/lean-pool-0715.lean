@[expose] public section

namespace Computability

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible

@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

attribute [local instance] turingPreorder

open scoped Computability

open Encodable

@[inherit_doc] infix:50 " ⊕ " => turingJoin

theorem RecursiveIn_cond_core_rfind {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    ∃ cmp : ℕ →. ℕ,
      RecursiveIn O cmp ∧
        (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) =
          (fun n => cond (c n) (f n) (g n)) := by
  let eqF : ℕ →. ℕ := fun p =>
    (Nat.pair <$>
        ((fun n : ℕ => (Nat.unpair n).1) p >>= f) <*>
        (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01
  let eqG : ℕ →. ℕ := fun p =>
    (Nat.pair <$>
        ((fun n : ℕ => (Nat.unpair n).1) p >>= g) <*>
        (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01
  let c1 : ℕ → Bool := fun p => c (Nat.unpair p).1
  let c2 : ℕ → Bool := fun p => !c (Nat.unpair p).1
  have hc1 : Computable c1 := by
    have hleft : Computable (fun p : ℕ => (Nat.unpair p).1) :=
      Computable.fst.comp Computable.unpair
    simpa [c1] using hc.comp hleft
  have hc2 : Computable c2 := by
    have hnot : Computable not := Primrec.not.to_comp
    simpa [c2] using hnot.comp hc1
  have heqF : RecursiveIn O eqF := eqCmp_recursiveIn hf
  have heqG : RecursiveIn O eqG := eqCmp_recursiveIn hg
  let t1 : ℕ →. ℕ := fun p => bif c1 p then eqF p else Part.some 1
  let t2 : ℕ →. ℕ := fun p => bif c2 p then eqG p else Part.some 1
  have ht1 : RecursiveIn O t1 := by
    simpa [t1] using (RecursiveIn_cond_const (O := O) (c := c1) (f := eqF) hc1 heqF 1)
  have ht2 : RecursiveIn O t2 := by
    simpa [t2] using (RecursiveIn_cond_const (O := O) (c := c2) (f := eqG) hc2 heqG 1)
  let mulPair : ℕ →. ℕ := (Nat.unpaired (fun a b : ℕ => a * b) : ℕ → ℕ)
  have hmul : RecursiveIn O mulPair := by
    have hpart : Nat.Partrec (mulPair : ℕ →. ℕ) := by
      simpa [mulPair] using (Nat.Partrec.of_primrec (Nat.Primrec.mul))
    exact recursiveIn_of_partrec (O := O) hpart
  let cmp : ℕ →. ℕ := fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair
  have hcmp : RecursiveIn O cmp := by
    have hpair : RecursiveIn O (fun p => Nat.pair <$> t1 p <*> t2 p) :=
      RecursiveIn.pair ht1 ht2
    have : RecursiveIn O (fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair) :=
      RecursiveIn.comp hmul hpair
    simpa [cmp] using this
  refine ⟨cmp, hcmp, ?_⟩
  funext n
  let φ : ℕ → Bool := fun m => decide (m = 0)
  cases hn : c n with
  | true =>
      simp only [Part.map_eq_map, cond]
      have hpred :
          (fun k => Part.map φ (cmp (Nat.pair n k))) =
            (fun k => Part.map φ (((Nat.pair <$> f n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> f n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_some_right, pfun_bind_some, pfun_bind_coe]
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := f n)
  | false =>
      simp only [Part.map_eq_map, cond]
      have hpred :
          (fun k => Part.map φ (cmp (Nat.pair n k))) =
            (fun k => Part.map φ (((Nat.pair <$> g n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> g n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_some, pfun_bind_some, pfun_bind_coe, Part.map_map,
            Function.comp_def, Part.map_id']
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := g n)

end Computability
end

@[expose] public section

namespace Complexity

namespace RAM

namespace TMConfig

namespace Sparse

theorem dispatchSymbols_exec_internal {tm : TM n}
    {cfg next : Complexity.Cfg n tm.Q} {store : Structured.Store}
    (state : tm.Q) (actual symbols : Fin (n + 2) → Γ)
    (remaining : List (Fin (n + 2)))
    (hstate : state = cfg.state)
    (hstep : tm.step cfg = some next)
    (hrepresents : Represents tm cfg store)
    (hworkStart : ∀ i, (cfg.work i).cells 0 = Γ.start)
    (houtputStart : cfg.output.cells 0 = Γ.start)
    (hone : store (oneReg n) = 1)
    (htapeCount : store (tapeCountReg n) = n + 2)
    (hactual : actual = readSymbols cfg)
    (hloaded : ∀ tape, tape ∈ remaining →
      store (symbolReg n tape) = symbolCode (actual tape))
    (hassigned : ∀ tape, tape ∉ remaining → symbols tape = actual tape)
    (hnodup : remaining.Nodup) :
    ∃ final cost space,
      Structured.Exec (dispatchSymbols tm state remaining symbols)
        store final (dispatchSteps tm state actual remaining) cost space ∧
      Represents tm next final := by
  subst state
  subst actual
  induction remaining generalizing symbols store with
  | nil =>
      have hsymbols : symbols = readSymbols cfg := by
        funext tape
        exact hassigned tape (by simp)
      subst symbols
      obtain ⟨cost, space, hexec⟩ :=
        Structured.Internal.exec_basics_exists
          (actionOps tm cfg.state (readSymbols cfg)) store
      refine ⟨Structured.Basic.execList
        (actionOps tm cfg.state (readSymbols cfg)) store,
        cost, space, ?_, ?_⟩
      · simpa [dispatchSymbols, action, dispatchSteps] using hexec
      · exact actionOps_represents_internal hstep hrepresents hworkStart
          houtputStart hone htapeCount
  | cons tape rest ih =>
      have htapeCode := hloaded tape (by simp)
      have htestOne : symbolReg n tape ≠ oneReg n :=
        symbolReg_ne_one n tape
      let cleared := Structured.Switch.cleared store (symbolReg n tape)
      have hrange := scratch_range_internal n
      have hclearedRepresents : Represents tm cfg cleared :=
        cleared_represents hrepresents (hrange.2.2.2.2.2.2 tape).1
          (hrange.2.2.2.2.2.2 tape).2
      have hclearedOne : cleared (oneReg n) = 1 := by
        exact (cleared_apply_of_ne store htestOne.symm).trans hone
      have hclearedCount : cleared (tapeCountReg n) = n + 2 := by
        have hne : tapeCountReg n ≠ symbolReg n tape := by
          simp [tapeCountReg, symbolReg]
          omega
        exact (cleared_apply_of_ne store hne).trans htapeCount
      have hclearedLoaded : ∀ candidate, candidate ∈ rest →
          cleared (symbolReg n candidate) =
            symbolCode (readSymbols cfg candidate) := by
        intro candidate hcandidate
        have hne : candidate ≠ tape := by
          intro heq
          subst candidate
          exact (List.nodup_cons.mp hnodup).1 hcandidate
        have hregs : symbolReg n candidate ≠ symbolReg n tape :=
          fun heq => hne ((symbolReg_injective n) heq)
        exact (cleared_apply_of_ne store hregs).trans
          (hloaded candidate (by simp [hcandidate]))
      have hclearedAssigned : ∀ candidate, candidate ∉ rest →
          Function.update symbols tape (readSymbols cfg tape) candidate =
            readSymbols cfg candidate := by
        intro candidate hnot
        by_cases heq : candidate = tape
        · subst candidate
          simp
        · rw [Function.update_of_ne heq]
          exact hassigned candidate (by simp [heq, hnot])
      obtain ⟨final, branchCost, branchSpace, hbranch, hfinalRepresents⟩ :=
        ih (symbols := Function.update symbols tape (readSymbols cfg tape))
          (store := cleared) hclearedRepresents hclearedOne hclearedCount
          (List.nodup_cons.mp hnodup).2 hclearedLoaded hclearedAssigned
      have hselectedBranch :
          ∃ cost space,
            Structured.Exec
              ((fun code : Fin 4 =>
                dispatchSymbols tm cfg.state rest
                  (Function.update symbols tape (symbolDecode code.val)))
                ⟨symbolCode (readSymbols cfg tape),
                  symbolCode_lt_internal (readSymbols cfg tape)⟩)
              cleared final
              (dispatchSteps tm cfg.state (readSymbols cfg) rest)
              cost space := by
        refine ⟨branchCost, branchSpace, ?_⟩
        simpa [symbolDecode_code_internal] using hbranch
      obtain ⟨cost, space, hexec⟩ := Structured.Switch.select_exec
        (fun code : Fin 4 =>
          dispatchSymbols tm cfg.state rest
            (Function.update symbols tape (symbolDecode code.val)))
        store final (symbolCode_lt_internal (readSymbols cfg tape))
        htapeCode hone htestOne hselectedBranch
      refine ⟨final, cost, space, ?_, hfinalRepresents⟩
      simpa [dispatchSymbols, dispatchSteps] using hexec

end Sparse
end TMConfig
end RAM
end Complexity
end

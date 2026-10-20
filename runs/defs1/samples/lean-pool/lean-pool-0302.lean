public section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol

open NFChoice.Foundation

open NFChoice.Foundation.ExactLiteralTrial

open NFChoice.SemanticCore

open NFChoice.ReplaySupport

open NFChoice.Compiler.CompactSourceSyntax

open NFChoice.Compiler.CompactSyntaxFVExplicit

open NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Compiler.CoreFVSimp

open NFChoice.DefinitionLeaves.AlphaFocusedSupport

open NFChoice.DefinitionLeaves.AlphaFocusedFV

open NFChoice.DirectNominalPrf

open NFChoice.DirectNominalPrf.Nominal

namespace SingletonImageAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0009`. -/
@[expose]
noncomputable def splitAlpha0009 (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (dv_w_z : w ≠ z) :
    TAlphaWff
      [((alphaDummy050 A), (alphaDummy051 z w)), ((alphaDummy000 A), w),
        ((alphaDummy003 A), z), ((alphaDummy002 A), y), ((alphaDummy001 A), x),
        ((alphaDummy004 A), (alphaDummy005 x y z w A))]
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy050 A)) (synCcompl
            (Class.cab (alphaDummy046 A)
              (synWrex (alphaDummy047 A) (Class.cv (alphaDummy003 A))
                (Wff.classEq (Class.cv (alphaDummy046 A))
                  (synCphi (Class.cv (alphaDummy047 A)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy050 A)) (synCcompl
              (Class.cab (alphaDummy046 A)
                (synWrex (alphaDummy047 A) (Class.cv (alphaDummy000 A))
                  (Wff.classEq (Class.cv (alphaDummy046 A))
                    (synCun (synCphi (Class.cv (alphaDummy047 A)))
                      (synCsn (synC0c))))))))))
      (Wff.imp (Wff.classMem (Class.cv (alphaDummy051 z w)) (synCcompl
            (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv z)
                (Wff.classEq (Class.cv (alphaDummy048 z w))
                  (synCphi (Class.cv (alphaDummy049 z w)))))))) (Wff.neg
          (Wff.classMem (Class.cv (alphaDummy051 z w)) (synCcompl
              (Class.cab (alphaDummy048 z w) (synWrex (alphaDummy049 z w) (Class.cv w)
                  (Wff.classEq (Class.cv (alphaDummy048 z w))
                    (synCun (synCphi (Class.cv (alphaDummy049 z w)))
                      (synCsn (synC0c)))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w A dv_w_z)))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.neg (splitAlpha0006 x y z w A dv_w_z)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy003 A))).fv ∪
                                ((Class.cv (alphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy078 A), (alphaDummy079 z w)),
                                    ((alphaDummy047 A), (alphaDummy049 z w)),
                                    ((alphaDummy046 A), (alphaDummy048 z w)),
                                    ((alphaDummy076 A), (alphaDummy077 z w)),
                                    ((alphaDummy050 A), (alphaDummy051 z w)),
                                    ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                                    ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                    ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 1))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 1))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0074 A) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0076 z w) 0))
                              (TAlphaVar.there
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0078 A) 0))
                                (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0079 z w) 0))
                                (TAlphaVar.there
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0075 A) 0))
                                  (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0077 z w) 0))
                                  (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (alphaDummy003 A))).fv ∪
                                ((Class.cv (alphaDummy000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv z)).fv ∪ ((Class.cv w)).fv)
                              (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A)))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (splitAlpha0008 x y z w A))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.reflOfClosed
                                  [((alphaDummy078 A), (alphaDummy079 z w)),
                                    ((alphaDummy047 A), (alphaDummy049 z w)),
                                    ((alphaDummy046 A), (alphaDummy048 z w)),
                                    ((alphaDummy076 A), (alphaDummy077 z w)),
                                    ((alphaDummy050 A), (alphaDummy051 z w)),
                                    ((alphaDummy000 A), w), ((alphaDummy003 A), z),
                                    ((alphaDummy002 A), y), ((alphaDummy001 A), x),
                                    ((alphaDummy004 A), (alphaDummy005 x y z w A))]
                                  (synCcompl (synCsn (synC0c))) (by
                                    simp only [fv_syn_ccompl, fv_syn_csn,
                                      fv_syn_c0c])))))))))))))))))

end SingletonImageAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end

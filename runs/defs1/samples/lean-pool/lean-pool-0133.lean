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

namespace CompositionAlpha

/-- Proof-translation construction identified upstream as `split_alpha_0000`. -/
@[expose]
noncomputable def splitAlpha0000 (x : Var) (y : Var) (z : Var) (A : Class) (B : Class) :
    TAlphaWff
      [((alphaDummy021 A B), (alphaDummy024 x y)),
        ((alphaDummy020 A B), (alphaDummy023 x y)),
        ((alphaDummy019 A B), (alphaDummy022 x y)),
        ((alphaDummy017 A B), (alphaDummy018 x y)),
        ((alphaDummy013 A B), (alphaDummy015 x y)),
        ((alphaDummy014 A B), (alphaDummy016 x y)),
        ((alphaDummy006 A B), (alphaDummy008 x y)),
        ((alphaDummy005 A B), (alphaDummy007 x y)),
        ((alphaDummy011 A B), (alphaDummy012 x y)),
        ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
        ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy019 A B))
            (synCun (Class.cv (alphaDummy020 A B)) (Class.cv (alphaDummy021 A B))))))
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y))) (synC0))
        (Wff.neg (Wff.classEq (Class.cv (alphaDummy022 x y))
            (synCun (Class.cv (alphaDummy023 x y)) (Class.cv (alphaDummy024 x y)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0018 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0019 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0016 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0017 x y) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0022 A B) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0023 x y) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0020 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0021 x y) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((alphaDummy021 A B), (alphaDummy024 x y)),
          ((alphaDummy020 A B), (alphaDummy023 x y)),
          ((alphaDummy019 A B), (alphaDummy022 x y)),
          ((alphaDummy017 A B), (alphaDummy018 x y)),
          ((alphaDummy013 A B), (alphaDummy015 x y)),
          ((alphaDummy014 A B), (alphaDummy016 x y)),
          ((alphaDummy006 A B), (alphaDummy008 x y)),
          ((alphaDummy005 A B), (alphaDummy007 x y)),
          ((alphaDummy011 A B), (alphaDummy012 x y)),
          ((alphaDummy009 A B), (alphaDummy010 x y)), ((alphaDummy001 A B), y),
          ((alphaDummy000 A B), x), ((alphaDummy003 A B), (alphaDummy004 x y z A B))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
              (by decide))
            (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
              (by decide)) (TAlphaVar.there
              (freshVar_injective (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                (by decide))
              (freshVar_injective (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0026 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0027 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0024 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0025 x y) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (alphaDummy013 A B))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (alphaDummy015 x y))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0030 A B) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0031 x y) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0028 A B) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (support_mem_0029 x y) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end CompositionAlpha
end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
end

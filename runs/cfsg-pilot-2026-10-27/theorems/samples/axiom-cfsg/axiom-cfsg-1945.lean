public section

namespace CFSG.RankThree.GF2n.Stroth80

section Certs

theorem stroth311aStatement_unconditional : Stroth311aStatement :=
  stroth311a_of_theoremX stroth34Statement_unconditional stroth310Statement_unconditional
    theoremXStatement_holds
    (griessCoverStatement_of_table
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      griessSL34Statement_holds)
    (stroth311Conj_of_theoremX stroth34Statement_unconditional theoremXStatement_holds)

end Certs
end CFSG.RankThree.GF2n.Stroth80
end

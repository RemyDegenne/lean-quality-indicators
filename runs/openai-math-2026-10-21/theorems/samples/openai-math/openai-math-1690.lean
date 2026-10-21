namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.PortTableLookup

variable {n d : Nat}

theorem accepts_word (table : PortTables.Table n d) (e : Fin n × Fin d)
    (a b : PortTables.Label) :
    (PortTables.tableWords table)[4 + 4098 * (PortTables.rowIndex n d e).val +
        (GraphTables.relationIndex (a, b)).val]? =
      some (GraphTables.bitWord (PortTables.accepts table e a b)) :=
  relation_word table (PortTables.rowIndex n d e) (GraphTables.relationIndex (a, b))

end UniqueGamesTheorem.Foundations.PCP.PortTableLookup
end
end OAI

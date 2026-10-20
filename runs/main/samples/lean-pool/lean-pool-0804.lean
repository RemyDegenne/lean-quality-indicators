@[expose] public section

namespace RS

theorem leftRotatePairs_perm
    (s t u : ℕ) :
    (nBlock s t u ++
      (pBlock s t u ++
        mBlock s t u)).Perm
    (mBlock s t u ++
      (pBlock s t u ++
        nBlock s t u)) :=
  (List.perm_append_comm_assoc _ _ _).trans
    ((List.Perm.append_left _
        List.perm_append_comm).trans
      (List.perm_append_comm_assoc _ _ _))

end RS
end

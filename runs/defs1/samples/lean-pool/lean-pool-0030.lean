@[expose] public section

namespace RS

/-- **The block factorization**: a block-sorted multi-star is the
iterated tensor of vertex stars with the circles split off. -/
noncomputable def multiStarBlocks :
    ∀ (ds : List ℕ) (c : ℕ),
      (multiStar (blockAssign ds) c).Equiv
        (addCircles (starTensor ds) c)
  | [], c => multiStarNil c
  | d :: ds, c => by
    refine (multiStarPeel d ds.sum c (blockAssign ds)
      (blockAssign (d :: ds))
      (fun i => dite_eq_left i.isLt)
      (fun j => by
        have h1 : ¬ ((Fin.natAdd d j :
            Fin (d + ds.sum)).val < d) := by
          change ¬ (d + j.val < d)
          omega
        refine (dite_eq_right h1).trans ?_
        refine congrArg Fin.succ
          (congrArg (blockAssign ds) (Fin.ext ?_))
        change d + j.val - d = j.val
        omega)).trans ?_
    refine (Fragment.Equiv.relabelCongr
      (tensorFragmentCongr (Fragment.Equiv.refl _)
        (Fragment.Equiv.relabelCongr
          (multiStarBlocks ds c) _)) _).trans ?_
    change ((tensorFragment
        ((vertexStar d).relabel (finCongr
          (by omega : d = 0 + d)))
        (addCircles ((starTensor ds).relabel (finCongr
          (by omega : ds.sum = 0 + ds.sum))) c)).relabel
        (finCongr (by omega :
          (0 + 0) + (d + ds.sum) = d + ds.sum))).Equiv
      (addCircles (starTensor (d :: ds)) c)
    exact Fragment.Equiv.relabelCongr
      (tensorAddCirclesRight
        ((vertexStar d).relabel (finCongr
          (by omega : d = 0 + d)))
        ((starTensor ds).relabel (finCongr
          (by omega : ds.sum = 0 + ds.sum))) c) _

end RS
end

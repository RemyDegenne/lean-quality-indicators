public section

namespace CFSG.YGroups

open CFSG.Open (MonsterY443 MonsterY443Gen MonsterY443Adj monsterY443Rels monsterY443ArmLength
  monsterY443SpiderWord)

open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

namespace Y443

theorem evalWord_replicate_flatten {G : Type*} [Group G] (g : ℕ → G) (w : List ℕ) (n : ℕ) :
    evalWord g (List.replicate n w).flatten = (evalWord g w) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, evalWord_append, ih, pow_succ']

end Y443
end CFSG.YGroups
end

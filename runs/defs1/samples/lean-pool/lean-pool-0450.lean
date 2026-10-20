@[expose] public section

namespace MatchingLogic

namespace Sorted

variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]

/-- `⇒`, the reflexive transitive closure of `Feeds`. -/
abbrev FeedsStar (S : MSignature) : S.Srt → S.Srt → Prop :=
  Relation.ReflTransGen (Feeds S)

end Sorted
end MatchingLogic
end

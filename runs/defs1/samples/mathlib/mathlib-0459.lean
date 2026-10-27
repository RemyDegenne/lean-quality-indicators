@[expose] public section

export LucasLehmer (LucasLehmerTest lucasLehmerResidue)

open LucasLehmer

namespace LucasLehmer

namespace norm_num_ext

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

/-- Tail-recursive version of `sModNat`. -/
@[expose] meta def sModNatTR (q k : ℕ) : ℕ :=
  go k (4 % q)
where
  /-- Helper function for `sMod''`. -/
  go : ℕ → ℕ → ℕ
  | 0, acc => acc
  | n + 1, acc => go n ((acc ^ 2 + (q - 2)) % q)
termination_by structural x => x

end norm_num_ext
end LucasLehmer
end

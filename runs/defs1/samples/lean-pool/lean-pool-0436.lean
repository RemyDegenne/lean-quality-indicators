@[expose] public section

namespace QECCertificates.LRAT

/-- Unit propagation along the hint sequence. `h` is a 1-based clause number. -/
def rupAux {K : Type} (D : ClauseDB K) (d : K) (a : PAssign) : List Nat → Bool
  | [] => false
  | h :: rest =>
      match D.get? d (h - 1) with
      | none => false
      | some E =>
          match scan a E with
          | [] => true
          | [l] => rupAux D d (l :: a) rest
          | _ => false

end QECCertificates.LRAT
end

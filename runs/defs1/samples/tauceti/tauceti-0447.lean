public section

namespace List

variable {R : Type*} [Zero R] [LinearOrder R]

/-- The sign of the first nonzero entry of a list, or `0` if every entry is zero. -/
def firstSign (l : List R) : SignType :=
  ((l.filter (fun v => decide (v ≠ 0))).head?.map SignType.sign).getD 0

end List
end

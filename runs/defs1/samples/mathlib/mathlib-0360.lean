open scoped Finset

public section

namespace Finsupp

open Lean Parser Term

@[nolint docBlame] -- we do not want any doc hover on this notation.
meta def fun₀.matchAlts : Parser :=
  leading_parser withPosition <| ppRealGroup <| many1Indent (ppSpace >> ppGroup matchAlt)

end Finsupp
end

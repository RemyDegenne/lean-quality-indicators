@[expose] public section

namespace RS

theorem pairedLedger : EdgeSubset.PairedLedger :=
  EdgeSubset.pairedLedger_iff_unsigned.mpr pairedLedgerUnsigned

end RS
end

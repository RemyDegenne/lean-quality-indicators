@[expose] public section

namespace BGS.NumberTheory

namespace RankinJointEnvelopeFiniteCertificate

/-- The Boolean check of the certificate's envelope leaves. -/
def check (cert : RankinJointEnvelopeFiniteCertificate) : Bool :=
  allRankinJointEnvelopeLeavesCheck cert.cutoff cert.profiles

end RankinJointEnvelopeFiniteCertificate
end BGS.NumberTheory
end

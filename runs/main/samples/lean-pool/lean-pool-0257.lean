@[expose] public section

namespace FD1D

namespace BellmanCertificate

namespace DPoly

theorem eval_mul [Zero R] [Add R] [Mul R] [CommRing S]
    (f : R → S) (hf0 : f 0 = 0)
    (hfadd : ∀ a b, f (a + b) = f a + f b)
    (hfmul : ∀ a b, f (a * b) = f a * f b)
    (x : S) (p q : DPoly R) :
    eval f x (mul p q) = eval f x p * eval f x q := by
  exact evalCoeffs_mul f hf0 hfadd hfmul x p.coeffs q.coeffs

end DPoly
end BellmanCertificate
end FD1D
end

import Std

namespace Reimann.CircularGauss69

def coeff {A : Type} [OfNat A 0] (p : List A) (n : Nat) : A := p[n]?.getD 0

def sumBelow {A : Type} [OfNat A 0] [Add A] (f : Nat → A) : Nat → A
  | 0 => 0
  | n+1 => sumBelow f n + f n

def convolution {A : Type} [OfNat A 0] [Add A] [Mul A] (a b : Nat → A) (n : Nat) : A :=
  sumBelow (fun i => a i * b (n-i)) (n+1)

end Reimann.CircularGauss69

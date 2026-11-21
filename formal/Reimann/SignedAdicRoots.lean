import Reimann.DyadicSplitRoot

/-! Exact factorization of the dyadic quadratic in the ring of compatible binary residues. -/
namespace Reimann.SignedAdicRoots

open Reimann.DyadicLattice

/-- Undo the substitution w = -y/b at one precision when b is invertible. -/
theorem undo_rescaling {n : Nat} (b c i w : BitVec n) (hi : b*i=1)
    (hw : w*w+c*(i*i)=w) : (-b*w)*(-b*w) + b*(-b*w) + c = 0 := by
  have hc : (b*b)*(c*(i*i))=c := calc
    _ = (b*i)*(b*i)*c := by grind
    _ = c := by rw [hi]; simp
  calc
    _ = (b*b)*(w*w+c*(i*i)) - (b*b)*w := by
      rw [BitVec.mul_add, hc]
      grind
    _ = 0 := by rw [hw]; simp

/-- The scaled polynomial y²+by+c over the full inverse limit has an even root. -/
theorem even_root (b c : Scalar) (hb : b.residue 0=1) (hc : c.residue 0=0) :
    ∃ y : Scalar, y.residue 0=0 ∧
      ∀ n, y.residue n*y.residue n+b.residue n*y.residue n+c.residue n=0 := by
  obtain ⟨i,hi⟩ := odd_scalar_inverse b hb
  let k := mul c (mul i i)
  have hk : k.residue 0=0 := by simp [k,mul,hc]
  obtain ⟨w,hw,he⟩ := DyadicSplitRoot.coherent_even_root k hk
  let y := mul (neg b) w
  refine ⟨y,by simp [y,mul,neg,hw],?_⟩
  intro n
  have eqn := congrArg (fun x : Scalar => x.residue n) he
  exact undo_rescaling _ _ _ _ (hi n) eqn

/-- The other scaled root follows from Vieta, and has opposite parity. -/
theorem scaled_factors (b c : Scalar) (hb : b.residue 0=1) (hc : c.residue 0=0) :
    ∃ y z : Scalar, y.residue 0=0 ∧ z.residue 0=1 ∧
      ∀ n, y.residue n+z.residue n= -b.residue n ∧ y.residue n*z.residue n=c.residue n := by
  obtain ⟨y,hy,root⟩ := even_root b c hb hc
  let z := add (neg b) (neg y)
  have hz : z.residue 0=1 := by rw [show z.residue 0= -b.residue 0 + -y.residue 0 from rfl,hb,hy]; decide
  refine ⟨y,z,hy,hz,?_⟩
  intro n
  have h := root n
  change y.residue n+(-b.residue n + -y.residue n)= -b.residue n ∧
    y.residue n*(-b.residue n + -y.residue n)=c.residue n
  constructor <;> grind

/-- Vieta for the original T-polynomial in the inverse-limit model of the 2-adic integers. -/
theorem monic_factors (b c : Scalar) (hb : b.residue 0=1) (hc : c.residue 0=0) :
    ∃ R S : Scalar, ∀ n, R.residue n+S.residue n= -(2*b.residue n) ∧
      R.residue n*S.residue n=4*c.residue n := by
  obtain ⟨y,z,_,_,h⟩ := scaled_factors b c hb hc
  refine ⟨add y y,add z z,?_⟩
  intro n
  have ⟨hs,hp⟩ := h n
  change y.residue n+y.residue n+(z.residue n+z.residue n)= -(2*b.residue n) ∧
    (y.residue n+y.residue n)*(z.residue n+z.residue n)=4*c.residue n
  constructor <;> grind

/-- Exact homogeneous factorization at all precisions using the same two coherent roots. -/
theorem homogeneous_factorization (b c : Scalar) (hb : b.residue 0=1) (hc : c.residue 0=0) :
    ∃ R S : Scalar, ∀ n (s a : BitVec (n+1)),
      (s-a)*(s-a) + (2*b.residue n)*a*(s-a) + (4*c.residue n)*a*a =
      ((s-a)-a*R.residue n)*((s-a)-a*S.residue n) := by
  obtain ⟨R,S,h⟩ := monic_factors b c hb hc
  refine ⟨R,S,?_⟩
  intro n s a
  have ⟨h₁,h₂⟩ := h n
  have hsum : 2*b.residue n = -(R.residue n+S.residue n) := by rw [h₁]; simp
  rw [hsum,←h₂]
  grind

theorem scaled_labels_four : ∀ y z : BitVec 2,
    y.setWidth 1=0 → y+z= -1 → y*z=2 → y=2 ∧ z=1 := by decide

theorem doubled_labels_eight : ∀ y z : BitVec 3,
    y.setWidth 2=2 → z.setWidth 2=1 → y+y=4 ∧ z+z=2 := by decide

theorem factor_from_scaled_vieta {n : Nat} (b c y z s a : BitVec n)
    (hs : y+z= -b) (hp : y*z=c) :
    (s-a)*(s-a) + (2*b)*a*(s-a) + (4*c)*a*a =
    ((s-a)-a*(y+y))*((s-a)-a*(z+z)) := by
  have hb : b= -(y+z) := by rw [hs]; simp
  rw [hb,←hp]
  grind

/-- At the two low-bit values forced by weight three the roots have disjoint labels modulo eight.
The polynomial identity is an equality of coherent scalars, for any two coherent inputs. -/
theorem labelled_scalar_factorization (b c : Scalar) (hb : b.residue 1=1) (hc : c.residue 1=2) :
    ∃ R S : Scalar, R.residue 2=4 ∧ S.residue 2=2 ∧ ∀ s a : Scalar,
      let x := add s (neg a)
      add (add (mul x x) (mul (mul (add b b) a) x))
        (mul (mul (add (add c c) (add c c)) a) a) =
        mul (add x (neg (mul a R))) (add x (neg (mul a S))) := by
  have hbl := b.reduce (i:=0) (j:=1) (by decide)
  have hcl := c.reduce (i:=0) (j:=1) (by decide)
  rw [hb] at hbl
  rw [hc] at hcl
  obtain ⟨y,z,hy,_,roots⟩ := scaled_factors b c hbl.symm hcl.symm
  have ⟨hs,hp⟩ := roots 1
  rw [hb] at hs
  rw [hc] at hp
  have ⟨y4,z4⟩ := scaled_labels_four _ _ ((y.reduce (i:=0) (j:=1) (by decide)).trans hy) hs hp
  have ⟨y8,z8⟩ := doubled_labels_eight _ _ ((y.reduce (i:=1) (j:=2) (by decide)).trans y4)
    ((z.reduce (i:=1) (j:=2) (by decide)).trans z4)
  refine ⟨add y y,add z z,y8,z8,?_⟩
  intro s a
  apply scalar_ext
  intro n
  have ⟨sn,pn⟩ := roots n
  have H := factor_from_scaled_vieta _ _ _ _ (s.residue n) (a.residue n) sn pn
  simp only [add, neg, mul]
  grind

end Reimann.SignedAdicRoots

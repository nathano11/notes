import Reimann.PairedSigns
import Reimann.WeightClasses

/-!
Consequences of the two signed residues for equation (9) of
`Dyadic_Window_Orders.md`, §8. The specialization of the integral
polynomials and Smith formula to the strict groups is an arithmetic input.
-/

namespace Reimann.PairedOrders

open Reimann.Dyadic Reimann.SampleSpacing Reimann.PairedSigns

/-- Exact finite valuations of the cleared numerators at the indicated weight,
in the order (plus, minus). The cleared denominator is the odd number 5^(2r). -/
def PairAt (c0 c1 : Int) (r α β : Nat) : Prop :=
  exactV (numerator c0 c1 1 (5^r)) α ∧ exactV (numerator c0 c1 (-1) (5^r)) β

/-- A dyadic valuation at least six forces a zero residue modulo 64. -/
theorem residue_zero_of_deep {x : Int} {n : Nat} (hx : exactV x n) (hn : 6 ≤ n) :
    x % 64 = 0 := by
  obtain ⟨u, hu⟩ := hx
  have en : n = 6 + (n-6) := by omega
  rw [en, twoPower_add] at hu
  change x = (64 * twoPower (n-6)) * (2*u+1) at hu
  rw [hu, Int.mul_assoc]
  simp

/-- The possible finite valuations for the three types of residues in the table. -/
theorem valuation_of_residue {x : Int} {n : Nat} (hx : exactV x n) :
    ((x%64=16 ∨ x%64=48) → n=4) ∧ (x%64=32 → n=5) ∧ (x%64=0 → 6≤n) := by
  by_cases deep : 6 ≤ n
  · have h := residue_zero_of_deep hx deep
    omega
  obtain ⟨u, hu⟩ := hx
  have cases' : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
  rcases cases' with h | h | h | h | h | h <;> subst n <;>
    simp [twoPower] at hu <;> omega

/-- Group the two congruences 1 and 5 modulo 8, retaining the sign at 3 and 7. -/
theorem signed_valuations {c0 c1 : Int} (h : WeightThree c0 c1) {r α β : Nat}
    (hr : r%2=1) (vals : PairAt c0 c1 r α β) :
    (r%4=1 ∧ α=4 ∧ β=4) ∨ (r%8=3 ∧ α=5 ∧ 6≤β) ∨ (r%8=7 ∧ 6≤α ∧ β=5) := by
  obtain ⟨p4,p5,p6⟩ := valuation_of_residue vals.1
  obtain ⟨m4,m5,m6⟩ := valuation_of_residue vals.2
  rcases all_odd_weights c0 c1 h r hr with ⟨w,e⟩ | ⟨w,e⟩ | ⟨w,e⟩ | ⟨w,e⟩
  all_goals obtain ⟨hp, hm⟩ := Prod.mk.inj e
  · exact Or.inl ⟨by omega, p4 (Or.inl hp), m4 (Or.inr hm)⟩
  · exact Or.inr (Or.inl ⟨w, p5 hp, m6 hm⟩)
  · exact Or.inl ⟨by omega, p4 (Or.inr hp), m4 (Or.inl hm)⟩
  · exact Or.inr (Or.inr ⟨w, p6 hp, m5 hm⟩)

/-- The Smith exponents asserted by equation (9) for layers a≥1. -/
def SmithAt (a α β lo hi : Nat) : Prop :=
  lo = min α β + a - 2 ∧ hi = max α β + a - 1

theorem smith_cases {c0 c1 : Int} (h : WeightThree c0 c1) {r α β a lo hi : Nat}
    (hr : r%2=1) (vals : PairAt c0 c1 r α β) (ha : 1 ≤ a) (smith : SmithAt a α β lo hi) :
    (r%4=1 ∧ lo=a+2 ∧ hi=a+3) ∨
    (r%8=3 ∧ lo=a+3 ∧ hi=a-1+β ∧ 6≤β) ∨
    (r%8=7 ∧ lo=a+3 ∧ hi=a-1+α ∧ 6≤α) := by
  obtain ⟨hs, hl⟩ := smith
  rcases signed_valuations h hr vals with ⟨w,p,m⟩ | ⟨w,p,m⟩ | ⟨w,p,m⟩
  · exact Or.inl ⟨w, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨w, by omega, by omega, m⟩)
  · exact Or.inr (Or.inr ⟨w, by omega, by omega, p⟩)

/-- There are exactly two missing exponents between the first possible order
and the progression of higher possible orders. -/
theorem order_gap {c0 c1 : Int} (h : WeightThree c0 c1) {r α β a lo hi order : Nat}
    (hr : r%2=1) (vals : PairAt c0 c1 r α β) (ha : 1 ≤ a) (smith : SmithAt a α β lo hi)
    (card : order = 2^lo * 2^hi) :
    order = 2^(2*a+5) ∨ ∃ j : Nat, order = 2^(2*a+8+j) := by
  rw [← Nat.pow_add] at card
  rcases smith_cases h hr vals ha smith with ⟨_,l,b⟩ | ⟨_,l,b,deep⟩ | ⟨_,l,b,deep⟩
  · exact Or.inl (card.trans (congrArg (2^·) (by omega)))
  · exact Or.inr ⟨β-6, card.trans (congrArg (2^·) (by omega))⟩
  · exact Or.inr ⟨α-6, card.trans (congrArg (2^·) (by omega))⟩

theorem layer_one_gap {c0 c1 : Int} (h : WeightThree c0 c1) {r α β lo hi order : Nat}
    (hr : r%2=1) (vals : PairAt c0 c1 r α β) (smith : SmithAt 1 α β lo hi)
    (card : order = 2^lo * 2^hi) :
    (order = 128 ∨ 1024 ≤ order) ∧ order ≠ 256 ∧ order ≠ 512 := by
  rcases order_gap h hr vals (by decide : 1 ≤ 1) smith card with small | ⟨j,big⟩
  · change order = 128 at small
    omega
  · have bound : (2 : Nat)^10 ≤ 2^(10+j) := Nat.pow_le_pow_right (by decide) (by omega)
    change order = 2^(10+j) at big
    change 1024 ≤ 2^(10+j) at bound
    omega

theorem exact_five_of_residue {x : Int} (h : x%64=32) : exactV x 5 := by
  refine ⟨x/64, ?_⟩
  change x = 32*(2*(x/64)+1)
  omega

/-- When one branch vanishes modulo 64, the other already has a finite
valuation, independently of any nonvanishing hypothesis. -/
theorem companion_of_deep {c0 c1 : Int} (h : WeightThree c0 c1) {r : Nat}
    (hr : r%2=1) :
    (numerator c0 c1 1 (5^r)%64=0 →
      r%8=7 ∧ exactV (numerator c0 c1 (-1) (5^r)) 5) ∧
    (numerator c0 c1 (-1) (5^r)%64=0 →
      r%8=3 ∧ exactV (numerator c0 c1 1 (5^r)) 5) := by
  rcases all_odd_weights c0 c1 h r hr with ⟨w,e⟩ | ⟨w,e⟩ | ⟨w,e⟩ | ⟨w,e⟩
  all_goals obtain ⟨hp, hm⟩ := Prod.mk.inj e
  · constructor <;> intro hz <;> omega
  · exact ⟨fun hz => False.elim (by omega), fun _ => ⟨w, exact_five_of_residue hp⟩⟩
  · constructor <;> intro hz <;> omega
  · exact ⟨fun _ => ⟨w, exact_five_of_residue hm⟩, fun hz => False.elim (by omega)⟩

/-- Every large valuation j+6 occurs in each signed position, paired with
exact valuation five at the same positive odd weight. -/
theorem every_high_pair {c0 c1 : Int} (h : WeightThree c0 c1) (j : Nat) :
    (∃ r, r%8=7 ∧ PairAt c0 c1 r (j+6) 5) ∧
    (∃ r, r%8=3 ∧ PairAt c0 c1 r 5 (j+6)) := by
  obtain ⟨p,m⟩ := both_seeds c0 c1 h
  obtain ⟨i,hi⟩ := WeightClasses.signed_exact_level c0 c1 1 p m (Or.inl rfl) (j+2)
  obtain ⟨k,hk⟩ := WeightClasses.signed_exact_level c0 c1 (-1) p m (Or.inr rfl) (j+2)
  change exactV (numerator c0 c1 1 (5^(1+2*i))) (j+6) at hi
  change exactV (numerator c0 c1 (-1) (5^(1+2*k))) (j+6) at hk
  have right := (companion_of_deep h (r := 1+2*i) (by omega)).1
    (residue_zero_of_deep hi (by omega))
  have left := (companion_of_deep h (r := 1+2*k) (by omega)).2
    (residue_zero_of_deep hk (by omega))
  exact ⟨⟨1+2*i, right.1, hi, right.2⟩, ⟨1+2*k, left.1, left.2, hk⟩⟩

theorem exact_four_of_residue {x : Int} (h : x%64=16 ∨ x%64=48) : exactV x 4 := by
  refine ⟨x/32, ?_⟩
  change x = 16*(2*(x/32)+1)
  omega

theorem weight_one_pair {c0 c1 : Int} (h : WeightThree c0 c1) : PairAt c0 c1 1 4 4 := by
  have hp := signed_sample_mod_weight c0 c1 1 h (Or.inl rfl) 1
  have hm := signed_sample_mod_weight c0 c1 (-1) h (Or.inr rfl) 1
  exact ⟨exact_four_of_residue (Or.inl hp), exact_four_of_residue (Or.inr hm)⟩

/-- Exact orders obtained by applying the paper's exponent formula to the
integral samples. Both the isolated order and every higher listed order occur. -/
theorem order_spectrum {c0 c1 : Int} (h : WeightThree c0 c1) (a order : Nat) (ha : 1 ≤ a) :
    (∃ r α β lo hi : Nat, r%2=1 ∧ PairAt c0 c1 r α β ∧ SmithAt a α β lo hi ∧
      order = 2^lo*2^hi) ↔ order = 2^(2*a+5) ∨ ∃ j : Nat, order = 2^(2*a+8+j) := by
  constructor
  · rintro ⟨r,α,β,lo,hi,odd,vals,smith,card⟩
    exact order_gap h odd vals ha smith card
  · rintro (small | ⟨j,big⟩)
    · refine ⟨1,4,4,a+2,a+3,by decide,weight_one_pair h,⟨by omega, by omega⟩,?_⟩
      rw [← Nat.pow_add, small]
      exact congrArg (2^·) (by omega)
    · obtain ⟨r,hr,vals⟩ := (every_high_pair h j).1
      refine ⟨r,j+6,5,a+3,a+j+5,by omega,vals,⟨by omega, by omega⟩,?_⟩
      rw [← Nat.pow_add, big]
      exact congrArg (2^·) (by omega)

end Reimann.PairedOrders

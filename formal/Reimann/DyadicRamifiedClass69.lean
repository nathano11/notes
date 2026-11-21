import Reimann.DyadicClass69

/-! The ramified ideal at 2 in the imaginary quadratic order Z[√−69]. -/
namespace Reimann.DyadicRamifiedClass69

abbrev IntegerBasis := Int × Int

def times (x y : IntegerBasis) : IntegerBasis :=
  (x.1*y.1-69*x.2*y.2, x.1*y.2+x.2*y.1)

def plus (x y : IntegerBasis) : IntegerBasis := (x.1+y.1,x.2+y.2)

def norm (x : IntegerBasis) : Int := x.1*x.1+69*x.2*x.2

/-- Kernel of reduction √−69 ↦ 1 in F₂. -/
def ramified (x : IntegerBasis) : Prop := ∃ t : Int, x.1=2*t+x.2

def principal (u x : IntegerBasis) : Prop := ∃ y, x=times u y

/-- Finite sums of products of elements of the ideal. -/
inductive idealSquare (I : IntegerBasis → Prop) : IntegerBasis → Prop where
  | zero : idealSquare I (0,0)
  | product {x y} : I x → I y → idealSquare I (times x y)
  | sum {x y} : idealSquare I x → idealSquare I y → idealSquare I (plus x y)

theorem ramified_absorbs (x y : IntegerBasis) (hy : ramified y) : ramified (times x y) := by
  obtain ⟨u,hu⟩ := hy
  refine ⟨x.1*u-x.2*u-35*x.2*y.2,?_⟩
  dsimp [times]
  grind

theorem norm_times (x y : IntegerBasis) : norm (times x y)=norm x*norm y := by
  simp only [times,norm]
  grind

theorem product_is_even (x y : IntegerBasis) (hx : ramified x) (hy : ramified y) :
    principal (2,0) (times x y) := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  exact ⟨(2*s*t+s*y.2+x.2*t-34*x.2*y.2,s*y.2+x.2*t+x.2*y.2),
    Prod.ext (by simp [times]; grind) (by simp [times]; grind)⟩

theorem square_is_even {x : IntegerBasis} (hx : idealSquare ramified x) : principal (2,0) x := by
  induction hx with
  | zero => exact ⟨(0,0),rfl⟩
  | product h k => exact product_is_even _ _ h k
  | sum _ _ ha hb =>
    obtain ⟨u,rfl⟩ := ha
    obtain ⟨v,rfl⟩ := hb
    exact ⟨plus u v,Prod.ext (by simp [plus,times]; grind) (by simp [plus,times]; grind)⟩

theorem even_in_square (x : IntegerBasis) : idealSquare ramified (times (2,0) x) := by
  have a : ramified (1,1) := ⟨0,rfl⟩
  have b : ramified (1,-1) := ⟨1,rfl⟩
  have c : ramified (-34,0) := ⟨-17,rfl⟩
  have d : ramified (2,0) := ⟨1,rfl⟩
  have h := idealSquare.sum (idealSquare.product (ramified_absorbs x _ a) b)
    (idealSquare.product (ramified_absorbs x _ c) d)
  have he : plus (times (times x (1,1)) (1,-1)) (times (times x (-34,0)) (2,0)) =
      times (2,0) x := Prod.ext (by simp only [plus,times]; grind) (by simp only [plus,times]; grind)
  exact he ▸ h

theorem ramified_square (x : IntegerBasis) : idealSquare ramified x ↔ principal (2,0) x := by
  exact ⟨square_is_even,fun ⟨y,hy⟩ => hy ▸ even_in_square y⟩

theorem ramified_iff_parity (x : IntegerBasis) : ramified x ↔ (x.1+x.2)%2=0 := by
  constructor
  · rintro ⟨t,ht⟩
    omega
  · intro h
    exact ⟨(x.1-x.2)/2, by omega⟩

theorem ramified_prime (x y : IntegerBasis) (h : ramified (times x y)) : ramified x ∨ ramified y := by
  have e : (times x y).1+(times x y).2 =
      (x.1+x.2)*(y.1+y.2)-70*(x.2*y.2) := by simp only [times]; grind
  have h0 := (ramified_iff_parity _).mp h
  rw [e] at h0
  have hprod : ((x.1+x.2)*(y.1+y.2))%2=0 := by omega
  rw [Int.mul_emod] at hprod
  rw [ramified_iff_parity,ramified_iff_parity]
  have hx := Int.emod_nonneg (x.1+x.2) (by decide : (2:Int)≠0)
  have hy := Int.emod_nonneg (y.1+y.2) (by decide : (2:Int)≠0)
  have hxl := Int.emod_lt_of_pos (x.1+x.2) (by decide : (0:Int)<2)
  have hyl := Int.emod_lt_of_pos (y.1+y.2) (by decide : (0:Int)<2)
  by_cases ax : (x.1+x.2)%2=0
  · exact Or.inl ax
  · right
    by_cases ay : (y.1+y.2)%2=0
    · exact ay
    · have a1 : (x.1+x.2)%2=1 := by omega
      have b1 : (y.1+y.2)%2=1 := by omega
      rw [a1,b1] at hprod
      contradiction

theorem norm_not_two (x : IntegerBasis) : norm x≠2 := by
  intro h
  have ls : (x.1*x.1)%3=2 := by unfold norm at h; rw [Int.mul_assoc] at h; omega
  rw [Int.mul_emod] at ls
  have hcases : x.1%3=0 ∨ x.1%3=1 ∨ x.1%3=2 := by omega
  rcases hcases with h0|h1|h2 <;> simp [*] at ls

theorem norm_divides (u x : IntegerBasis) (h : principal u x) : norm u ∣ norm x := by
  obtain ⟨y,rfl⟩ := h
  exact ⟨norm y,norm_times u y⟩

theorem ramified_nonprincipal : ¬∃ u : IntegerBasis, ∀ x, ramified x ↔ principal u x := by
  rintro ⟨u,hu⟩
  have d4 : norm u ∣ 4 := norm_divides u (2,0) ((hu _).mp ⟨1,rfl⟩)
  have d70 : norm u ∣ 70 := norm_divides u (1,1) ((hu _).mp ⟨0,rfl⟩)
  obtain ⟨k,hk⟩ := d4
  obtain ⟨l,hl⟩ := d70
  have d2 : norm u ∣ 2 := ⟨l-17*k, by grind⟩
  have hn : 0 ≤ norm u := by
    have a := Int.sq_nonneg u.1
    have b := Int.sq_nonneg u.2
    unfold norm
    grind
  have nz : norm u ≠ 0 := by intro h; rw [h] at hk; omega
  have le := Int.le_of_dvd (by decide : (0:Int)<2) d2
  have odd := norm_not_two u
  have one : norm u = 1 := by omega
  have conj : times u (u.1,-u.2)=(norm u,0) := Prod.ext (by simp [times,norm]; grind) (by simp [times]; grind)
  have bad := (hu (1,0)).mpr ⟨(u.1,-u.2),by rw [conj,one]⟩
  have := (ramified_iff_parity (1,0)).mp bad
  contradiction

/-- P is prime and nonprincipal, and its literal ideal square is (2).
These are precisely the order-two ideal-class relations in Z[√−69]. -/
theorem dyadic_class_order_two :
    (∀ x y, ramified (times x y) → ramified x ∨ ramified y) ∧
    (∀ x, idealSquare ramified x ↔ principal (2,0) x) ∧
    ¬∃ u : IntegerBasis, ∀ x, ramified x ↔ principal u x :=
  ⟨ramified_prime,ramified_square,ramified_nonprincipal⟩

end Reimann.DyadicRamifiedClass69

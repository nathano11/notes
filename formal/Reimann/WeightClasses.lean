import Reimann.SampleSpacing

/-!
The binary lifting in §8 of `Dyadic_Window_Orders.md`.
The index `i` denotes the positive odd weight `1+2*i`.
-/

namespace Reimann.WeightClasses

open Reimann.Dyadic

/-- Divisibility at level zero starts at 16. -/
def hit (f : Nat → Int) (k i : Nat) : Prop := (2 : Int)^(k+4) ∣ f i

/-- The difference of two siblings, divided by the current modulus, is odd. -/
def SiblingSteps (f : Nat → Int) : Prop :=
  ∀ k i : Nat, ∃ u : Int, f (i+2^k) = f i + (2 : Int)^(k+4)*(2*u+1)

theorem hit_shift (f : Nat → Int) (step : SiblingSteps f) (k i : Nat) :
    hit f k (i+2^k) ↔ hit f k i := by
  obtain ⟨u, hu⟩ := step k i
  unfold hit
  rw [hu, Int.dvd_add_left (Int.dvd_mul_right _ _)]

theorem hit_mod (f : Nat → Int) (step : SiblingSteps f) (k i : Nat) :
    hit f k i ↔ hit f k (i % 2^k) := by
  have shifts (r n : Nat) : hit f k (r+2^k*n) ↔ hit f k r := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, ← Nat.add_assoc, hit_shift f step, ih]
  have h := shifts (i%2^k) (i/2^k)
  rwa [Nat.mod_add_div] at h

theorem hit_parent {f : Nat → Int} {k i : Nat} (h : hit f (k+1) i) :
    hit f k i := by
  obtain ⟨u, hu⟩ := h
  refine ⟨2*u, ?_⟩
  rw [show k+1+4 = (k+4)+1 by omega, Int.pow_succ] at hu
  simpa [Int.mul_assoc] using hu

/-- After removing the current power of two, the next condition is parity. -/
theorem hit_child_iff_even (f : Nat → Int) (k i : Nat) (u : Int)
    (hu : f i = (2 : Int)^(k+4)*u) : hit f (k+1) i ↔ 2 ∣ u := by
  unfold hit
  rw [hu, show k+1+4 = (k+4)+1 by omega, Int.pow_succ]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, Int.eq_of_mul_eq_mul_left (Int.pow_ne_zero (by decide : (2 : Int) ≠ 0))
      (by simpa [Int.mul_assoc] using hz)⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, Int.mul_assoc]⟩

theorem sibling_alternative (f : Nat → Int) (step : SiblingSteps f) (k i : Nat)
    (parent : hit f k i) : hit f (k+1) (i+2^k) ↔ ¬hit f (k+1) i := by
  obtain ⟨u, hu⟩ := parent
  obtain ⟨v, hv⟩ := step k i
  have hw : f (i+2^k) = (2 : Int)^(k+4)*(u+(2*v+1)) := by
    rw [hv, hu, ← Int.mul_add]
  rw [hit_child_iff_even f k _ _ hw, hit_child_iff_even f k _ _ hu]
  omega

/-- There are only two residues upstairs with a given lower residue. -/
theorem binary_fiber {m j r : Nat} (hj : j < 2*m) (hr : j%m=r) :
    j=r ∨ j=r+m := by
  by_cases h : j < m
  · left
    rwa [Nat.mod_eq_of_lt h] at hr
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hr
    omega

/-- The representative characterizes every nonnegative odd-weight index. -/
def RootAt (f : Nat → Int) (k r : Nat) : Prop :=
  r < 2^k ∧ ∀ i, hit f k i ↔ i%2^k = r

theorem lift_root (f : Nat → Int) (step : SiblingSteps f) (k r : Nat)
    (root : RootAt f k r) :
    ∃ s, RootAt f (k+1) s ∧ (s=r ∨ s=r+2^k) := by
  have parent := (root.2 r).mpr (Nat.mod_eq_of_lt root.1)
  have alt := sibling_alternative f step k r parent
  have two : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ, Nat.mul_comm]
  have chosen : ∃ s, (s=r ∨ s=r+2^k) ∧ hit f (k+1) s ∧
      ∀ j, j < 2^(k+1) → hit f (k+1) j → j=s := by
    have which (j : Nat) (hj : j < 2^(k+1)) (good : hit f (k+1) j) :
        j=r ∨ j=r+2^k :=
      binary_fiber (two ▸ hj) ((root.2 j).mp (hit_parent good))
    by_cases hr : hit f (k+1) r
    · refine ⟨r, Or.inl rfl, hr, ?_⟩
      intro j hj good
      rcases which j hj good with h | h
      · exact h
      · exact False.elim ((alt.mp (h ▸ good)) hr)
    · refine ⟨r+2^k, Or.inr rfl, alt.mpr hr, ?_⟩
      intro j hj good
      rcases which j hj good with h | h
      · exact False.elim (hr (h ▸ good))
      · exact h
  obtain ⟨s, side, good, onlyOne⟩ := chosen
  refine ⟨s, ⟨?_, ?_⟩, side⟩
  · have h := root.1
    rcases side with h' | h' <;> rw [h', two] <;> omega
  · intro i
    rw [hit_mod f step (k+1) i]
    constructor
    · exact onlyOne _ (Nat.mod_lt _ (Nat.pow_pos (by decide)))
    · intro h
      simpa only [h] using good

theorem root_at_every_depth (f : Nat → Int) (step : SiblingSteps f)
    (seed : hit f 0 0) (k : Nat) : ∃ r, RootAt f k r := by
  induction k with
  | zero =>
    refine ⟨0, by decide, ?_⟩
    intro i
    rw [hit_mod f step 0 i]
    simpa [Nat.mod_one] using seed
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs, _⟩ := lift_root f step k r hr
    exact ⟨s, hs⟩

theorem root_unique {f : Nat → Int} {k r s : Nat}
    (hr : RootAt f k r) (hs : RootAt f k s) : r=s := by
  have h := (hs.2 r).mp ((hr.2 r).mpr (Nat.mod_eq_of_lt hr.1))
  rwa [Nat.mod_eq_of_lt hr.1] at h

/-- Independently chosen roots at successive precisions are compatible. -/
theorem root_compatible {f : Nat → Int} {k r s : Nat}
    (hr : RootAt f k r) (hs : RootAt f (k+1) s) : s%2^k=r :=
  (hr.2 s).mp (hit_parent ((hs.2 s).mpr (Nat.mod_eq_of_lt hs.1)))

/-- The actual reciprocal-polynomial numerator at a positive odd weight. -/
def sample (c0 c1 ε : Int) (i : Nat) : Int :=
  SampleSpacing.numerator c0 c1 ε ((5 : Int)^(1+2*i))

theorem seed_even_constant (c0 c1 ε : Int) (hsign : ε=1 ∨ ε= -1)
    (seed : hit (sample c0 c1 ε) 0 0) : 2 ∣ c0 := by
  obtain ⟨w, hw⟩ := seed
  rcases hsign with h | h <;> subst ε <;>
    simp [sample, SampleSpacing.numerator] at hw <;> omega

theorem numerator_difference (c0 c1 ε a b : Int) :
    SampleSpacing.numerator c0 c1 ε b - SampleSpacing.numerator c0 c1 ε a =
      (b-a)*((1-c1+c0)*(a+b)+(c1-2)*ε) := by
  unfold SampleSpacing.numerator
  grind

theorem numerator_slope (c0 c1 ε a b : Int) (hc0 : 2 ∣ c0)
    (hc1 : ∃ w : Int, c1=2+4*w) (ha : ∃ u : Int, a=1+4*u)
    (hb : ∃ v : Int, b=1+4*v) :
    ∃ z : Int, (1-c1+c0)*(a+b)+(c1-2)*ε = 2*(2*z+1) := by
  obtain ⟨t, ht⟩ := hc0
  obtain ⟨w, hw⟩ := hc1
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨t-2*w-1+(1-c1+c0)*(u+v)+w*ε, ?_⟩
  rw [hw, ht, hu, hv]
  grind

theorem twoPower_eq_pow (k : Nat) : twoPower k = (2 : Int)^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [twoPower, ih, Int.pow_succ, Int.mul_comm]

theorem sample_steps (c0 c1 ε : Int) (hc0 : 2 ∣ c0)
    (hc1 : ∃ w : Int, c1=2+4*w) : SiblingSteps (sample c0 c1 ε) := by
  intro k i
  let n := 1+2*i
  let m := 1+2*(i+2^k)
  have hm : n + 2^(k+1)*(2*0+1) = m := by
    dsimp [n, m]
    rw [Nat.pow_succ]
    omega
  have hgap := SampleSpacing.power_gap n (k+1) 0
  rw [hm] at hgap
  obtain ⟨w, hw⟩ := numerator_slope c0 c1 ε _ _ hc0 hc1
    (SampleSpacing.five_power_mod_four n) (SampleSpacing.five_power_mod_four m)
  have hx := SampleSpacing.exactV_mul_twice_odd _ _ w hgap
  rw [←hw, ←numerator_difference] at hx
  obtain ⟨z, hz⟩ := hx
  rw [twoPower_eq_pow, show k+1+2+1=k+4 by omega] at hz
  refine ⟨z, ?_⟩
  change SampleSpacing.numerator c0 c1 ε (5^m) =
    SampleSpacing.numerator c0 c1 ε (5^n) + 2^(k+4)*(2*z+1)
  omega

/-- Each finite precision singles out a unique index class. Its representative
gives a positive odd weight, and every other odd weight is covered by the iff. -/
theorem unique_weight_class (c0 c1 ε : Int) (hc1 : ∃ w : Int, c1=2+4*w)
    (hsign : ε=1 ∨ ε= -1) (seed : hit (sample c0 c1 ε) 0 0) (k : Nat) :
    ∃ r, RootAt (sample c0 c1 ε) k r ∧ ∀ s, RootAt (sample c0 c1 ε) k s → s=r := by
  have steps := sample_steps c0 c1 ε (seed_even_constant c0 c1 ε hsign seed) hc1
  obtain ⟨r, hr⟩ := root_at_every_depth _ steps seed k
  exact ⟨r, hr, fun _ hs => root_unique hs hr⟩

/-- Exact low-weight data needed to start both sign branches. -/
theorem two_seeds_iff (c0 c1 : Int) :
    (hit (sample c0 c1 1) 0 0 ∧ hit (sample c0 c1 (-1)) 0 0) ↔
    (c0 % 16 = 8 ∧ c1 % 8 = 2) := by
  change (16 ∣ (1-5)^2+c1*5*(1-5)+c0*5^2 ∧
    16 ∣ (-1-5)^2+c1*5*(-1-5)+c0*5^2) ↔ _
  omega

theorem classes_from_two_seeds (c0 c1 ε : Int)
    (plusSeed : hit (sample c0 c1 1) 0 0) (minusSeed : hit (sample c0 c1 (-1)) 0 0)
    (hsign : ε=1 ∨ ε= -1) (k : Nat) :
    ∃ r, RootAt (sample c0 c1 ε) k r ∧ ∀ s, RootAt (sample c0 c1 ε) k s → s=r := by
  have h := ((two_seeds_iff c0 c1).mp ⟨plusSeed, minusSeed⟩).2
  have hc : ∃ w : Int, c1=2+4*w := ⟨2*(c1/8), by omega⟩
  apply unique_weight_class c0 c1 ε hc hsign
  rcases hsign with h | h <;> subst ε
  · exact plusSeed
  · exact minusSeed

/-- Two branches meet precisely when their samples agree modulo the current
modulus at the first branch's canonical representative. -/
theorem roots_equal_iff {f g : Nat → Int} {k r s : Nat}
    (hf : RootAt f k r) (hg : RootAt g k s) :
    r=s ↔ (2 : Int)^(k+4) ∣ f r-g r := by
  have base := (hf.2 r).mpr (Nat.mod_eq_of_lt hf.1)
  have other := hg.2 r
  rw [Nat.mod_eq_of_lt hf.1] at other
  change (2 : Int)^(k+4) ∣ f r at base
  change ((2 : Int)^(k+4) ∣ g r) ↔ r=s at other
  constructor
  · intro h
    exact Int.dvd_sub base (other.mpr h)
  · intro h
    apply other.mp
    simpa only [show f r - (f r-g r) = g r by omega] using Int.dvd_sub base h

theorem cancel_five_power (k n : Nat) (z : Int) :
    (2 : Int)^k ∣ 5^n*z ↔ (2 : Int)^k ∣ z := by
  rw [←Int.dvd_gcd_mul_iff_dvd_mul]
  rw [Int.pow_gcd_pow_of_gcd_eq_one (by decide : Int.gcd 2 5=1)]
  simp

/-- Translating the index residue back to the paper's odd weight modulus. -/
theorem odd_weight_mod (i k : Nat) :
    (1+2*i)%2^(k+1) = 1+2*(i%2^k) := by
  let m := 2^k
  have h := Nat.mod_add_div i m
  have small : i%m<m := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have bound : 1+2*(i%m)<2*m := by omega
  have hweight : 1+2*i = (1+2*(i%m))+(2*m)*(i/m) := by
    calc
      1+2*i = 1+2*(i%m+m*(i/m)) := by rw [h]
      _ = _ := by grind
  change (1+2*i)%2^(k+1)=1+2*(i%m)
  rw [show 2^(k+1)=2*m by rw [Nat.pow_succ]; exact Nat.mul_comm _ _,
    hweight, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]

theorem root_odd_weight {f : Nat → Int} {k r : Nat} (root : RootAt f k r) (i : Nat) :
    hit f k i ↔ (1+2*i)%2^(k+1)=1+2*r := by
  rw [root.2, odd_weight_mod]
  omega

/-- A nonzero numerator has the exact current valuation when it passes this
precision and fails the next one. The equivalence handles zero as well. -/
theorem exact_level_iff (f : Nat → Int) (k i : Nat) :
    exactV (f i) (k+4) ↔ hit f k i ∧ ¬hit f (k+1) i := by
  constructor
  · rintro ⟨u, hu⟩
    rw [twoPower_eq_pow] at hu
    refine ⟨⟨2*u+1, hu⟩, ?_⟩
    rw [hit_child_iff_even f k i _ hu]
    omega
  · rintro ⟨⟨u, hu⟩, hchild⟩
    rw [hit_child_iff_even f k i _ hu] at hchild
    refine ⟨u/2, ?_⟩
    rw [twoPower_eq_pow, hu]
    exact congrArg ((2 : Int)^(k+4) * ·) (by omega)

/-- Of the two children above a root, precisely its nonlifting sibling gives
the exact valuation. The other child remains the next root. -/
theorem exact_sibling {f : Nat → Int} {k r s : Nat}
    (parent : RootAt f k r) (child : RootAt f (k+1) s) :
    ∃ b, ((s=r ∧ b=r+2^k) ∨ (s=r+2^k ∧ b=r)) ∧ b<2^(k+1) ∧
      ∀ i, exactV (f i) (k+4) ↔ i%2^(k+1)=b := by
  have htwo : 2^(k+1) = 2*2^k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd : 2^k ∣ 2^(k+1) := ⟨2, Nat.pow_succ ..⟩
  have split (i : Nat) : i%2^k=r ↔ i%2^(k+1)=r ∨ i%2^(k+1)=r+2^k := by
    have modmod := Nat.mod_mod_of_dvd i hd
    constructor
    · intro h
      apply binary_fiber (m := 2^k)
      · rw [←htwo]
        exact Nat.mod_lt _ (Nat.pow_pos (by decide))
      · exact modmod.trans h
    · intro h
      rw [←modmod]
      rcases h with h | h <;> rw [h] <;> simp [Nat.mod_eq_of_lt parent.1]
  have side := binary_fiber (htwo ▸ child.1) (root_compatible parent child)
  have hr := parent.1
  have hm : 0 < 2^k := Nat.pow_pos (by decide)
  rcases side with h | h
  · refine ⟨r+2^k, Or.inl ⟨h, rfl⟩, by rw [htwo]; omega, ?_⟩
    intro i
    rw [exact_level_iff, parent.2, child.2, split, h]
    omega
  · refine ⟨r, Or.inr ⟨h, rfl⟩, by rw [htwo]; omega, ?_⟩
    intro i
    rw [exact_level_iff, parent.2, child.2, split, h]
    omega

/-- On a seeded branch the exact valuation identifies a single positive odd
weight class modulo twice the modulus for weak divisibility. -/
theorem exact_weight_class (f : Nat → Int) (step : SiblingSteps f)
    (seed : hit f 0 0) (k : Nat) :
    ∃ b, b<2^(k+1) ∧ ∀ i, exactV (f i) (k+4) ↔ (1+2*i)%2^(k+2)=1+2*b := by
  obtain ⟨r, parent⟩ := root_at_every_depth f step seed k
  obtain ⟨s, child, _⟩ := lift_root f step k r parent
  obtain ⟨b, _, hb, shell⟩ := exact_sibling parent child
  refine ⟨b, hb, ?_⟩
  intro i
  rw [shell, show k+2=(k+1)+1 by omega, odd_weight_mod]
  omega

theorem every_exact_level (f : Nat → Int) (step : SiblingSteps f)
    (seed : hit f 0 0) (k : Nat) : ∃ i, exactV (f i) (k+4) := by
  obtain ⟨b, hb, shell⟩ := exact_weight_class f step seed k
  refine ⟨b, (shell b).mpr ?_⟩
  rw [show k+2=(k+1)+1 by omega, odd_weight_mod, Nat.mod_eq_of_lt hb]

/-- At every finite valuation at least four there is an actual positive odd
weight `1+2*i` realizing it on either sign's reciprocal numerator. -/
theorem signed_exact_level (c0 c1 ε : Int)
    (plusSeed : hit (sample c0 c1 1) 0 0) (minusSeed : hit (sample c0 c1 (-1)) 0 0)
    (hsign : ε=1 ∨ ε= -1) (k : Nat) : ∃ i, exactV (sample c0 c1 ε i) (k+4) := by
  obtain ⟨r, hr, _⟩ := classes_from_two_seeds c0 c1 ε plusSeed minusSeed hsign k
  obtain ⟨s, hs, _⟩ := classes_from_two_seeds c0 c1 ε plusSeed minusSeed hsign (k+1)
  obtain ⟨b, _, hb, shell⟩ := exact_sibling hr hs
  exact ⟨b, (shell b).mpr (Nat.mod_eq_of_lt hb)⟩

end Reimann.WeightClasses

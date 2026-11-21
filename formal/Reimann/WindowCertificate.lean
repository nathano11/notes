import Std

/-!
Finite arithmetic in §1 of *The integer behind the arithmetic window*.
The supplied table lists the lengths at each base and each weight. The
number-field proof must identify these entries and show the support is complete.
-/
namespace Reimann.WindowCertificate

/-- Length at base `p`, summed over all supplied weights (including repetitions). -/
def totalLength (weights : List Nat) (len : Nat → Nat → Nat) (p : Nat) : Nat :=
  (weights.map (len p)).sum

/-- Taking the individual weight orders or adding their lengths gives the same factor. -/
theorem primePower_eq_weightProduct (weights : List Nat) (len : Nat → Nat → Nat) (p : Nat) :
    p ^ totalLength weights len p = (weights.map (fun r => p ^ len p r)).prod := by
  induction weights with
  | nil => simp [totalLength]
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons]
    change p ^ (len p r + totalLength rs len p) = _
    rw [Nat.pow_add, ih]

/-- Product of the required base powers for the selected support. -/
def windowOrder (bases : List Nat) (exponent : Nat → Nat) : Nat :=
  (bases.map (fun p => p ^ exponent p)).prod

theorem windowOrder_cons (p : Nat) (ps : List Nat) (e : Nat → Nat) :
    windowOrder (p :: ps) e = p ^ e p * windowOrder ps e := by
  simp [windowOrder]

theorem primePower_dvd_windowOrder {p : Nat} (ps : List Nat) (e : Nat → Nat)
    (hp : p ∈ ps) : p ^ e p ∣ windowOrder ps e := by
  induction ps with
  | nil => simp at hp
  | cons q qs ih =>
    rw [windowOrder_cons]
    rcases List.mem_cons.mp hp with h | h
    · subst q
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_mul_left_of_dvd (ih h) _

theorem coprime_windowOrder (b : Nat) (ps : List Nat) (e : Nat → Nat)
    (hc : ∀ p ∈ ps, Nat.Coprime b p) : Nat.Coprime b (windowOrder ps e) := by
  induction ps with
  | nil => exact Nat.coprime_one_right b
  | cons q qs ih =>
    rw [windowOrder_cons]
    exact ((hc q (by simp)).pow_right (e q)).mul_right
      (ih fun p hp => hc p (List.mem_cons_of_mem _ hp))

/-- Each base-power requirement is simultaneous in the same integer `H`. -/
theorem windowOrder_dvd_iff (ps : List Nat) (e : Nat → Nat) (H : Nat)
    (hc : ps.Pairwise Nat.Coprime) :
    windowOrder ps e ∣ H ↔ ∀ p ∈ ps, p ^ e p ∣ H := by
  constructor
  · intro h p hp
    exact Nat.dvd_trans (primePower_dvd_windowOrder ps e hp) h
  · intro h
    induction ps with
    | nil => exact Nat.one_dvd H
    | cons p ps ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hc
      rw [windowOrder_cons]
      apply ((coprime_windowOrder p ps e hhead).pow_left (e p)).mul_dvd_of_dvd_of_dvd
      · exact h p (by simp)
      · exact ih htail fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem windowOrder_pos (ps : List Nat) (e : Nat → Nat)
    (hp : ∀ p ∈ ps, 0 < p) : 0 < windowOrder ps e := by
  induction ps with
  | nil => simp [windowOrder]
  | cons p ps ih =>
    rw [windowOrder_cons]
    exact Nat.mul_pos (Nat.pow_pos (hp p (by simp)))
      (ih fun q hq => hp q (List.mem_cons_of_mem _ hq))

/-- Positive witnesses below an integer bound exist exactly up to the minimal product. -/
theorem bounded_certificate_iff (ps : List Nat) (e : Nat → Nat) (B : Nat)
    (hc : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, 0 < p) :
    (∃ H, 0 < H ∧ H ≤ B ∧ ∀ p ∈ ps, p ^ e p ∣ H) ↔ windowOrder ps e ≤ B := by
  constructor
  · rintro ⟨H, hH, hB, covers⟩
    exact Nat.le_trans (Nat.le_of_dvd hH ((windowOrder_dvd_iff ps e H hc).mpr covers)) hB
  · intro h
    exact ⟨windowOrder ps e, windowOrder_pos ps e hp, h, fun _ hmem =>
      primePower_dvd_windowOrder ps e hmem⟩

theorem windowOrder_add (ps : List Nat) (e f : Nat → Nat) :
    windowOrder ps (fun p => e p + f p) = windowOrder ps e * windowOrder ps f := by
  induction ps with
  | nil => simp [windowOrder]
  | cons p ps ih =>
    simp only [windowOrder_cons, Nat.pow_add, ih]
    ac_rfl

/-- Regroup the whole finite order by weight. The right side multiplies the orders
at the same weight before moving to the next weight. -/
theorem windowOrder_eq_product_by_weight (ps weights : List Nat) (len : Nat → Nat → Nat) :
    windowOrder ps (totalLength weights len) =
      (weights.map (fun r => windowOrder ps (fun p => len p r))).prod := by
  induction weights with
  | nil =>
    change windowOrder ps (fun _ => 0) = 1
    induction ps with
    | nil => rfl
    | cons p ps ih => simpa [windowOrder_cons] using ih
  | cons r rs ih =>
    change windowOrder ps (fun p => len p r + totalLength rs len p) = _
    rw [windowOrder_add, ih]
    simp

/-- Splitting the lengths into an accounted part and the remaining lengths
splits the minimal integer by an exact factor. -/
theorem windowOrder_residual (ps : List Nat) (full known : Nat → Nat)
    (hle : ∀ p ∈ ps, known p ≤ full p) :
    windowOrder ps full =
      windowOrder ps known * windowOrder ps (fun p => full p - known p) := by
  induction ps with
  | nil => simp [windowOrder]
  | cons p ps ih =>
    have hd : full p = known p + (full p - known p) := by
      have := hle p (by simp)
      omega
    rw [windowOrder_cons, windowOrder_cons, windowOrder_cons,
      ih (fun q hq => hle q (List.mem_cons_of_mem _ hq))]
    conv => lhs; arg 1; rw [hd, Nat.pow_add]
    ac_rfl

/-- The precise integer budget left for missing factors after paying for all
proved lengths. The known part may spend the entire budget. -/
theorem residual_budget_iff (ps : List Nat) (full known : Nat → Nat) (B : Nat)
    (hc : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, 0 < p)
    (hle : ∀ p ∈ ps, known p ≤ full p) :
    (∃ H, 0 < H ∧ H ≤ B ∧ ∀ p ∈ ps, p ^ full p ∣ H) ↔
      windowOrder ps (fun p => full p - known p) ≤ B / windowOrder ps known := by
  rw [bounded_certificate_iff ps full B hc hp, windowOrder_residual ps full known hle,
    Nat.mul_comm (windowOrder ps known)]
  exact (Nat.le_div_iff_mul_le (windowOrder_pos ps known hp)).symm

/-- In the manuscript the weights are precisely 1 through t−1. Aggregation
at a prime takes place before testing divisibility of the common witness. -/
theorem arithmetic_window_budget_iff (ps : List Nat) (t B : Nat) (len : Nat → Nat → Nat)
    (hc : ps.Pairwise Nat.Coprime) (hp : ∀ p ∈ ps, 0 < p) :
    (∃ H, 0 < H ∧ H ≤ B ∧ ∀ p ∈ ps, p ^ totalLength (List.range' 1 (t-1)) len p ∣ H) ↔
      ((List.range' 1 (t-1)).map (fun r => windowOrder ps (fun p => len p r))).prod ≤ B := by
  rw [bounded_certificate_iff ps _ B hc hp, windowOrder_eq_product_by_weight]

/-- The note's example with three units of length at 2 and two at 5. -/
theorem example_order_200 :
    windowOrder [2,5] (fun p => if p=2 then 3 else 2) = 200 := by decide

end Reimann.WindowCertificate

import Std

/-! Coefficients of the group ring (ℤ/64)[C₆₄], in ascending powers
of X. The operator X-1 has nilpotence index exactly 224. -/
namespace Reimann.SignedCyclicAction

abbrev Row := Fin 64 → BitVec 6

/-- Multiplication by the generator X, wrapping the final coefficient. -/
def shift (r : Row) (i : Fin 64) : BitVec 6 := r (i - 1)

def difference (r : Row) (i : Fin 64) : BitVec 6 := shift r i - r i

def iterate : Nat → Row → Row
  | 0, r => r
  | n+1, r => difference (iterate n r)

/-- The row of the multiplicative identity. -/
def delta (i : Fin 64) : BitVec 6 := if i=0 then 1 else 0

/-- Materialize an entire step before the next one, to check large exponents. -/
def tableStep (v : Vector (BitVec 6) 64) : Vector (BitVec 6) 64 :=
  Vector.ofFn (fun i => v.get (i-1) - v.get i)

def table : Nat → Vector (BitVec 6) 64
  | 0 => Vector.ofFn delta
  | n+1 => tableStep (table n)

theorem table_correct (n : Nat) : (table n).get = iterate n delta := by
  induction n with
  | zero => funext i; exact Vector.getElem_ofFn i.isLt
  | succ n ih =>
    funext i
    change (Vector.ofFn (fun j : Fin 64 => (table n).get (j-1) - (table n).get j))[i.val] = _
    rw [Vector.getElem_ofFn, ih]
    rfl

theorem iterate_add (n : Nat) (u v : Row) :
    iterate n (fun i => u i + v i) = fun i => iterate n u i + iterate n v i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [iterate, ih, difference, shift]
    grind

theorem iterate_scale (n : Nat) (a : BitVec 6) (u : Row) :
    iterate n (fun i => a*u i) = fun i => a*iterate n u i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    simp only [iterate, ih, difference, shift, BitVec.mul_sub]

theorem iterate_zero (n : Nat) : iterate n (fun _ => 0) = fun _ => 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change difference (iterate n (fun _ => 0)) = _
    rw [ih]
    funext i
    exact BitVec.sub_self _

/-- Translation by any generator power commutes with a single shift. -/
theorem subtract_indices (i j : Fin 64) : (i-1)-j = (i-j)-1 := by
  revert i j
  decide

theorem iterate_translate (n : Nat) (u : Row) (j : Fin 64) :
    iterate n (fun i => u (i-j)) = fun i => iterate n u (i-j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change difference (iterate n (fun i => u (i-j))) = _
    rw [ih]
    funext i
    change iterate n u ((i-1)-j) - iterate n u (i-j) = iterate n u ((i-j)-1) - iterate n u (i-j)
    rw [subtract_indices]

theorem translate_delta (i j : Fin 64) : delta (i-j) = (if i=j then 1 else 0) := by
  revert i j
  decide

def partialRow (r : Row) (n : Nat) (i : Fin 64) : BitVec 6 := if i.val < n then r i else 0

theorem partialRow_succ (r : Row) (j : Fin 64) :
    partialRow r (j.val+1) = fun i => partialRow r j.val i + r j*delta (i-j) := by
  funext i
  rw [translate_delta]
  unfold partialRow
  by_cases h : i = j
  · subst i; simp
  · have hne : i.val ≠ j.val := fun eq => h (Fin.ext eq)
    have same : i.val < j.val+1 ↔ i.val < j.val := by omega
    simp [h, same]

/-- A power vanishing on the basis element 1 vanishes on every cyclic row. -/
theorem zero_from_delta (n : Nat) (h : iterate n delta = fun _ => 0) (r : Row) :
    iterate n r = fun _ => 0 := by
  have step (k : Nat) (hk : k ≤ 64) : iterate n (partialRow r k) = fun _ => 0 := by
    induction k with
    | zero =>
      have empty : partialRow r 0 = fun _ => 0 := by funext i; simp [partialRow]
      rw [empty, iterate_zero]
    | succ k ih =>
      let j : Fin 64 := ⟨k, by omega⟩
      change iterate n (partialRow r (j.val+1)) = _
      rw [partialRow_succ r j, iterate_add, iterate_scale, iterate_translate, h, ih (by omega)]
      funext i
      simp
  have full : partialRow r 64 = r := by funext i; simp [partialRow, i.isLt]
  exact full ▸ step 64 (by decide)

theorem constant_of_table {n : Nat} {a : BitVec 6} (hc : table n = Vector.replicate 64 a) :
    iterate n delta = fun _ => a := by
  rw [← table_correct, hc]
  funext i
  exact Vector.getElem_replicate i.isLt

theorem zero_after_constant (n : Nat) (a : BitVec 6) (h : iterate n delta = fun _ => a) (r : Row) :
    iterate (n+1) r = fun _ => 0 := by
  apply zero_from_delta
  change difference (iterate n delta) = _
  rw [h]
  funext i
  exact BitVec.sub_self a

set_option maxRecDepth 262144 in
set_option maxHeartbeats 0 in
/-- At the last nonzero power every cyclic coefficient equals 32. -/
theorem penultimate_table : table 223 = Vector.replicate 64 32 := by decide +kernel

theorem iterate_223_nonzero (i : Fin 64) : iterate 223 delta i = 32 := by
  exact congrFun (constant_of_table penultimate_table) i

/-- The 224th power of X−1 annihilates the full cyclic group ring. -/
theorem iterate_224 (r : Row) : iterate 224 r = fun _ => 0 :=
  zero_after_constant 223 32 (constant_of_table penultimate_table) r

end Reimann.SignedCyclicAction

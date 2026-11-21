import Reimann.TameRationalField277

namespace Reimann.TameTraceLattice277

open TameRationalField277

def genProduct : Biquad := bm gen3 gen23

/-- Sum of the diagonal entries of multiplication by z in the basis
1, X, Y, XY. The field operations are those of TameRationalField277. -/
def regularTrace (z : Biquad) : Rat :=
  (bm z (scalar 1)).1.1 + (bm z gen3).1.2 + (bm z gen23).2.1 + (bm z genProduct).2.2

theorem trace_one (z : Biquad) : regularTrace z = 4*z.1.1 := by
  simp only [regularTrace,scalar,gen3,gen23,genProduct,bm,qm,qa,qs]
  grind

theorem trace_X (z : Biquad) : regularTrace (bm z gen3) = -12*z.1.2 := by
  rw [trace_one]
  simp only [gen3,bm,qm,qa,qs]
  grind

theorem trace_Y (z : Biquad) : regularTrace (bm z gen23) = -92*z.2.1 := by
  rw [trace_one]
  simp only [gen23,bm,qm,qa,qs]
  grind

theorem trace_XY (z : Biquad) : regularTrace (bm z genProduct) = 276*z.2.2 := by
  rw [trace_one]
  simp only [genProduct,gen3,gen23,bm,qm,qa,qs]
  grind

def IsInteger (r : Rat) : Prop := ∃ k : Int, r = (k : Rat)

def InOrder (z : Biquad) : Prop :=
  IsInteger z.1.1 ∧ IsInteger z.1.2 ∧ IsInteger z.2.1 ∧ IsInteger z.2.2

theorem scalar_mul_coords (r : Rat) (z : Biquad) :
    bm (scalar r) z = ((r*z.1.1,r*z.1.2),(r*z.2.1,r*z.2.2)) := by
  apply Prod.ext <;> apply Prod.ext <;> simp only [scalar,bm,qm,qa,qs] <;> grind

def IntegralTraces (z : Biquad) : Prop :=
  IsInteger (regularTrace z) ∧ IsInteger (regularTrace (bm z gen3)) ∧
  IsInteger (regularTrace (bm z gen23)) ∧ IsInteger (regularTrace (bm z genProduct))

/-- On the trace-dual lattice the four integer coefficients of 276z
are 69T₁, −23T_X, −3T_Y, T_XY. -/
theorem trace_clears_276 (z : Biquad) (hz : IntegralTraces z) :
    InOrder (bm (scalar 276) z) := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := hz
  rw [trace_one] at ha
  rw [trace_X] at hb
  rw [trace_Y] at hc
  rw [trace_XY] at hd
  rw [scalar_mul_coords]
  exact ⟨⟨69*a,by grind⟩,⟨-23*b,by grind⟩,⟨-3*c,by grind⟩,⟨d,hd⟩⟩

theorem order_int_scale (k : Int) (z : Biquad) (h : InOrder z) :
    InOrder (bm (scalar (k : Rat)) z) := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := h
  rw [scalar_mul_coords]
  exact ⟨⟨k*a,by grind⟩,⟨k*b,by grind⟩,⟨k*c,by grind⟩,⟨k*d,by grind⟩⟩

theorem order_traces (z : Biquad) (h : InOrder z) : IntegralTraces z := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩⟩ := h
  exact ⟨⟨4*a,by rw [trace_one,ha]; grind⟩,⟨-12*b,by rw [trace_X,hb]; grind⟩,
    ⟨-92*c,by rw [trace_Y,hc]; grind⟩,⟨276*d,by rw [trace_XY,hd]; grind⟩⟩

/-- Exact integer Bézout certificate at every precision, including depth zero. -/
theorem bezout_power (n : Nat) : ∃ j : Int, 276*j+277^n=1 := by
  induction n with
  | zero => exact ⟨0,by decide⟩
  | succ n ih =>
    obtain ⟨j,hj⟩ := ih
    refine ⟨277*j-1, ?_⟩
    rw [Int.pow_succ]
    grind

theorem denominator_unit (s : Int) (hs : ¬277 ∣ s) : ¬277 ∣ 276*s := by
  rintro ⟨k,hk⟩
  exact hs ⟨s-k,by grind⟩

/-- Localized lattice at 277, inside the rational coordinate field. -/
def Localized (L : Biquad → Prop) (z : Biquad) : Prop :=
  ∃ s : Int, (¬277 ∣ s) ∧ L (bm (scalar (s : Rat)) z)

theorem scale_twice (a b : Int) (z : Biquad) :
    bm (scalar (a : Rat)) (bm (scalar (b : Rat)) z) = bm (scalar ((a*b : Int) : Rat)) z := by
  simp only [scalar_mul_coords]
  apply Prod.ext <;> apply Prod.ext <;> grind

/-- Every lattice between the polynomial order and its trace dual gives
the same localization at 277. This requires no knowledge of its exact index. -/
theorem localized_lattice_iff (L : Biquad → Prop)
    (lower : ∀ z, InOrder z → L z) (upper : ∀ z, L z → IntegralTraces z) (z : Biquad) :
    Localized L z ↔ Localized InOrder z := by
  constructor
  · rintro ⟨s,hs,h⟩
    refine ⟨276*s,denominator_unit s hs,?_⟩
    have hc := trace_clears_276 _ (upper _ h)
    have he := scale_twice 276 s z
    change bm (scalar 276) (bm (scalar (s : Rat)) z) = _ at he
    exact he ▸ hc
  · rintro ⟨s,hs,h⟩
    exact ⟨s,hs,lower _ h⟩

abbrev M4 (S : Type) := Fin 4 → Fin 4 → S

def sum4 (f : Fin 4 → Rat) : Rat := f 0+f 1+f 2+f 3

def matrixMul (A B : M4 Rat) : M4 Rat := fun i j => sum4 (fun k => A i k * B k j)

def matrixTrace (A : M4 Rat) : Rat := sum4 (fun i => A i i)

theorem matrix_swap (A B : M4 Rat) : matrixTrace (matrixMul A B) = matrixTrace (matrixMul B A) := by
  unfold matrixTrace matrixMul sum4
  grind

theorem matrix_assoc (A B C : M4 Rat) : matrixMul (matrixMul A B) C = matrixMul A (matrixMul B C) := by
  funext i j
  unfold matrixMul sum4
  grind

def matrixOne : M4 Rat := fun i j => if i=j then 1 else 0

theorem fin_four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by
  rcases i with ⟨v,hv⟩
  have h : v=0 ∨ v=1 ∨ v=2 ∨ v=3 := by omega
  rcases h with h|h|h|h <;> subst v <;> decide +revert

theorem matrix_id_right (A : M4 Rat) : matrixMul A matrixOne = A := by
  funext i j
  rcases fin_four j with h|h|h|h <;> subst j <;> simp +decide [matrixMul,matrixOne,sum4] <;> grind

theorem matrix_id_left (A : M4 Rat) : matrixMul matrixOne A = A := by
  funext i j
  rcases fin_four i with h|h|h|h <;> subst i <;> simp +decide [matrixMul,matrixOne,sum4] <;> grind

def coordinate (i : Fin 4) (z : Biquad) : Rat :=
  match i.val with
  | 0 => z.1.1
  | 1 => z.1.2
  | 2 => z.2.1
  | _ => z.2.2

def standardBasis (j : Fin 4) : Biquad :=
  match j.val with
  | 0 => scalar 1
  | 1 => gen3
  | 2 => gen23
  | _ => genProduct

def regMatrix (z : Biquad) : M4 Rat :=
  fun i j => coordinate i (bm z (standardBasis j))

theorem regMatrix_trace (z : Biquad) : matrixTrace (regMatrix z) = regularTrace z := rfl

def column (S : M4 Rat) (j : Fin 4) : Biquad := ((S 0 j,S 1 j),(S 2 j,S 3 j))

theorem regular_on_column (z : Biquad) (S : M4 Rat) (i j : Fin 4) :
    matrixMul (regMatrix z) S i j = coordinate i (bm z (column S j)) := by
  rcases fin_four i with h|h|h|h <;> subst i <;>
    simp only [matrixMul,sum4,regMatrix,coordinate,standardBasis,column,genProduct,gen3,gen23,scalar,bm,qm,qa,qs] <;>
    grind

def intMatrix (M : M4 Int) : M4 Rat := fun i j => (M i j : Rat)

theorem integral_matrix_trace (M : M4 Int) : IsInteger (matrixTrace (intMatrix M)) := by
  refine ⟨M 0 0 + M 1 1 + M 2 2 + M 3 3,?_⟩
  simp only [matrixTrace,sum4,intMatrix]
  grind

/-- Multiplication preserves the lattice spanned by the columns of S when
every product with a basis element is an integral linear combination of the columns. -/
theorem stable_trace (z : Biquad) (S V : M4 Rat)
    (hs : matrixMul S V = matrixOne) (hv : matrixMul V S = matrixOne)
    (h : ∀ j, ∃ coefficients : Fin 4 → Int, ∀ i,
      coordinate i (bm z (column S j)) = sum4 (fun k => S i k * (coefficients k : Rat))) :
    IsInteger (regularTrace z) := by
  let M : M4 Int := fun k j => (Classical.choose (h j)) k
  have commute : matrixMul (regMatrix z) S = matrixMul S (intMatrix M) := by
    funext i j
    rw [regular_on_column]
    exact Classical.choose_spec (h j) i
  rw [← regMatrix_trace]
  have he : matrixTrace (regMatrix z) = matrixTrace (intMatrix M) := by
    calc
      matrixTrace (regMatrix z) = matrixTrace (matrixMul (regMatrix z) (matrixMul S V)) := by
        rw [hs, matrix_id_right]
      _ = matrixTrace (matrixMul (matrixMul S (intMatrix M)) V) := by rw [← matrix_assoc,commute]
      _ = matrixTrace (matrixMul V (matrixMul S (intMatrix M))) := matrix_swap _ _
      _ = matrixTrace (intMatrix M) := by rw [← matrix_assoc,hv,matrix_id_left]
  rw [he]
  exact integral_matrix_trace _

/-- Data of a full rank-four integral order between the polynomial basis and
the rational algebra. The columns of S are its integral basis. -/
structure OrderBasis (L : Biquad → Prop) where
  S : M4 Rat
  inverse : M4 Rat
  right_inv : matrixMul S inverse = matrixOne
  left_inv : matrixMul inverse S = matrixOne
  basis_mem : ∀ j, L (column S j)
  coordinates : ∀ z, L z → ∃ c : Fin 4 → Int, ∀ i,
    coordinate i z = sum4 (fun k => S i k * (c k : Rat))
  mul_mem : ∀ x y, L x → L y → L (bm x y)
  contains : ∀ z, InOrder z → L z

theorem orderBasis_trace {L : Biquad → Prop} (B : OrderBasis L) (z : Biquad) (hz : L z) :
    IsInteger (regularTrace z) :=
  stable_trace z B.S B.inverse B.right_inv B.left_inv
    (fun j => B.coordinates _ (B.mul_mem z _ hz (B.basis_mem j)))

theorem radicals_in_order : InOrder gen3 ∧ InOrder gen23 ∧ InOrder genProduct := by
  refine ⟨⟨⟨0,rfl⟩,⟨1,rfl⟩,⟨0,rfl⟩,⟨0,rfl⟩⟩,
    ⟨⟨0,rfl⟩,⟨0,rfl⟩,⟨1,rfl⟩,⟨0,rfl⟩⟩,
    ⟨⟨0,?_⟩,⟨0,?_⟩,⟨0,?_⟩,⟨1,?_⟩⟩⟩ <;>
    simp only [genProduct,bm,qa,qm,qs,gen3,gen23] <;> grind

theorem orderBasis_traces {L : Biquad → Prop} (B : OrderBasis L) (z : Biquad) (hz : L z) :
    IntegralTraces z := by
  obtain ⟨hx,hy,hxy⟩ := radicals_in_order
  exact ⟨orderBasis_trace B _ hz,orderBasis_trace B _ (B.mul_mem _ _ hz (B.contains _ hx)),
    orderBasis_trace B _ (B.mul_mem _ _ hz (B.contains _ hy)),
    orderBasis_trace B _ (B.mul_mem _ _ hz (B.contains _ hxy))⟩

/-- Every full integral overorder certified by an integral basis has this
same localization. The upper trace bound is proved from stability. -/
theorem full_order_localization {L : Biquad → Prop} (B : OrderBasis L) (z : Biquad) :
    Localized L z ↔ Localized InOrder z :=
  localized_lattice_iff L B.contains (orderBasis_traces B) z

end Reimann.TameTraceLattice277

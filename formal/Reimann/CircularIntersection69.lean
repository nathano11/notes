import Reimann.CircularKernel69

/-! Exponents at 69 and 277 and the two odd quadratic characters. The
identity and simultaneous-conjugation signatures encode the real-subfield
condition on generator labels. The conclusions concern exponent classes. -/
namespace Reimann.CircularIntersection69

open CircularPolynomial69 CircularKernel69

def res69 (r : Fin 19113) : Fin 69 := ⟨r.val % 69, Nat.mod_lt _ (by decide)⟩

def res277 (r : Fin 19113) : Fin 277 := ⟨r.val % 277, Nat.mod_lt _ (by decide)⟩

def crt (a : Fin 69) (b : Fin 277) : Fin 19113 :=
  ⟨(277*a.val + 18837*b.val) % 19113,Nat.mod_lt _ (by decide)⟩

theorem crt_res69 (a : Fin 69) (b : Fin 277) : res69 (crt a b) = a := by
  apply Fin.ext
  change (277*a.val + 18837*b.val) % 19113 % 69 = a.val
  rw [Nat.mod_mod_of_dvd _ (by decide : 69 ∣ 19113)]
  rw [show 277*a.val + 18837*b.val = a.val + 69*(4*a.val+273*b.val) by omega,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt a.isLt]

theorem crt_res277 (a : Fin 69) (b : Fin 277) : res277 (crt a b) = b := by
  apply Fin.ext
  change (277*a.val + 18837*b.val) % 19113 % 277 = b.val
  rw [Nat.mod_mod_of_dvd _ (by decide : 277 ∣ 19113)]
  rw [show 277*a.val + 18837*b.val = b.val + 277*(a.val+68*b.val) by omega,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt b.isLt]

theorem crt_reconstruct (r : Fin 19113) : crt (res69 r) (res277 r) = r := by
  apply Fin.ext
  change (277*(r.val%69) + 18837*(r.val%277))%19113 = r.val
  have h69 := Nat.mod_add_div r.val 69
  have h277 := Nat.mod_add_div r.val 277
  have identity : 277*(r.val%69) + 18837*(r.val%277) +
      19113*((r.val/69)+273*(r.val/277)) = r.val+19113*r.val := by omega
  have h := congrArg (fun k : Nat => k % 19113) identity
  simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt] using h

theorem coprime_residue (n m : Nat) : Nat.Coprime (n%m) m ↔ Nat.Coprime n m := by
  simp only [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_comm n m,Nat.gcd_rec m n]

theorem crt_unit_iff (r : Fin 19113) :
    Nat.Coprime r.val 19113 ↔ Nat.Coprime (res69 r).val 69 ∧ Nat.Coprime (res277 r).val 277 := by
  change Nat.Coprime r.val (69*277) ↔ Nat.Coprime (r.val%69) 69 ∧ Nat.Coprime (r.val%277) 277
  rw [Nat.coprime_mul_iff_right,coprime_residue,coprime_residue]

def chi3 (a : Nat) : Nat := match a % 3 with | 0 => 0 | 1 => 1 | _ => 276

def chi23 (a : Nat) : Nat := match (a % 23)^11 % 23 with | 0 => 0 | 1 => 1 | _ => 276

theorem eta_factors (a : Nat) : eta a = (chi3 a * chi23 a) % 277 := rfl

theorem chi3_square_classes : ∀ a : Fin 3, chi3 a.val = 1 ↔
    a.val ≠ 0 ∧ ∃ u : Fin 3, u.val^2 % 3 = a.val := by decide +kernel

theorem chi23_square_classes : ∀ a : Fin 23, chi23 a.val = 1 ↔
    a.val ≠ 0 ∧ ∃ u : Fin 23, u.val^2 % 23 = a.val := by decide +kernel

theorem chi3_mul : ∀ a b : Fin 3, chi3 ((a.val*b.val)%3) = (chi3 a.val*chi3 b.val)%277 := by
  decide +kernel

theorem chi23_mul : ∀ a b : Fin 23, chi23 ((a.val*b.val)%23) = (chi23 a.val*chi23 b.val)%277 := by
  decide +kernel

theorem equal_signs_iff : ∀ a : Fin 69, eta a.val = 1 ↔
    (chi3 a.val = 1 ∧ chi23 a.val = 1) ∨ (chi3 a.val = 276 ∧ chi23 a.val = 276) := by
  decide +kernel

def signature (r : Fin 19113) : Nat × Nat × Fin 277 :=
  (chi3 (res69 r).val, chi23 (res69 r).val, res277 r)

theorem identity_signature : signature 1 = (1,1,1) := by decide +kernel

theorem conjugation_signature : signature 19112 = (276,276,276) := by decide +kernel

def FixesRealLabels (r : Fin 19113) : Prop :=
  signature r = signature 1 ∨ signature r = signature 19112

theorem real_labels_iff (r : Fin 19113) : FixesRealLabels r ↔
    (chi3 (res69 r).val = 1 ∧ chi23 (res69 r).val = 1 ∧ res277 r = 1) ∨
    (chi3 (res69 r).val = 276 ∧ chi23 (res69 r).val = 276 ∧ res277 r = 276) := by
  rw [FixesRealLabels,identity_signature,conjugation_signature]
  simp only [signature,Prod.mk.injEq]

theorem real_labels_positive (r : Fin 19113) (h : FixesRealLabels r) :
    eta (res69 r).val = 1 := by
  apply (equal_signs_iff _).mpr
  rcases (real_labels_iff r).mp h with ⟨s,t,_⟩ | ⟨s,t,_⟩
  · exact Or.inl ⟨s,t⟩
  · exact Or.inr ⟨s,t⟩

theorem real_labels_unit (r : Fin 19113) (h : FixesRealLabels r) : Nat.Coprime r.val 19113 := by
  apply (crt_unit_iff _).mpr
  refine ⟨(unit_partition _).mpr (Or.inl (real_labels_positive _ h)),?_⟩
  rcases (real_labels_iff _).mp h with ⟨_,_,e⟩ | ⟨_,_,e⟩ <;> rw [e] <;> decide

theorem lift_positive_signs (a : Fin 69) (h3 : chi3 a.val = 1) (h23 : chi23 a.val = 1) :
    FixesRealLabels (crt a 1) := by
  apply (real_labels_iff _).mpr
  exact Or.inl (by rw [crt_res69,crt_res277]; exact ⟨h3,h23,rfl⟩)

theorem lift_negative_signs (a : Fin 69) (h3 : chi3 a.val = 276) (h23 : chi23 a.val = 276) :
    FixesRealLabels (crt a 276) := by
  apply (real_labels_iff _).mpr
  exact Or.inr (by rw [crt_res69,crt_res277]; exact ⟨h3,h23,rfl⟩)

theorem restriction_image (a : Fin 69) :
    (∃ r : Fin 19113, Nat.Coprime r.val 19113 ∧ FixesRealLabels r ∧ res69 r = a) ↔ eta a.val = 1 := by
  constructor
  · rintro ⟨r,_,h,rfl⟩
    exact real_labels_positive r h
  · intro h
    rcases (equal_signs_iff _).mp h with ⟨s,t⟩ | ⟨s,t⟩
    · have lift := lift_positive_signs a s t
      exact ⟨crt a 1,real_labels_unit _ lift,lift,crt_res69 ..⟩
    · have lift := lift_negative_signs a s t
      exact ⟨crt a 276,real_labels_unit _ lift,lift,crt_res69 ..⟩

/-- The two Booleans label the choices of sign of the quadratic generators.
The last component labels a power of the primitive 277th root. -/
abbrev GeneratorLabels := Bool × Bool × Fin 277

def actLabels (r : Fin 19113) (t : GeneratorLabels) : GeneratorLabels :=
  (if chi3 (res69 r).val = 1 then t.1 else !t.1,
   if chi23 (res69 r).val = 1 then t.2.1 else !t.2.1, res277 r * t.2.2)

def conjugateLabels (t : GeneratorLabels) : GeneratorLabels := (!t.1,!t.2.1,-t.2.2)

/-- Pointwise fixation of triples modulo their simultaneous conjugates. -/
def PointwiseReal (r : Fin 19113) : Prop :=
  ∀ t : GeneratorLabels, actLabels r t = t ∨ actLabels r t = conjugateLabels t

theorem tame_conjugate : ∀ b : Fin 277, 276 * b = -b := by decide +kernel

theorem signatures_fix_orbits (r : Fin 19113) (h : FixesRealLabels r) : PointwiseReal r := by
  rintro ⟨u,v,b⟩
  rcases (real_labels_iff _).mp h with ⟨s,t,e⟩ | ⟨s,t,e⟩
  · exact Or.inl (by simp [actLabels,s,t,e,Lean.Grind.Semiring.one_mul])
  · exact Or.inr (by simp [actLabels,conjugateLabels,s,t,e,tame_conjugate])

theorem quadratic_unit_signs : ∀ a : Fin 69, Nat.Coprime a.val 69 →
    (chi3 a.val = 1 ∨ chi3 a.val = 276) ∧ (chi23 a.val = 1 ∨ chi23 a.val = 276) := by
  decide +kernel

theorem pointwise_signature (r : Fin 19113) (unit : Nat.Coprime r.val 19113)
    (h : PointwiseReal r) : FixesRealLabels r := by
  have test := h (false,false,1)
  obtain ⟨u,v⟩ := quadratic_unit_signs (res69 r) ((crt_unit_iff _).mp unit).1
  apply (real_labels_iff _).mpr
  rcases u with s | s <;> rcases v with t | t <;>
    simp [actLabels,conjugateLabels,s,t,Lean.Grind.Semiring.mul_one] at test ⊢ <;> exact test

theorem pointwise_restriction_image (a : Fin 69) :
    (∃ r : Fin 19113, Nat.Coprime r.val 19113 ∧ PointwiseReal r ∧ res69 r = a) ↔ eta a.val = 1 := by
  rw [← restriction_image]
  constructor
  · rintro ⟨r,hu,h,ha⟩
    exact ⟨r,hu,pointwise_signature r hu h,ha⟩
  · rintro ⟨r,hu,h,ha⟩
    exact ⟨r,hu,signatures_fix_orbits r h,ha⟩

theorem projected_product_stabilizer {R : Type} [Lean.Grind.Field R] [Lean.Grind.IsCharP R 0]
    (x : R) (h69 : x^69 = 1) (h23 : x^23 ≠ 1) (h3 : x^3 ≠ 1)
    (a : Fin 69) (hu : Nat.Coprime a.val 69) :
    (∃ r : Fin 19113, Nat.Coprime r.val 19113 ∧ PointwiseReal r ∧ res69 r = a) ↔
      signedProduct (x^a.val) 1 = signedProduct x 1 :=
  (pointwise_restriction_image a).trans (primitive_positive_stabilizer x h69 h23 h3 a hu).symm

end Reimann.CircularIntersection69

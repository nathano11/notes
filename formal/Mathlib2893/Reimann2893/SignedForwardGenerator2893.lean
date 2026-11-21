import Reimann2893.SignedForwardPeriod2893
import Mathlib.GroupTheory.OrderOfElement

/-! Exact order of the forward automorphism, from the quadratic multiplier norms. -/
namespace Reimann.SignedForwardGenerator2893

open SignedFieldLayers2893 SignedForwardPeriod2893

def orbitProduct {K : Type*} [Field K] (σ : K ≃+* K) (x : K) : Nat → K
  | 0 => 1
  | j+1 => orbitProduct σ x j * (σ^j) x

theorem orbit_add {K : Type*} [Field K] (σ : K ≃+* K) (x : K) (j k : Nat) :
    orbitProduct σ x (j+k) = orbitProduct σ x j * orbitProduct σ ((σ^j) x) k := by
  induction k with
  | zero => simp [orbitProduct]
  | succ k ih =>
    change orbitProduct σ x (j+k) * (σ^(j+k)) x =
      orbitProduct σ x j * (orbitProduct σ ((σ^j) x) k * (σ^k) ((σ^j) x))
    rw [ih, Nat.add_comm j k, pow_add, RingAut.mul_apply, mul_assoc]

theorem orbit_mul {K : Type*} [Field K] (σ : K ≃+* K) (x y : K) (j : Nat) :
    orbitProduct σ (x*y) j = orbitProduct σ x j * orbitProduct σ y j := by
  induction j with
  | zero => simp [orbitProduct]
  | succ j ih => simp only [orbitProduct,ih,map_mul]; ring

theorem orbit_double {K : Type*} [Field K] (σ : K ≃+* K) (x : K) (j : Nat) :
    orbitProduct σ x (j*2) = orbitProduct σ (x*(σ^j) x) j := by
  rw [Nat.mul_two, orbit_add, orbit_mul]

theorem orbit_include (n j : Nat) (x : Layer n) :
    orbitProduct (forward (n+1)) (includeNext n x) j =
      includeNext n (orbitProduct (forward n) x j) := by
  induction j with
  | zero => simp [orbitProduct]
  | succ j ih => simp only [orbitProduct,ih,map_mul,pow_include]

theorem root_multiplier (n : Nat) :
    forward (n+1) (traceRoot (n+1)) = includeNext n (multiplier (traceRoot n))*traceRoot (n+1) := by
  rw [forward_five]
  let y := traceRoot (n+1)
  change y^5-5*y^3+5*y = _
  calc
    _ = ((y^2)^2-5*y^2+5)*y := by ring
    _ = _ := by
      change (((traceRoot (n+1))^2)^2-5*(traceRoot (n+1))^2+5)*traceRoot (n+1)=_
      rw [traceRoot_succ_sq]
      simp only [multiplier,map_add,map_ofNat,map_sub,map_pow,map_one]
      ring

theorem power_on_trace (n j : Nat) :
    (forward (n+1)^j) (traceRoot (n+1)) =
      includeNext n (orbitProduct (forward n) (multiplier (traceRoot n)) j)*traceRoot (n+1) := by
  induction j with
  | zero => simp [orbitProduct]
  | succ j ih =>
    rw [pow_succ, RingAut.mul_apply, root_multiplier, map_mul, pow_include, ih, orbitProduct, map_mul]
    ring

theorem multiplier_norm (n : Nat) :
    multiplier (traceRoot (n+1))*multiplier (-traceRoot (n+1)) =
      includeNext n (multiplier (-traceRoot n)) := by
  let y := traceRoot (n+1)
  calc
    _ = (y^2)^2-3*y^2+1 := by dsimp [y,multiplier]; ring
    _ = _ := by
      change ((traceRoot (n+1))^2)^2-3*(traceRoot (n+1))^2+1 = _
      rw [traceRoot_succ_sq]
      simp only [multiplier,map_sub,map_add,map_ofNat,map_pow,map_neg,map_one]
      ring

theorem map_multiplier {K L : Type*} [Field K] [Field L] (σ : K ≃+* L) (x : K) :
    σ (multiplier x) = multiplier (σ x) := by simp [multiplier]

theorem multiplier_orbits (n : Nat) :
    orbitProduct (forward n) (multiplier (traceRoot n)) (2^n) = -1 ∧
      orbitProduct (forward n) (multiplier (-traceRoot n)) (2^n) = -1 := by
  induction n with
  | zero => simp [orbitProduct, traceRoot_zero, multiplier]
  | succ n ih =>
    have flip : (forward (n+1)^(2^n)) (traceRoot (n+1)) = -traceRoot (n+1) := by
      rw [power_on_trace, ih.1, map_neg, map_one, neg_one_mul]
    have both := multiplier_norm n
    have descent :
        orbitProduct (forward (n+1)) (includeNext n (multiplier (-traceRoot n))) (2^n) = -1 := by
      rw [orbit_include, ih.2, map_neg, map_one]
    constructor
    · rw [pow_succ 2 n, orbit_double, map_multiplier, flip, both, descent]
    · rw [pow_succ 2 n, orbit_double, map_multiplier, map_neg, flip, neg_neg]
      rw [mul_comm (multiplier _) (multiplier _), both, descent]

/-- The half turn on each nontrivial layer is its quadratic conjugation on the new trace. -/
theorem forward_half_turn (n : Nat) :
    (forward (n+1)^(2^n)) (traceRoot (n+1)) = -traceRoot (n+1) := by
  rw [power_on_trace, (multiplier_orbits n).1, map_neg, map_one, neg_one_mul]

theorem trace_nonzero (n : Nat) : traceRoot (n+1) ≠ 0 := by
  intro h
  have eqn := traceRoot_succ_sq n
  rw [h,zero_pow (by decide)] at eqn
  apply radicand_ne_zero (tower n)
  change 2+traceRoot n = 0
  apply (includeNext n).injective
  rw [map_zero]
  exact eqn.symm

theorem half_turn_nontrivial (n : Nat) : forward (n+1)^(2^n) ≠ 1 := by
  intro h
  have e := forward_half_turn n
  rw [h, RingAut.one_apply] at e
  have htwo : (2:Layer (n+1)) * traceRoot (n+1) = 0 := by
    calc
      _ = traceRoot (n+1) + traceRoot (n+1) := two_mul _
      _ = traceRoot (n+1) + -traceRoot (n+1) := congrArg (traceRoot (n+1) + ·) e
      _ = 0 := add_neg_cancel _
  exact trace_nonzero n ((mul_eq_zero.mp htwo).resolve_left two_ne_zero)

/-- Each finite-layer automorphism attains the complete dyadic order. -/
theorem forward_order (n : Nat) : orderOf (forward n) = 2^n := by
  cases n with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff]
    rfl
  | succ n => exact orderOf_eq_prime_pow (half_turn_nontrivial n) (forward_period (n+1))

theorem extend_ext (n : Nat) {L : Type*} [Field L] (i k : Layer (n+1) →+* L)
    (base : ∀ a : Layer n, i (includeNext n a) = k (includeNext n a))
    (root : i (traceRoot (n+1)) = k (traceRoot (n+1))) : i = k := by
  apply RingHom.ext
  intro z
  obtain ⟨a,b,rfl⟩ := span_next n z
  simp only [map_add,map_mul,base,root]

/-- Any two embeddings of a finite layer into the same field over the same
bottom embedding are related by a bounded power of the forward automorphism. -/
theorem embeddings_conjugate (n : Nat) {L : Type*} [Field L] (i k : Layer n →+* L)
    (same : ∀ b : Bottom, i (embedBottom n b) = k (embedBottom n b)) :
    ∃ j : Nat, j < 2^n ∧ ∀ x : Layer n, i ((forward n^j) x) = k x := by
  induction n with
  | zero =>
    refine ⟨0,by decide,fun x => ?_⟩
    rw [pow_zero,RingAut.one_apply]
    exact same x
  | succ n ih =>
    obtain ⟨m,hm,agree⟩ := ih (i.comp (includeNext n)) (k.comp (includeNext n)) (fun b => same b)
    let twist (j : Nat) := i.comp (forward (n+1)^j).toRingHom
    have base (a : Layer n) : twist m (includeNext n a) = k (includeNext n a) := by
      change i ((forward (n+1)^m) (includeNext n a)) = k (includeNext n a)
      rw [pow_include]
      exact agree a
    have squares : (twist m (traceRoot (n+1)))^2 = (k (traceRoot (n+1)))^2 := by
      rw [←map_pow,←map_pow,traceRoot_succ_sq,base]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp squares with hp | hn
    · refine ⟨m,by rw [pow_succ]; omega,fun x => ?_⟩
      exact DFunLike.congr_fun (extend_ext n _ _ base hp) x
    · let j := m+2^n
      have comp' (x : Layer (n+1)) : twist j x = twist m ((forward (n+1)^(2^n)) x) := by
        change i ((forward (n+1)^(m+2^n)) x) = i ((forward (n+1)^m) ((forward (n+1)^(2^n)) x))
        rw [pow_add,RingAut.mul_apply]
      have b' (a : Layer n) : twist j (includeNext n a) = k (includeNext n a) := by
        rw [comp',pow_include,forward_period,RingAut.one_apply,base]
      have r' : twist j (traceRoot (n+1)) = k (traceRoot (n+1)) := by
        rw [comp',forward_half_turn,map_neg,hn,neg_neg]
      exact ⟨j,by dsimp [j]; rw [pow_succ]; omega, fun x => DFunLike.congr_fun (extend_ext n _ _ b' r') x⟩

/-- Every relative field automorphism is a unique power in the indicated range. -/
theorem relative_generator (n : Nat) (σ : Layer n ≃+* Layer n)
    (fixed : ∀ b : Bottom, σ (embedBottom n b) = embedBottom n b) :
    ∃! j : Fin (2^n), σ = (forward n)^j.val := by
  obtain ⟨m,hm,eqn⟩ := embeddings_conjugate n (RingHom.id _) σ.toRingHom (fun b => (fixed b).symm)
  have rep : σ = (forward n)^m := RingEquiv.ext (fun x => (eqn x).symm)
  refine ⟨⟨m,hm⟩,rep,?_⟩
  intro j hj
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := forward n) _ _ (hj.symm.trans rep)
  · change j.val < orderOf (forward n)
    rw [forward_order]
    exact j.isLt
  · change m < orderOf (forward n)
    rwa [forward_order]

end Reimann.SignedForwardGenerator2893

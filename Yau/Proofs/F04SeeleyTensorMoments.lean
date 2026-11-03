import Yau.Proofs.F04SeeleyTensor

open scoped Topology

noncomputable section
set_option maxHeartbeats 1000000

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem reflectLinear_decompose (k : ℕ) (p : E × ℝ) :
    reflectLinear k p = (p.1, 0) + (-dyadic k) • (0, p.2) := by
  ext <;> simp [reflectLinear_apply]

/-- The shifted version makes induction in the number of tensor slots
possible: splitting off one time slot shifts the scalar moment by one. -/
theorem tensor_moment_shift : ∀ m q : ℕ, ∀ A : Jet E F m,
    HasSum (fun k => (seeleyWeight k * (-dyadic k) ^ q) •
      A.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)) A := by
  intro m
  induction m with
  | zero =>
    intro q A
    have hcomp (k : ℕ) : A.compContinuousLinearMap (fun _ : Fin 0 => reflectLinear k) = A := by
      apply ContinuousMultilinearMap.ext
      intro v
      change A (fun i : Fin 0 => reflectLinear k (v i)) = A v
      congr 1
      funext i
      exact Fin.elim0 i
    simpa only [hcomp, one_smul] using (seeleyWeight_moment q).smul_const A
  | succ m ih =>
    intro q A
    have hs := tensor_moment_summable (m + 1) q A
    have heq : (∑' k, (seeleyWeight k * (-dyadic k) ^ q) •
        A.compContinuousLinearMap (fun _ : Fin (m + 1) => reflectLinear k)) = A := by
      ext v
      rw [ContinuousMultilinearMap.tsum_eval hs v]
      let P : E × ℝ := ((v 0).1, 0)
      let Q : E × ℝ := (0, (v 0).2)
      let vv : Fin m → E × ℝ := fun i => v i.succ
      let A0 : Jet E F m := A.curryLeft P
      let A1 : Jet E F m := A.curryLeft Q
      have hs0 := ContinuousMultilinearMap.hasSum_eval (ih q A0) vv
      have hs1 := ContinuousMultilinearMap.hasSum_eval (ih (q + 1) A1) vv
      have hcons (k : ℕ) : (fun i : Fin (m + 1) => reflectLinear k (v i)) =
          Fin.cons (reflectLinear k (v 0)) (fun i : Fin m => reflectLinear k (vv i)) := by
        funext i
        refine Fin.cases (by rfl) (fun j => by rfl) i
      have hterm (k : ℕ) :
          ((seeleyWeight k * (-dyadic k) ^ q) •
            A.compContinuousLinearMap (fun _ : Fin (m + 1) => reflectLinear k)) v =
          ((seeleyWeight k * (-dyadic k) ^ q) •
            A0.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)) vv +
          ((seeleyWeight k * (-dyadic k) ^ (q + 1)) •
            A1.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)) vv := by
        change (seeleyWeight k * (-dyadic k) ^ q) •
          A (fun i => reflectLinear k (v i)) = _
        rw [hcons, ← ContinuousMultilinearMap.curryLeft_apply, reflectLinear_decompose,
          map_add, map_smul]
        simp only [add_apply, smul_apply,
          smul_add, smul_smul, pow_succ, mul_assoc]
        rfl
      have hpq : P + Q = v 0 := by ext <;> simp [P, Q]
      have hav : A0 vv + A1 vv = A v := by
        change A.curryLeft P vv + A.curryLeft Q vv = A v
        rw [← add_apply, ← map_add, hpq,
          ContinuousMultilinearMap.curryLeft_apply]
        congr 1
        funext i
        refine Fin.cases (by rfl) (fun j => by rfl) i
      have hsum : HasSum (fun k => ((seeleyWeight k * (-dyadic k) ^ q) •
          A.compContinuousLinearMap (fun _ : Fin (m + 1) => reflectLinear k)) v) (A v) := by
        convert hs0.add hs1 using 1
        · funext k
          exact hterm k
        · exact hav.symm
      exact hsum.tsum_eq
    convert hs.hasSum using 1
    exact heq.symm

theorem seeley_tensor_moment (m : ℕ) (A : Jet E F m) :
    HasSum (fun k => seeleyWeight k •
      A.compContinuousLinearMap (fun _ : Fin m => reflectLinear k)) A := by
  simpa only [pow_zero, mul_one] using tensor_moment_shift m 0 A

end Yau.F04Proof.Seeley

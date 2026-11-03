import Yau.Proofs.F05NonlinearInitial

/-! First equation compatibility for a nonconstant initial profile makes the
actual correction source initially zero, as required for positive-time restart. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_initial_general (h : ℝ → HermitianField M) (T : ℝ)
    (p z : M.Carrier → ℝ → ℝ) (hZ0 : ∀ x, z x 0 = 0)
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 T) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) (x : M.Carrier) :
    F05NonlinearCorrection h T p z x 0 = 0 := by
  unfold F05NonlinearCorrection F05IntrinsicLinearOperator
  rw [hZ0 x,add_zero,sub_self,zero_mul,zero_add,hCompat x]
  ring

end Yau.Proofs.F05Aux

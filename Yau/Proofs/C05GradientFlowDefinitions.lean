import Yau.Geometry.Calculus

/-! Computed real gradient and covariant Hessian for the metric G = 2 Re h. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05GradientFlowAux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def realPairing (k : HermitianField M) (x : M.Carrier)
    (v w : TangentVector M x) : ℝ :=
  2 * ((k x).toFun v w).re

def realNormSq (k : HermitianField M) (x : M.Carrier) (v : TangentVector M x) : ℝ :=
  2 * Yau.hermitianNormSq (k x) v

def realNorm (k : HermitianField M) (x : M.Carrier) (v : TangentVector M x) : ℝ :=
  Real.sqrt (realNormSq k x v)

def realGradComponent (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (a : RIdx n) : ℝ :=
  ∑ b : RIdx n, (realMetricFn k c z)⁻¹ a b * rDeriv (inChart c f) z b

def realGradInChart (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (fun i => (realGradComponent k f c z (i, 0) : ℂ) +
    Complex.I * (realGradComponent k f c z (i, 1) : ℂ))

def realGrad (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) : TangentVector M x :=
  chartVec x x (realGradInChart k f x (chartPt x x))

def realHessInChart (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (a b : RIdx n) : ℝ :=
  rDeriv (fun w => rDeriv (inChart c f) w b) z a -
    ∑ q : RIdx n, christoffel k c z q a b * rDeriv (inChart c f) z q

def realHess (k : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier)
    (v w : TangentVector M x) : ℝ :=
  ∑ a : RIdx n, ∑ b : RIdx n,
    realHessInChart k f x (chartPt x x) a b *
      realCoord (tangentCoords x x v) a * realCoord (tangentCoords x x w) b

@[simp] theorem realPairing_self (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) : realPairing k x v v = realNormSq k x v := rfl

theorem realNormSq_nonneg (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) : 0 ≤ realNormSq k x v :=
  mul_nonneg (by norm_num) (hermitianNormSq_nonneg (k x) v)

theorem realNormSq_pos (k : HermitianField M) (x : M.Carrier)
    {v : TangentVector M x} (hv : v ≠ 0) : 0 < realNormSq k x v :=
  mul_pos (by norm_num) (hermitianNormSq_pos (k x) hv)

theorem realNorm_nonneg (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) : 0 ≤ realNorm k x v := Real.sqrt_nonneg _

theorem realNorm_sq (k : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) : realNorm k x v ^ 2 = realNormSq k x v :=
  Real.sq_sqrt (realNormSq_nonneg k x v)

end Yau.Proofs.C05GradientFlowAux

import Yau.Proofs.C07CurveConcatSpeed

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07PolygonalPrefixAux

open Yau Set MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

def constantPiecewise (x : M.Carrier) : PiecewiseC1Curve x x where
  toFun := fun _ => x
  start_eq := rfl
  finish_eq := rfl
  breakpoints := ∅
  breakpoints_mem := by simp
  continuous_on := continuousOn_const
  piecewise_c1 := fun _ _ => contDiffAt_const

theorem constant_speed (g : HermitianField M) (x : M.Carrier) (u : ℝ) :
    curveSpeed g (constantPiecewise x) u = 0 := by
  have hd : realTangentDerivative (constantPiecewise x) u = 0 := by
    rw [C07CurveConcatAux.realTangentDerivative_eq_deriv_chart]
    change deriv (fun _ : ℝ => chartPt x x) u = 0
    exact deriv_const u (chartPt x x)
  rw [curveSpeed, hd]
  change Real.sqrt (2 * ((g x).toFun 0 0).re) = 0
  rw [((g x).positive_definite 0).2.mpr rfl, mul_zero, Real.sqrt_zero]

def constantIntegrable (g : HermitianField M) (x : M.Carrier) : IntegrableCurve g x x :=
  ⟨constantPiecewise x, by
    have heq : curveSpeed g (constantPiecewise x) = fun _ => 0 :=
      funext (constant_speed g x)
    rw [heq]
    exact integrableOn_zero⟩

theorem constant_length (g : HermitianField M) (x : M.Carrier) :
    curveLength g (constantIntegrable g x).1 = 0 := by
  simp [curveLength, constantIntegrable, constant_speed]

end Yau.Proofs.C07PolygonalPrefixAux

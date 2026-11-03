import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Complex

/-! The real Jacobian of complex scalar multiplication is its actual
complex norm squared, including the zero scalar. -/

noncomputable section
namespace Yau.NodeProofs.D02AreaReparamAux

theorem complex_scalar_real_det (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = Complex.normSq c := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

end Yau.NodeProofs.D02AreaReparamAux

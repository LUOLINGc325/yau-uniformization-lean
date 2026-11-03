import Yau.LeafProofs.L21ComplexLinear
import Yau.LeafProofs.L21CayleyGraph

/-! The graph acts on actual real derivatives by the frozen Wirtinger formula. -/

noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem sum_stdVec (v : X n) : ∑ i, v i • Yau.stdVec i = v := by
  ext j
  simp [Yau.stdVec, PiLp.single_apply, Pi.single_apply, eq_comm]

theorem wirt_eq_linearPart (f : X n → ℂ) (x v : X n) :
    Yau.wirt f x v = linearPart (fderiv ℝ f x) v := by
  change (1 / 2 : ℂ) * (fderiv ℝ f x v - Complex.I * fderiv ℝ f x (Complex.I • v)) =
    (1 / 2 : ℝ) • (fderiv ℝ f x v - Complex.I * fderiv ℝ f x (Complex.I • v))
  norm_num [Complex.real_smul]

theorem wirt_eq_sum (f : X n → ℂ) (x v : X n) :
    Yau.wirt f x v = ∑ k, v k * Yau.wirt f x (Yau.stdVec k) := by
  simp only [wirt_eq_linearPart]
  conv_lhs => rw [← sum_stdVec v]
  simp only [map_sum, map_smul, smul_eq_mul]

def graphMatrix (C : X n → X n →L[ℝ] X n) (x : X n) :
    Matrix (Fin n) (Fin n) ℂ := fun i k => C x (Yau.stdVec i) k

def dbarA (A : X n → Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (f : X n → ℂ) (x : X n) : ℂ :=
  Yau.wirtBar f x (Yau.stdVec i) +
    ∑ k, A x i k * Yau.wirt f x (Yau.stdVec k)

/-- The operator with the actual matrix coefficients is precisely the
complexified real vector field `R_i + i S_i`. -/
theorem dbarA_graphMatrix_eq
    (C : X n → X n →L[ℝ] X n) (i : Fin n) (f : X n → ℂ) (x : X n) :
    dbarA (graphMatrix C) i f x =
      fderiv ℝ f x (graphReal (C x) (Yau.stdVec i)) +
        Complex.I * fderiv ℝ f x (graphImag (C x) (Yau.stdVec i)) := by
  rw [dbarA]
  change Yau.wirtBar f x (Yau.stdVec i) +
    (∑ k, (C x (Yau.stdVec i)) k * Yau.wirt f x (Yau.stdVec k)) = _
  rw [← wirt_eq_sum]
  simp only [Yau.wirtBar, Yau.wirt, graphReal, graphImag, map_smul,
    map_add, smul_sub, map_sub, Complex.real_smul, smul_eq_mul]
  norm_num
  ring

end Yau.LeafProofs.L21Aux

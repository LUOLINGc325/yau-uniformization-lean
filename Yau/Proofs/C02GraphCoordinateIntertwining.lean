import Yau.Proofs.C02CayleyNativeBridge
import Yau.LeafProofs.L21GraphIntertwining

/-! The actual graph-coordinate equations give intertwining of the
whole real Fréchet differential, in the same chosen coordinate family. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ}

theorem coordinate_fderiv_apply {F : ComplexVector n → ComplexVector n}
    {x : ComplexVector n} (hF : DifferentiableAt ℝ F x) (k : Fin n) (v : ComplexVector n) :
    fderiv ℝ (fun y => F y k) x v = fderiv ℝ F x v k := by
  let L := (EuclideanSpace.proj k : ComplexVector n →L[ℂ] ℂ).restrictScalars ℝ
  have h := (L.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  exact congrArg (fun D : ComplexVector n →L[ℝ] ℂ => D v) h

theorem graph_coordinate_differential_intertwines
    (J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (F : ComplexVector n → ComplexVector n) (x : ComplexVector n)
    (hF : DifferentiableAt ℝ F x)
    (hJ2 : ∀ v, J x (J x v) = -v)
    (hClose : ‖J x - L12Aux.complexStructureCLM n‖ ≤ 1 / 4)
    (hEquation : ∀ i k, L21Aux.dbarA (cayleyCoefficientMatrix J) i (fun y => F y k) x = 0)
    (v : ComplexVector n) :
    fderiv ℝ F x (J x v) = Complex.I • fderiv ℝ F x v := by
  have hi : (J x + L21Aux.stdComplex n).IsInvertible := by
    rw [native_stdComplex_eq]
    exact (complex_sum_isInvertible_and_inverse_norm (J x) hClose).1
  ext k
  have hEq : ∀ i, L21Aux.dbarA
      (L21Aux.graphMatrix (fun y => L21Aux.cayleyMap (J y))) i (fun y => F y k) x = 0 := by
    rw [native_graphMatrix_eq]
    exact fun i => hEquation i k
  have h := (L21Aux.dbarA_cayley_eq_zero_iff J x hJ2 hi (fun y => F y k)).mp hEq v
  simpa only [coordinate_fderiv_apply hF, PiLp.smul_apply, smul_eq_mul] using h

end Yau.Blueprint.C02Proof

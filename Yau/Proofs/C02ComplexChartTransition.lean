import Yau.LeafProofs.L12

noncomputable section
open scoped Manifold ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realChartChange_fderiv_I (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) :
    fderiv ℝ (realChartChange a b) z (Complex.I • v) =
      Complex.I • fderiv ℝ (realChartChange a b) z v := by
  have hc : DifferentiableAt ℂ (realChartChange a b) z :=
    (chartTransition_contDiffAt a b hz hy).differentiableAt (by simp)
  have hd : fderiv ℝ (realChartChange a b) z = (fderiv ℂ (realChartChange a b) z).restrictScalars ℝ :=
    (hc.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [hd]
  exact (fderiv ℂ (realChartChange a b) z).map_smul Complex.I v

end Yau.Blueprint.C02Proof

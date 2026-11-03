import Yau.LeafProofs.L05DiniIteration
import Yau.LeafProofs.L16

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

abbrev DiniHessian (n : ℕ) := Space n →L[ℝ] Space n →L[ℝ] ℝ

def diniHeatD2 {n : ℕ} (a : ℝ) (y : Space n) : DiniHessian n :=
  fderiv ℝ (fderiv ℝ (L16Aux.gaussianKernel a)) y

def diniHeatD3 {n : ℕ} (a : ℝ) (y : Space n) : Space n →L[ℝ] DiniHessian n :=
  fderiv ℝ (diniHeatD2 a) y

def diniHeatDtD2 {n : ℕ} (a : ℝ) (y : Space n) : DiniHessian n :=
  deriv (fun b : ℝ => diniHeatD2 b y) a

def diniBudget (psi : ℝ → ℝ) (r : ℝ) : ℝ :=
  (∫ s in (0:ℝ)..r, psi s/s)+r*(∫ s in Set.Ioi r, psi s/s^2)

def diniDyadicAverage (psi : ℝ → ℝ) (R : ℝ) : ℝ :=
  ∑' k : ℕ, (1/4:ℝ)^k*psi ((2:ℝ)^k*R)

def diniModulusTail (G : ℝ) (phi : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else if s ≤ 1 then phi s else phi 1+2*G

end Yau.LeafProofs.L05Aux

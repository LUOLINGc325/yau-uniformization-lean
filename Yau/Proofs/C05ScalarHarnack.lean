import Yau.Proofs.C05HarnackMinimum

/-! The minimized Harnack quantity uses the original scalar curvature and
the original positive Ricci matrix, at the same point and physical time. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C05Aux

open Yau Blueprint

variable {n : ℕ} {X : KahlerManifold n}

def scalarCovector (k : HermitianField X.manifold) (x : Pt X) : ComplexVector n :=
  WithLp.toLp 2 (fun i =>
    wirt (fun z => Complex.ofReal (inChart x (scalarCurvature k) z))
      (chartPt x x) (stdVec i))

def scalarHarnackSum (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  deriv (fun s => scalarCurvature (h s) x) t + t⁻¹ * scalarCurvature (h t) x

def minimizedScalarHarnack (h : Flow X) (x : Pt X) (t : ℝ) : ℝ :=
  scalarHarnackSum h x t - dualNormMat (ricci (h t) x) (scalarCovector (h t) x)

theorem scalarHarnack_minimized (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    0 ≤ dualNormMat (ricci (h t) x) (scalarCovector (h t) x) ∧
      dualNormMat (ricci (h t) x) (scalarCovector (h t) x) ≤ scalarHarnackSum h x t := by
  apply scalar_harnack_minimum _ (hH.2.2.1 t ht.le x)
  intro v
  simpa only [scalarCovector, scalarHarnackSum, WithLp.ofLp_toLp] using
    hH.2.2.2.2.1 x t ht (WithLp.toLp 2 v)

theorem minimizedScalarHarnack_nonneg (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    0 ≤ minimizedScalarHarnack h x t :=
  sub_nonneg.mpr (scalarHarnack_minimized o h hH x ht).2

theorem minimizedScalarHarnack_le (o : Pt X) (h : Flow X)
    (hH : HarnackCompleteness X o h) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    minimizedScalarHarnack h x t ≤ scalarHarnackSum h x t :=
  sub_le_self _ (scalarHarnack_minimized o h hH x ht).1

end Yau.Proofs.C05Aux

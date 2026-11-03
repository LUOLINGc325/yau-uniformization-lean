import Yau.Proofs.C03GeodesicBoundary

/-! The linear-in-time quadratic correction contributes only its terminal
pairing to the integrated actual energy Hessian. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem source_geodesic_linear_acceleration_boundary (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ : ℝ → ComplexVector n) (hγ : ContDiff ℝ 3 γ)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv γ)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t)) t)
    (Q : ComplexVector n) :
    (∫ t in Icc (0 : ℝ) 1,
      realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
        (Q + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (t • Q))) =
      realMetricInChart k (0 : ComplexVector n) (γ 1) (deriv γ 1) Q := by
  have hT : ContDiff ℝ 1 (deriv γ) :=
    (show ContDiff ℝ (1 + 1) γ from hγ.of_le (by norm_num)).deriv'
  have hA : ContDiff ℝ 1 (fun t : ℝ => t • Q) := contDiff_id.smul contDiff_const
  have hder : deriv (fun t : ℝ => t • Q) = fun _ => Q := by
    funext t
    convert! ((hasDerivAt_id t).smul_const Q).deriv using 1 <;> simp only [id_eq, one_smul]
  have H := source_geodesic_pairing_boundary hn k hk γ (deriv γ) (fun t : ℝ => t • Q)
    (hγ.of_le (by norm_num)) hT hA
    (fun t _ => (hγ.differentiable (by norm_num) t).hasDerivAt) hgeo
  simpa only [hder, one_smul, zero_smul, map_zero, sub_zero] using H

end Yau.Proofs.C03Aux

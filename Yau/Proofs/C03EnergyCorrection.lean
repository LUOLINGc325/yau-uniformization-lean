import Yau.Proofs.C03MovingDensityCorrection
import Yau.Proofs.C03LinearAccelerationBoundary

/-! The freely chosen terminal holomorphic second jet changes the actual
energy Hessian by exactly twice its terminal metric pairing. -/

noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingEnergy_second_correction (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W) (v : ℂ)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv γ)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (deriv γ t)) t)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => v • W s)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (v • W t)) t) :
    mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W Q)) v) v 0 -
      mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W 0)) v) v 0 =
      2 * realMetricInChart k (0 : ComplexVector n) (γ 1) (deriv γ 1) (v ^ 2 • Q) := by
  have hZ (q : ComplexVector n) : ContDiffOn ℝ 3 (movingJoint γ W q) (univ ×ˢ univ) :=
    movingJoint_contDiffOn γ W q univ hγ.contDiffOn hW.contDiffOn
  rw [sourceEnergy_secondDirection hn k hk _ univ univ isOpen_univ isOpen_univ
      (subset_univ _) (hZ Q) (mem_univ _) v v,
    sourceEnergy_secondDirection hn k hk _ univ univ isOpen_univ isOpen_univ
      (subset_univ _) (hZ 0) (mem_univ _) v v,
    ← integral_sub
      (sourceEnergy_secondDirection_integrable hn k hk _ univ univ isOpen_univ isOpen_univ
        (subset_univ _) (mem_univ _) (hZ Q) v v)
      (sourceEnergy_secondDirection_integrable hn k hk _ univ univ isOpen_univ isOpen_univ
        (subset_univ _) (mem_univ _) (hZ 0) v v)]
  calc
    _ = ∫ t in Icc (0 : ℝ) 1,
        2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
          (v ^ 2 • Q + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t)
            (t • (v ^ 2 • Q))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact movingEnergyDensity_second_correction hn k hk γ W Q hγ hW v t (hparallel t ht)
    _ = 2 * (∫ t in Icc (0 : ℝ) 1,
        realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
          (v ^ 2 • Q + chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t)
            (t • (v ^ 2 • Q)))) := integral_const_mul _ _
    _ = _ := by rw [source_geodesic_linear_acceleration_boundary hn k hk γ hγ hgeo]

end Yau.Proofs.C03Aux

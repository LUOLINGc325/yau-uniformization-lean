import Yau.Proofs.C03MovingEnergyJets

/-! The explicit two-ended family has zero first energy derivative and the
genuine paired-curvature trace, using Kähler identities only near its base path. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingEnergy_fderiv_zero (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℂ,
      HasDerivAt (fun s => a • W s)
        (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t) :
    fderiv ℝ (sourceEnergy hn k (movingJoint γ W Q)) 0 = 0 := by
  have hZ : ContDiff ℝ 3 (movingJoint γ W Q) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using
      movingJoint_contDiffOn γ W Q univ hγ.contDiffOn hW.contDiffOn
  ext a
  exact sourceEnergy_firstDirection_zero hn k hk _ univ univ isOpen_univ isOpen_univ
    (subset_univ _) (mem_univ _) (by simpa only [univ_prod_univ] using hZ.contDiffOn) a
    (fun t ht => movingJoint_parallel_firstVariation _ γ W Q
      (hZ.contDiffAt.of_le (by norm_num)) a (hparallel t ht a))

theorem movingEnergy_paired_trace (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n)
    (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W)
    (O : Set (ComplexVector n)) (hO : IsOpen O)
    (himage : MapsTo γ (Icc (0 : ℝ) 1) O)
    (hI : ∀ z ∈ O, ∀ v, chartChristoffelBilin k (0 : ComplexVector n) z
      (Complex.I • v) (Complex.I • v) = -chartChristoffelBilin k (0 : ComplexVector n) z v v)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℂ,
      HasDerivAt (fun s => a • W s)
        (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t) :
    mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W Q)) 1) 1 0 +
      mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W Q)) Complex.I) Complex.I 0 =
      ∫ t in Icc (0 : ℝ) 1,
        2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
          (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (γ t)
            (W t) (deriv γ t) (W t)) +
        2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
          (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (γ t)
            (Complex.I • W t) (deriv γ t) (Complex.I • W t)) := by
  let Z := movingJoint γ W Q
  have hZ : ContDiff ℝ 3 Z := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using
      movingJoint_contDiffOn γ W Q univ hγ.contDiffOn hW.contDiffOn
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (a : ℂ) :
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
        (mapDirection Z (a, 0)) (0, t) = 0 :=
    movingJoint_parallel_firstVariation _ γ W Q (hZ.contDiffAt.of_le (by norm_num)) a
      (hparallel t ht a)
  have hr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
          (mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (1, 0)
            (mapDirection Z (1, 0))) (0, t) +
        mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
          (mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (Complex.I, 0)
            (mapDirection Z (Complex.I, 0))) (0, t) = 0 := by
    apply covariant_radial_pair_time_zero k hk (0 : ComplexVector n) Z
      (by rw [euclidean_chartTarget hn]; trivial) hZ.contDiffAt
    have hbase : Z (0, t) ∈ O := by
      simpa only [Z, movingJoint, movingTrial_zero_parameter] using himage ht
    have hnear : ∀ᶠ p in 𝓝 (0, t), Z p ∈ O :=
      hZ.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hbase)
    filter_upwards [hnear] with p hp
    exact movingJoint_radial_covariant_trace _ γ W Q
      (hZ.contDiffAt.of_le (by norm_num)) (hI (Z p) hp)
  have H := sourceEnergy_paired_secondVariation hn k hk Z univ univ
    isOpen_univ isOpen_univ (subset_univ _) (mem_univ _)
    (by simpa only [univ_prod_univ] using hZ.contDiffOn) 1 Complex.I
    (fun t ht => hp t ht 1) (fun t ht => hp t ht Complex.I) hr
  rw [H]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hZd : DifferentiableAt ℝ (movingJoint γ W Q) (0, t) :=
    hZ.differentiable (by norm_num) (0, t)
  simp only [Z, movingJoint_time_jet_zero γ W Q hZd,
    movingJoint_parameter_jet γ W Q hZd, mul_zero, zero_smul, add_zero, one_smul,
    movingJoint, movingTrial_zero_parameter]

end Yau.Proofs.C03Aux

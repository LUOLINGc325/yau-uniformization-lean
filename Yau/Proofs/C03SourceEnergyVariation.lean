import Yau.Proofs.C03SourceEnergy

/-! The compact energy integral retains both moving endpoints in its
paired second variation. No endpoint acceleration is discarded. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem sourceEnergy_firstDirection_zero (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ℂ) ∈ U) (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) (v : ℂ)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1,
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
        (mapDirection Z (v, 0)) (0, t) = 0) :
    mapDirection (sourceEnergy hn k Z) v 0 = 0 := by
  rw [sourceEnergy_firstDirection hn k hk Z U J hU hJ hunit hZ hzero v]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  apply mapEnergyDensity_firstDirection_zero k hk (0 : ComplexVector n) Z
    (by rw [euclidean_chartTarget hn]; trivial)
    ((hZ.contDiffAt ((hU.prod hJ).mem_nhds ⟨hzero, hunit ht⟩)).of_le (by norm_num))
    (v, 0) (0, 1) (hparallel t ht)

theorem sourceEnergy_secondDirection_integrable (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ℂ) ∈ U) (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) (v w : ℂ) :
    IntegrableOn (fun t => mapDirection
      (mapDirection (sourceEnergyDensity hn k Z) (v, 0)) (w, 0) (0, t)) (Icc (0 : ℝ) 1) := by
  change IntegrableOn (fun t => parameterDirection
    (parameterDirection (sourceEnergyDensity hn k Z) v) w (0, t)) _
  have HD := sourceEnergyDensity_contDiffOn hn k hk Z _ (hU.prod hJ) hZ
  have HC := (parameterDirection_contDiffOn hU hJ 0
    (parameterDirection_contDiffOn hU hJ 1 HD v) w).continuousOn
  exact (HC.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ ht => ⟨hzero, hunit ht⟩)).integrableOn_Icc

theorem sourceEnergy_paired_secondVariation (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hzero : (0 : ℂ) ∈ U) (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) (v vi : ℂ)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1,
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
        (mapDirection Z (v, 0)) (0, t) = 0)
    (hparallelI : ∀ t ∈ Icc (0 : ℝ) 1,
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
        (mapDirection Z (vi, 0)) (0, t) = 0)
    (hradial : ∀ t ∈ Icc (0 : ℝ) 1,
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
          (mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (v, 0)
            (mapDirection Z (v, 0))) (0, t) +
        mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
          (mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (vi, 0)
            (mapDirection Z (vi, 0))) (0, t) = 0) :
    mapDirection (mapDirection (sourceEnergy hn k Z) v) v 0 +
      mapDirection (mapDirection (sourceEnergy hn k Z) vi) vi 0 =
      ∫ t in Icc (0 : ℝ) 1,
        2 * realMetricInChart k (0 : ComplexVector n) (Z (0, t))
          (mapDirection Z (0, 1) (0, t))
          (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (Z (0, t))
            (mapDirection Z (v, 0) (0, t)) (mapDirection Z (0, 1) (0, t))
            (mapDirection Z (v, 0) (0, t))) +
        2 * realMetricInChart k (0 : ComplexVector n) (Z (0, t))
          (mapDirection Z (0, 1) (0, t))
          (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (Z (0, t))
            (mapDirection Z (vi, 0) (0, t)) (mapDirection Z (0, 1) (0, t))
            (mapDirection Z (vi, 0) (0, t))) := by
  rw [sourceEnergy_secondDirection hn k hk Z U J hU hJ hunit hZ hzero,
    sourceEnergy_secondDirection hn k hk Z U J hU hJ hunit hZ hzero,
    ← integral_add (sourceEnergy_secondDirection_integrable hn k hk Z U J hU hJ hunit hzero hZ v v)
      (sourceEnergy_secondDirection_integrable hn k hk Z U J hU hJ hunit hzero hZ vi vi)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have HZ : ContDiffAt ℝ 3 Z (0, t) :=
    hZ.contDiffAt ((hU.prod hJ).mem_nhds ⟨hzero, hunit ht⟩)
  have hp (a : ℂ) :
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (a, 0)
        (mapDirection Z (0, 1)) (0, t) =
      mapCovariantD (chartChristoffelBilin k (0 : ComplexVector n)) Z (0, 1)
        (mapDirection Z (a, 0)) (0, t) :=
    mapCovariantD_torsionFree _ Z (HZ.of_le (by norm_num))
      (chartChristoffelBilin_symm k (0 : ComplexVector n) (Z (0, t))) _ _
  exact mapEnergyDensity_paired_secondVariation k hk (0 : ComplexVector n) Z
    (by rw [euclidean_chartTarget hn]; trivial) HZ (v, 0) (vi, 0) (0, 1)
    ((hp v).trans (hparallel t ht)) ((hp vi).trans (hparallelI t ht)) (hradial t ht)

end Yau.Proofs.C03Aux

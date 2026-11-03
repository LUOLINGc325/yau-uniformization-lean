import Yau.Proofs.C03SourceParallel
import Yau.Proofs.C03EnergyVariation
import Yau.LeafProofs.L23DistanceEnergyDirections
import Yau.LeafProofs.L23LocalDistanceSupportEnergyDensity

/-! The actual source-path energy is C² in the whole complex parameter.
Its first and second derivatives are genuine compact density integrals. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem euclidean_chartTarget (hn : 1 ≤ n)
    (c : (ComplexEuclideanManifold n hn).Carrier) : chartTarget c = univ := by
  change (extChartAt (ComplexModel n) (c : ComplexVector n)).target = univ
  rw [extChartAt_model_space_eq_id]
  rfl

def sourceEnergyDensity (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (Z : ℂ × ℝ → ComplexVector n) (p : ℂ × ℝ) : ℝ :=
  realMetricInChart k (0 : ComplexVector n) (Z p)
    (mapDirection Z (0, 1) p) (mapDirection Z (0, 1) p)

def sourceEnergy (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (Z : ℂ × ℝ → ComplexVector n) (a : ℂ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, sourceEnergyDensity hn k Z (a, t)

theorem sourceEnergyDensity_contDiffOn (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (S : Set (ℂ × ℝ)) (hS : IsOpen S)
    (hZ : ContDiffOn ℝ 3 Z S) :
    ContDiffOn ℝ 2 (sourceEnergyDensity hn k Z) S := by
  have hT : ContDiffOn ℝ 2 (mapDirection Z (0, 1)) S :=
    (hZ.fderiv_of_isOpen hS (by norm_num)).clm_apply contDiffOn_const
  have hG : ContDiffOn ℝ 2 (fun p => realMetricInChart k (0 : ComplexVector n) (Z p)) S :=
    ((realMetricInChart_smooth k hk (0 : ComplexVector n)).of_le (by simp)).comp
      (hZ.of_le (by norm_num)) (by
        rw [euclidean_chartTarget hn]
        exact mapsTo_univ _ _)
  exact (hG.clm_apply hT).clm_apply hT

theorem sourceEnergy_contDiffOn (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) :
    ContDiffOn ℝ 2 (sourceEnergy hn k Z) U :=
  contDiffOn_unitIntegral hU hJ hunit 2
    (sourceEnergyDensity_contDiffOn hn k hk Z _ (hU.prod hJ) hZ)

theorem sourceEnergy_eq_fieldPathEnergy (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (Z : ℂ × ℝ → ComplexVector n) (a : ℂ)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ Z (a, t)) :
    sourceEnergy hn k Z a = fieldPathEnergy k (fun t => Z (a, t)) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hder := (hZ t ht).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n)
      (fun s => Z (a, s)) t := hder.differentiableAt.mdifferentiableAt
  have hsrc : Z (a, t) ∈ (chartAt (ComplexVector n)
      (0 : (ComplexVector n))).source := by
    rw [euclidean_chartSource hn]
    trivial
  have hcd : HasDerivAt (fun s => chartPt (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n)
      (Z (a, s))) (mapDirection Z (0, 1) (a, t)) t := by
    simpa only [euclidean_chartPt, mapDirection, Function.comp_def] using hder
  simpa only [sourceEnergyDensity, euclidean_chartPt] using
    (fieldPathSpeed_sq_eq_chartDerivative k (fun s => Z (a, s)) (0 : ComplexVector n)
      t hsrc _ hmd hcd).symm

theorem sourceEnergy_firstDirection (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) {a : ℂ} (ha : a ∈ U) (v : ℂ) :
    mapDirection (sourceEnergy hn k Z) v a =
      ∫ t in Icc (0 : ℝ) 1,
        mapDirection (sourceEnergyDensity hn k Z) (v, 0) (a, t) :=
  unitIntegral_firstDirection hU hJ hunit
    ((sourceEnergyDensity_contDiffOn hn k hk Z _ (hU.prod hJ) hZ).of_le (by norm_num)) ha v

theorem sourceEnergy_secondDirection (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (Z : ℂ × ℝ → ComplexVector n) (U : Set ℂ) (J : Set ℝ)
    (hU : IsOpen U) (hJ : IsOpen J) (hunit : Icc (0 : ℝ) 1 ⊆ J)
    (hZ : ContDiffOn ℝ 3 Z (U ×ˢ J)) {a : ℂ} (ha : a ∈ U) (v w : ℂ) :
    mapDirection (mapDirection (sourceEnergy hn k Z) v) w a =
      ∫ t in Icc (0 : ℝ) 1,
        mapDirection (mapDirection (sourceEnergyDensity hn k Z) (v, 0)) (w, 0) (a, t) :=
  unitIntegral_secondDirection hU hJ hunit
    (sourceEnergyDensity_contDiffOn hn k hk Z _ (hU.prod hJ) hZ) ha v w

end Yau.Proofs.C03Aux

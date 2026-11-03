import Yau.Proofs.C03ShortLiftMapPath
import Yau.LeafProofs.L12

/-! Actual differential and length identities for the original pullback metric. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set Filter MeasureTheory
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux C07RadialCurveAux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

local instance (hn : 1 ≤ n) : NormedAddCommGroup (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedAddCommGroup (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℝ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℝ (ComplexVector n))
local instance (hn : 1 ≤ n) : NormedSpace ℂ (ComplexEuclideanManifold n hn).Carrier :=
  inferInstanceAs (NormedSpace ℂ (ComplexVector n))
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

theorem mappedCurve_velocity {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htb : t ∉ gamma.breakpoints) :
    realTangentDerivative (mappedCurve hPhi hn gamma hmem) t =
      mfderiv (ComplexModel n) (ComplexModel n) Phi (gamma t)
        (realTangentDerivative gamma t) := by
  let beta := mappedCurve hPhi hn gamma hmem
  let G : ComplexVector n → ComplexVector n := fun z => chartPt (Phi (gamma t)) (Phi z)
  let H : ℝ → ComplexVector n := fun s => chartPt (Phi (gamma t)) (beta s)
  have hG : ContDiffAt ℂ ∞ G (gamma t) :=
    (contMDiffAt_extChartAt.comp (gamma t)
      (hPhi.contMDiffAt (Metric.isOpen_ball.mem_nhds (hmem t ⟨ht.1.le, ht.2.le⟩)))).contDiffAt
  have hGD := (hG.differentiableAt (by simp)).hasFDerivAt
  have hgD := (euclidean_curve_contDiffAt hn gamma htb).differentiableAt (by norm_num)
  have hcomp := (hGD.restrictScalars ℝ).comp_hasDerivAt t hgD.hasDerivAt
  have heq : H =ᶠ[𝓝 t] G ∘ (gamma : ℝ → ComplexVector n) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    change chartPt (Phi (gamma t)) (mappedCurve hPhi hn gamma hmem s) = _
    rw [mappedCurve_on_interval hPhi hn gamma hmem ⟨hs.1.le, hs.2.le⟩]
    rfl
  have hcoord : deriv H t = fderiv ℂ G (gamma t) (deriv (gamma : ℝ → ComplexVector n) t) :=
    (hcomp.congr_of_eventuallyEq heq).deriv
  have hPhim := (hPhi.contMDiffAt
    (Metric.isOpen_ball.mem_nhds (hmem t ⟨ht.1.le, ht.2.le⟩))).mdifferentiableAt (by simp)
  have hPhiD (v : ComplexVector n) :
      mfderiv (ComplexModel n) (ComplexModel n) Phi (gamma t) v =
        fderiv ℂ G (gamma t) v := by
    unfold mfderiv
    rw [ite_eq_left hPhim]
    simp only [ModelWithCorners.range_eq_univ, fderivWithin_univ, ContinuousLinearMap.comp_apply]
    rfl
  rw [euclidean_curve_velocity hn gamma t, hPhiD]
  have hbt : beta t = Phi (gamma t) :=
    mappedCurve_on_interval hPhi hn gamma hmem ⟨ht.1.le, ht.2.le⟩
  have hid := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := Phi (gamma t))
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  change realTangentDerivative beta t = _
  unfold realTangentDerivative
  rw [hbt, hid]
  exact hcoord

theorem mappedCurve_speed_eq {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htb : t ∉ gamma.breakpoints) :
    curveSpeed k (mappedCurve hPhi hn gamma hmem) t = curveSpeed ks gamma t := by
  unfold curveSpeed
  rw [mappedCurve_on_interval hPhi hn gamma hmem ⟨ht.1.le, ht.2.le⟩,
    mappedCurve_velocity hPhi hn gamma hmem ht htb]
  unfold hermitianNormSq
  rw [heq (gamma t) (hmem t ⟨ht.1.le, ht.2.le⟩)]

theorem mappedCurve_speed_ae {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r) :
    curveSpeed k (mappedCurve hPhi hn gamma hmem) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      curveSpeed ks gamma := by
  have hbad : ∀ᵐ t : ℝ ∂volume, t ∉ gamma.breakpoints := by
    rw [ae_iff]
    simp only [not_not]
    have hset : {t : ℝ | t ∈ gamma.breakpoints} = (gamma.breakpoints : Set ℝ) := by
      ext t
      rfl
    rw [hset]
    exact gamma.breakpoints.finite_toSet.measure_zero volume
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hbad] with t ht htb
  exact mappedCurve_speed_eq hPhi hn ks k heq gamma hmem ht htb

theorem mappedCurve_length_eq {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Phi (Metric.ball 0 r))
    (hn : 1 ≤ n) (ks : HermitianField (ComplexEuclideanManifold n hn))
    (k : HermitianField M)
    (heq : ∀ z ∈ Metric.ball 0 r, ∀ u v : ComplexVector n,
      (ks z).toFun u v = (k (Phi z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Phi z v))
    {a b : ComplexVector n}
    (gamma : PiecewiseC1Curve (M := ComplexEuclideanManifold n hn) a b)
    (hmem : ∀ t ∈ Icc (0 : ℝ) 1, (gamma t : ComplexVector n) ∈ Metric.ball 0 r) :
    curveLength k (mappedCurve hPhi hn gamma hmem) = curveLength ks gamma :=
  integral_congr_ae (mappedCurve_speed_ae hPhi hn ks k heq gamma hmem)

end Yau.Proofs.C03Aux.ShortLift


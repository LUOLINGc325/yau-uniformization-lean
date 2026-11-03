import Yau.Proofs.C03ShortLiftRadial
import Yau.LeafProofs.L12

/-! The fixed target chart supplies actual smooth radial curves with the stated length bound. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix
open Set Filter
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n =>
      WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

def targetParameter (ctarget : M.Carrier) (w0 q : ComplexVector n) : M.Carrier :=
  chartInv ctarget (w0 + q)

theorem shift_ball_mem (w0 q : ComplexVector n) (delta : ℝ)
    (hq : q ∈ Metric.ball 0 delta) : w0 + q ∈ Metric.ball w0 delta := by
  simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hq

theorem radial_target_mem {w0 w : ComplexVector n} {delta t : ℝ}
    (hw : w ∈ Metric.ball w0 delta) (ht : t ∈ Icc (0 : ℝ) 1) :
    w0 + t • (w - w0) ∈ Metric.ball w0 delta := by
  apply shift_ball_mem
  apply C07RadialCurveAux.radial_point_mem
  · simpa only [Metric.mem_ball, dist_eq_norm] using hw
  · exact ht

theorem targetParameter_smooth (ctarget : M.Carrier) (w0 : ComplexVector n) (delta : ℝ)
    (hW : Metric.ball w0 delta ⊆ chartTarget ctarget) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (targetParameter ctarget w0) (Metric.ball 0 delta) := by
  have hshift : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (fun q : ComplexVector n => w0 + q) (Metric.ball 0 delta) :=
    (contDiff_const.add contDiff_id).contMDiff.contMDiffOn
  exact (contMDiffOn_extChartAt_symm (I := ComplexModel n) ctarget).comp hshift
    (fun q hq => hW (shift_ball_mem w0 q delta hq))

theorem targetParameter_mfderiv (ctarget : M.Carrier) (w0 q v : ComplexVector n)
    (hq : w0 + q ∈ chartTarget ctarget) :
    mfderiv (ComplexModel n) (ComplexModel n) (targetParameter ctarget w0) q v =
      chartVec ctarget (targetParameter ctarget w0 q) v := by
  have hi : MDifferentiableAt (ComplexModel n) (ComplexModel n) (chartInv ctarget) (w0 + q) := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := ComplexModel n) hq
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h
  have hd : HasFDerivAt (fun u : ComplexVector n => w0 + u)
      (ContinuousLinearMap.id ℂ _) q := (hasFDerivAt_id q).const_add w0
  have hs : MDifferentiableAt (ComplexModel n) (ComplexModel n)
      (fun u : ComplexVector n => w0 + u) q := hd.differentiableAt.mdifferentiableAt
  have hmf : mfderiv (ComplexModel n) (ComplexModel n)
      (fun u : ComplexVector n => w0 + u) q v = v := by
    rw [mfderiv_eq_fderiv, hd.fderiv]
    rfl
  change mfderiv (ComplexModel n) (ComplexModel n)
    ((chartInv ctarget) ∘ (fun u : ComplexVector n => w0 + u)) q v = _
  rw [mfderiv_comp q hi hs]
  change mfderiv (ComplexModel n) (ComplexModel n) (chartInv ctarget) (w0 + q)
    (mfderiv (ComplexModel n) (ComplexModel n) (fun u : ComplexVector n => w0 + u) q v) = _
  rw [hmf]
  unfold chartVec
  have hpt : chartPt ctarget (chartInv ctarget (w0 + q)) = w0 + q :=
    (extChartAt (ComplexModel n) ctarget).right_inv hq
  change _ = mfderiv (ComplexModel n) (ComplexModel n) (chartInv ctarget)
    (chartPt ctarget (chartInv ctarget (w0 + q))) v
  rw [hpt]

theorem targetParameter_real_norm (k : HermitianField M) (ctarget : M.Carrier)
    (w0 q v : ComplexVector n) (hq : w0 + q ∈ chartTarget ctarget) :
    2 * hermitianNormSq (k (targetParameter ctarget w0 q))
      (mfderiv (ComplexModel n) (ComplexModel n) (targetParameter ctarget w0) q v) =
      realMetricInChart k ctarget (w0 + q) v v := by
  rw [targetParameter_mfderiv ctarget w0 q v hq, realMetricInChart_apply,
    underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartVec ctarget (w0 + q) v hq]
  rfl

theorem targetParameter_upper (k : HermitianField M) (ctarget : M.Carrier)
    (w0 : ComplexVector n) (delta L : ℝ)
    (hW : Metric.ball w0 delta ⊆ chartTarget ctarget)
    (hG : ∀ q ∈ Metric.ball w0 delta, ∀ v : ComplexVector n,
      realMetricInChart k ctarget q v v ≤ L ^ 2 * ‖v‖ ^ 2)
    (q : ComplexVector n) (hq : q ∈ Metric.ball 0 delta) (v : ComplexVector n) :
    2 * hermitianNormSq (k (targetParameter ctarget w0 q))
      (mfderiv (ComplexModel n) (ComplexModel n) (targetParameter ctarget w0) q v) ≤
        L ^ 2 * ‖v‖ ^ 2 := by
  rw [targetParameter_real_norm k ctarget w0 q v (hW (shift_ball_mem w0 q delta hq))]
  exact hG _ (shift_ball_mem w0 q delta hq) v

end Yau.Proofs.C03Aux.ShortLift


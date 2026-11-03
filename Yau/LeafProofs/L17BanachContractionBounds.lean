import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

open Set Metric
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BanachContractionAux

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def iterationMap (e : X ≃L[ℝ] Y) (f : Y) (N : X → Y) (u : X) : X := e.symm (f+N u)

variable (e : X ≃L[ℝ] Y) (f : Y) (N : X → Y) {r L : ℝ}

theorem equation_iff_fixed (u : X) : e u=f+N u ↔ iterationMap e f N u=u := by
  constructor
  · intro h
    have he := congrArg e.symm h
    simpa only [e.symm_apply_apply,iterationMap] using he.symm
  · intro h
    have he := congrArg e h
    simpa only [iterationMap,e.apply_symm_apply] using he.symm

theorem iterationMap_sub_norm_le
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    {u v : X} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖iterationMap e f N u-iterationMap e f N v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
  have hid : (f+N u)-(f+N v)=N u-N v := by abel
  calc
    ‖iterationMap e f N u-iterationMap e f N v‖ = ‖e.symm (N u-N v)‖ := by
      rw [iterationMap,iterationMap,← map_sub,hid]
    _ ≤ ‖e.symm.toContinuousLinearMap‖*‖N u-N v‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖*(L*‖u-v‖) :=
      mul_le_mul_of_nonneg_left (hLip u v hu hv) (norm_nonneg _)
    _ = (‖e.symm.toContinuousLinearMap‖*L)*‖u-v‖ := (mul_assoc _ _ _).symm
    _ ≤ (1/2 : ℝ)*‖u-v‖ := mul_le_mul_of_nonneg_right hSmall (norm_nonneg _)

theorem iterationMap_lipschitzOn
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2) :
    LipschitzOnWith (1/2 : ℝ≥0) (iterationMap e f N) (closedBall 0 r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
    iterationMap_sub_norm_le e f N hLip hSmall
      (by simpa only [mem_closedBall,dist_zero_right] using hu)
      (by simpa only [mem_closedBall,dist_zero_right] using hv)

theorem iterationMap_norm_le (hr : 0 ≤ r)
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    {u : X} (hu : ‖u‖ ≤ r) :
    ‖iterationMap e f N u‖ ≤ (1/2 : ℝ)*‖u‖+‖e.symm (f+N 0)‖ := by
  have h := iterationMap_sub_norm_le e f N hLip hSmall hu (v := 0) (by simpa using hr)
  calc
    ‖iterationMap e f N u‖ = ‖(iterationMap e f N u-iterationMap e f N 0)+iterationMap e f N 0‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖iterationMap e f N u-iterationMap e f N 0‖+‖iterationMap e f N 0‖ := norm_add_le _ _
    _ ≤ (1/2 : ℝ)*‖u‖+‖e.symm (f+N 0)‖ := by
      simpa only [sub_zero,iterationMap] using add_le_add h (le_refl ‖iterationMap e f N 0‖)

theorem iterationMap_mapsTo (hr : 0 ≤ r)
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    (hZero : ‖e.symm (f+N 0)‖ ≤ r/2) :
    MapsTo (iterationMap e f N) (closedBall 0 r) (closedBall 0 r) := by
  intro u hu
  have hu' : ‖u‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hu
  have h := iterationMap_norm_le e f N hr hLip hSmall hu'
  have hbound : ‖iterationMap e f N u‖ ≤ r := by linarith
  simpa only [mem_closedBall,dist_zero_right] using hbound

theorem ball_equation_norm_le (hr : 0 ≤ r)
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    {u : X} (hu : ‖u‖ ≤ r) (heq : e u=f+N u) :
    ‖u‖ ≤ 2*‖e.symm (f+N 0)‖ := by
  have h := iterationMap_norm_le e f N hr hLip hSmall hu
  rw [(equation_iff_fixed e f N u).mp heq] at h
  linarith

theorem ball_equation_unique
    (hLip : ∀ u v, ‖u‖ ≤ r → ‖v‖ ≤ r → ‖N u-N v‖ ≤ L*‖u-v‖)
    (hSmall : ‖e.symm.toContinuousLinearMap‖*L ≤ 1/2)
    {u v : X} (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) (hueq : e u=f+N u) (hveq : e v=f+N v) : u=v := by
  have h := iterationMap_sub_norm_le e f N hLip hSmall hu hv
  rw [(equation_iff_fixed e f N u).mp hueq,(equation_iff_fixed e f N v).mp hveq] at h
  have hn : ‖u-v‖=0 := by have := norm_nonneg (u-v); linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Yau.LeafProofs.L17BanachContractionAux

import Yau.Proofs.F03FlowTimeEnvelope
import Yau.Proofs.F03CompactHeatError

/-! Subtracting the terminal affine potential cancels initial curvature and leaves a genuinely bounded Laplacian. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L19Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def centeredFlowPotential (X : KahlerManifold n) (U : STF X) (T : ℝ) : STF X :=
  fun x s => U x s-(s/T)*U x T

theorem centeredFlowPotential_smooth
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) :
    SmoothSpaceTime (centeredFlowPotential X U T) (Icc 0 T) := by
  have hUT := smoothSpaceTime_slice hf.2.1 hT.le
  intro a
  have hU := (hf.2.1 a).mono
    (show chartTarget a ×ˢ Icc 0 T ⊆ chartTarget a ×ˢ Ici 0 from fun p hp => ⟨hp.1,hp.2.1⟩)
  exact hU.sub ((contDiffOn_snd.div_const T).mul
    ((hUT a).comp contDiffOn_fst (fun p hp => hp.1)))

theorem centeredFlowPotential_hasDerivWithinAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (T : ℝ) (x : Pt X) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (centeredFlowPotential X U T x) (P x s-U x T/T) (Ici 0) s := by
  have hU := hf.2.2.2.2.2.2.2.1 x s hs
  have hLinear := (((hasDerivAt_id s).div_const T).mul_const (U x T)).hasDerivWithinAt (s := Ici 0)
  convert hU.sub hLinear using 1
  · funext y
    rfl
  · ring

theorem centeredFlowPotential_laplacian
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 ≤ s) (x : Pt X) :
    laplacian X.metric.form (fun y => centeredFlowPotential X U T y s) x=
      -flowMetricDefect X h s x+(s/T)*flowMetricDefect X h T x := by
  have hUs := smoothSpaceTime_slice hf.2.1 hs
  have hUT := smoothSpaceTime_slice hf.2.1 hT.le
  have hUTscale : SmoothFn (fun y => (s/T)*U y T) := fun a => contDiffOn_const.mul (hUT a)
  have hS := F02Aux.metricDefect_potential_identity X o h U P ρ hf hs x
  have hEnd := F02Aux.metricDefect_potential_identity X o h U P ρ hf hT.le x
  change flowMetricDefect X h s x=s*scalarCurvature X.metric.form x-laplacian X.metric.form (fun y => U y s) x at hS
  change flowMetricDefect X h T x=T*scalarCurvature X.metric.form x-laplacian X.metric.form (fun y => U y T) x at hEnd
  change laplacian X.metric.form (fun y => U y s-(s/T)*U y T) x=_
  rw [laplacian_sub_smooth X.metric hUs hUTscale]
  dsimp only
  rw [laplacian_const_mul X.metric.form hUT (s/T) x]
  rw [show laplacian X.metric.form (fun y => U y s) x=s*scalarCurvature X.metric.form x-flowMetricDefect X h s x by linarith,
    show laplacian X.metric.form (fun y => U y T) x=T*scalarCurvature X.metric.form x-flowMetricDefect X h T x by linarith]
  field_simp [hT.ne'] <;> ring

theorem centeredFlowPotential_laplacian_bound
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc 0 T) (x : Pt X) :
    |laplacian X.metric.form (fun y => centeredFlowPotential X U T y s) x| ≤ n := by
  rw [centeredFlowPotential_laplacian X o h U P ρ hf hT hs.1 x]
  have hS := flowMetricDefect_bounds X o h U P ρ hf hs.1 x
  have hEnd := flowMetricDefect_bounds X o h U P ρ hf hT.le x
  have hq0 : 0 ≤ s/T := div_nonneg hs.1 hT.le
  have hq1 : s/T ≤ 1 := (div_le_one hT).mpr hs.2
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hq0 hEnd.1],by nlinarith [mul_le_of_le_one_left hEnd.1 hq1]⟩

end Yau.Proofs.F03Aux

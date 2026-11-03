import Yau.Proofs.F03JointSpatialWords
import Yau.Proofs.F03KernelSmoothTransport

/-! Actual joint kernel smoothness supplies the genuine vector-valued spatial differential and its right-variable measurability. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem joint_first_product_fderiv_contDiffAt {E F B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {u : E × F → B} {p : E × F} {m : ℕ∞ω}
    (hu : ContDiffAt ℝ (m+1) u p) :
    ContDiffAt ℝ m (fun q : E × F => fderiv ℝ (fun x => u (x,q.2)) q.1) p := by
  have hF : ContDiffAt ℝ (m+1)
      (Function.uncurry (fun q : E × F => fun x : E => u (x,q.2))) (p,p.1) :=
    hu.comp (p,p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact hF.fderiv_succ contDiffAt_fst

theorem continuous_of_chartwise_continuous {B : Type*} [TopologicalSpace B]
    (f : M.Carrier → B)
    (hf : ∀ a,ContinuousOn (fun z => f (chartInv a z)) (chartTarget a)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : ContinuousAt (fun z => f (chartInv x z)) (chartPt x x) :=
    (hf x).continuousAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x))
  have hComp := hc.comp (continuousAt_extChartAt (I := ComplexModel n) x)
  apply hComp.congr
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact congrArg f ((extChartAt (ComplexModel n) x).left_inv hy)

def kernelLeftChartDifferential (H : ℝ → M.Carrier → M.Carrier → ℝ)
    (a : M.Carrier) (b : ℝ) (z : ComplexVector n) (y : M.Carrier) : ComplexVector n →L[ℝ] ℝ :=
  fderiv ℝ (fun w => H b (chartInv a w) y) z

theorem kernelLeftChartDifferential_smooth_right_chart
    (H : ℝ → M.Carrier → M.Carrier → ℝ) (hH : KernelSmoothOn univ H)
    (a c : M.Carrier) {b : ℝ} (hb : 0 < b) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    ContDiffOn ℝ ∞ (fun w => kernelLeftChartDifferential H a b z (chartInv c w)) (chartTarget c) := by
  let J : ComplexVector n × ComplexVector n → ℝ := fun p => H b (chartInv a p.1) (chartInv c p.2)
  have hPhi : ContDiff ℝ ∞ (fun p : ComplexVector n × ComplexVector n => ((p.1,p.2),b)) := by fun_prop
  have hJ : ContDiffOn ℝ ∞ J (chartTarget a ×ˢ chartTarget c) :=
    (hH a c).comp hPhi.contDiffOn (fun p hp => ⟨⟨⟨hp.1,mem_univ _⟩,⟨hp.2,mem_univ _⟩⟩,hb⟩)
  have hOpen := (isOpen_extChartAt_target (I := ComplexModel n) a).prod
    (isOpen_extChartAt_target (I := ComplexModel n) c)
  have hD : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ComplexVector n =>
      fderiv ℝ (fun v => J (v,p.2)) p.1) (chartTarget a ×ˢ chartTarget c) := by
    intro p hp
    exact (joint_first_product_fderiv_contDiffAt (m := ∞)
      (hJ.contDiffAt (hOpen.mem_nhds hp))).contDiffWithinAt
  exact hD.comp (contDiffOn_const.prodMk contDiffOn_id) (fun w hw => ⟨hz,hw⟩)

theorem kernelLeftChartDifferential_continuous_right
    (H : ℝ → M.Carrier → M.Carrier → ℝ) (hH : KernelSmoothOn univ H)
    (a : M.Carrier) {b : ℝ} (hb : 0 < b) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    Continuous (kernelLeftChartDifferential H a b z) := by
  apply continuous_of_chartwise_continuous
  intro c
  exact (kernelLeftChartDifferential_smooth_right_chart H hH a c hb hz).continuousOn

theorem kernelLeftChartDifferential_smooth_left
    (H : ℝ → M.Carrier → M.Carrier → ℝ) (hH : KernelSmoothOn univ H)
    (a : M.Carrier) {b : ℝ} (hb : 0 < b) (y : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => kernelLeftChartDifferential H a b z y) (chartTarget a) :=
  (kernelSmooth_univ_smoothFn_left H hH hb y a).fderiv_of_isOpen
    (isOpen_extChartAt_target (I := ComplexModel n) a) (by simp)

end Yau.Proofs.F03Aux

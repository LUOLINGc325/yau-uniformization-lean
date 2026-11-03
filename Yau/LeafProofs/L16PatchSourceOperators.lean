import Yau.LeafProofs.L16BoundaryChartSource
import Yau.LeafProofs.L16CompatibleHolderGraph
import Yau.LeafProofs.L16DefiningFlattening

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance patchSourceOperators_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance patchSourceOperators_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The genuine interior source cutoff is a continuous linear map from the
physical compatible graph to the full-space source graph. Only the physical
source is Holder; arbitrary values outside its domain are suppressed. -/
theorem interior_patch_source_operator {n : ℕ} {α T P : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) {ψ : Space n → ℝ}
    (hψ : HolderBound α (cylinder univ 0 T) (fun p => ψ p.1) P)
    (hSupport : tsupport ψ ⊆ closure O) :
    ∃ L : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α (univ : Set (Space n)) T,
      ‖L‖ ≤ 2*P ∧ ∀ f,
        EqOn (compatibleHolderFun (L f)) (fun p => ψ p.1*compatibleHolderFun f p)
          (cylinder univ 0 T) := by
  let E := compatibleHolderGraph α O T
  let F : E → Point n → ℝ := fun f p => ψ p.1*compatibleHolderFun f p
  have hBound (f : E) : HolderBound α (cylinder (closure (univ : Set (Space n))) 0 T)
      (F f) ((2*P)*‖f‖) := by
    have hLocal : HolderBound α (((closure O)×ˢuniv)∩cylinder univ 0 T)
        (compatibleHolderFun f) ‖f‖ :=
      holderBound_mono (compatibleHolderFun_holderBound f) (fun p hp => ⟨hp.1.1,hp.2.2⟩)
    have hZero (p : Point n) (_hp : p ∈ cylinder univ 0 T)
        (hpU : p ∉ (closure O)×ˢ(univ : Set ℝ)) : ψ p.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hpU ⟨hSupport h,mem_univ _⟩
    simpa only [closure_univ,smul_eq_mul,F] using
      holderBound_smul_cutoff_extension hψ hLocal hZero
  have hAdd (f g : E) (p : Point n) (_hp : p ∈ cylinder (closure (univ : Set (Space n))) 0 T) :
      F (f+g) p = F f p+F g p := by
    dsimp only [F]
    rw [compatibleHolderFun_add]
    simp only [Pi.add_apply,mul_add]
  have hSmul (c : ℝ) (f : E) (p : Point n)
      (_hp : p ∈ cylinder (closure (univ : Set (Space n))) 0 T) : F (c • f) p = c*F f p := by
    dsimp only [F]
    rw [compatibleHolderFun_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have hCorner (f : E) (x : Space n) (hx : x ∈ frontier (univ : Set (Space n))) : F f (x,0) = 0 := by
    simp only [frontier_univ,mem_empty_iff_false] at hx
  let L := compatibleHolderGraphLift hα hT F hBound hAdd hSmul hCorner
  refine ⟨L,compatibleHolderGraphLift_opNorm_le hα hT (by nlinarith [hψ.1])
    F hBound hAdd hSmul hCorner,?_⟩
  intro f
  simpa only [closure_univ] using
    compatibleHolderGraphLift_eqOn hα hT F hBound hAdd hSmul hCorner f

/-- A buffered actual chart and its true initial face give an actual
bounded linear pulled-source map. Its constant is fixed before time, the
physical cutoff and every source. -/
theorem boundary_patch_source_operator {n : ℕ} {O : Set (Space n)} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (e : Space n) (he : ‖e‖ = 1)
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFaces : ∀ y ∈ c.source,
      (y ∈ closure O ↔ 0 ≤ inner ℝ e (c y)) ∧
      (y ∈ frontier O ↔ inner ℝ e (c y) = 0))
    {q : ℝ} (hq : 0 < q) (hTarget : Metric.closedBall (0 : Space n) (4*q) ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T P : ℝ) (ψ : Space n → ℝ), 0 ≤ T →
      HolderBound α (cylinder univ 0 T) (fun p => ψ p.1) P →
      ∃ L : compatibleHolderGraph α O T →L[ℝ] compatibleHolderGraph α {x | 0 < inner ℝ e x} T,
        ‖L‖ ≤ C*P ∧ ∀ f,
          EqOn (compatibleHolderFun (L f))
            (fun p => innerPatchBump q hq 0 p.1*(ψ (c.symm p.1)*compatibleHolderFun f (c.symm p.1,p.2)))
            (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  obtain ⟨C,hC,hSource⟩ := boundary_chart_cutoff_source_holder hα hα1 e c hci hFaces hq hTarget
  refine ⟨2*C,by positivity,?_⟩
  intro T P ψ hT hψ
  have hP : 0 ≤ P := hψ.1
  let H : Set (Space n) := {x | 0 < inner ℝ e x}
  let E := compatibleHolderGraph α O T
  have hClosure : closure H = {x | 0 ≤ inner ℝ e x} := unitNormal_halfSpace_closure he
  have hFrontier : frontier H = {x | inner ℝ e x = 0} := unitNormal_halfSpace_frontier he
  let F : E → Point n → ℝ := fun f p =>
    innerPatchBump q hq 0 p.1*(ψ (c.symm p.1)*compatibleHolderFun f (c.symm p.1,p.2))
  have hSourceBound (f : E) := holderBound_mul
    (holderBound_mono hψ (fun p hp => ⟨mem_univ _,hp.2⟩)) (compatibleHolderFun_holderBound f)
  have hSourceCorner (f : E) (x : Space n) (hx : x ∈ frontier O) :
      ψ x*compatibleHolderFun f (x,0) = 0 := by rw [compatibleHolderFun_corner f hx,mul_zero]
  have hRaw (f : E) := hSource T (2*P*‖f‖) (fun p => ψ p.1*compatibleHolderFun f p)
    (hSourceBound f) (hSourceCorner f)
  have hBound (f : E) : HolderBound α (cylinder (closure H) 0 T) (F f) (((2*C)*P)*‖f‖) := by
    rw [hClosure]
    have h := (hRaw f).1
    have hCost : C*(2*P*‖f‖) = ((2*C)*P)*‖f‖ := by ring
    rw [hCost] at h
    exact h
  have hAdd (f g : E) (p : Point n) (_hp : p ∈ cylinder (closure H) 0 T) :
      F (f+g) p = F f p+F g p := by
    dsimp only [F]
    rw [compatibleHolderFun_add]
    simp only [Pi.add_apply,mul_add]
  have hSmul (a : ℝ) (f : E) (p : Point n) (_hp : p ∈ cylinder (closure H) 0 T) :
      F (a • f) p = a*F f p := by
    dsimp only [F]
    rw [compatibleHolderFun_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  have hCorner (f : E) (x : Space n) (hx : x ∈ frontier H) : F f (x,0) = 0 := by
    rw [hFrontier] at hx
    exact (hRaw f).2 x hx
  let L := compatibleHolderGraphLift hα hT F hBound hAdd hSmul hCorner
  refine ⟨L,compatibleHolderGraphLift_opNorm_le hα hT (by positivity)
    F hBound hAdd hSmul hCorner,?_⟩
  intro f
  simpa only [hClosure] using compatibleHolderGraphLift_eqOn hα hT F hBound hAdd hSmul hCorner f

end Yau.LeafProofs.L16Aux

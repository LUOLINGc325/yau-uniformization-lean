import Yau.LeafProofs.L17KoszulChange
import Yau.LeafProofs.L17ScalarEllipticity

/-! The genuine real metric in each original bounded-geometry chart. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

def backgroundMetric (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ℝ := by
  let : IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) (e z)) :=
    isNormableSpace_of_finiteDimensional
  let L := (mfderiv 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) e z).comp
    (tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) z).symm.toContinuousLinearMap
  exact ((L12Aux.underlyingRealRiemannianMetric g).inner (e z)).bilinearComp L L

theorem backgroundMetric_apply (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (z u v : ComplexVector n) :
    backgroundMetric g e z u v =
      (L12Aux.underlyingRealRiemannianMetric g).inner (e z)
        (realChartFrame e z u) (realChartFrame e z v) := rfl

theorem backgroundMetric_sesquilinear (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (u v : ComplexVector n) :
    backgroundMetric g e z u v =
      2 * (star (WithLp.ofLp u) ⬝ᵥ (pullbackMatrix g e z *ᵥ WithLp.ofLp v)).re := by
  rw [backgroundMetric_apply, L12Aux.underlyingRealRiemannianMetric_inner,
    realTangentEquiv_realChartFrame e he hz u,
    realTangentEquiv_realChartFrame e he hz v, pullbackMatrix_sesquilinear]

theorem scalarRealification_basis (H : Matrix (Fin n) (Fin n) ℂ) (a b : RIdx n) :
    (star (WithLp.ofLp (realVec a)) ⬝ᵥ (H *ᵥ WithLp.ofLp (realVec b))).re =
      scalarRealification H a b := by
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realVec, EuclideanSpace.single, dotProduct, Matrix.mulVec,
      scalarRealification, Pi.single_apply] <;> simp [apply_ite]

theorem backgroundMetric_basis (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) (a b : RIdx n) :
    backgroundMetric g e z (realVec a) (realVec b) =
      2 * scalarRealification (pullbackMatrix g e z) a b := by
  rw [backgroundMetric_sesquilinear g e he hz, scalarRealification_basis]

theorem backgroundMetric_symm (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (z u v : ComplexVector n) :
    backgroundMetric g e z u v = backgroundMetric g e z v u :=
  (L12Aux.underlyingRealRiemannianMetric g).symm (e z) _ _

theorem backgroundMetric_pos (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) {u : ComplexVector n} (hu : u ≠ 0) :
    0 < backgroundMetric g e z u u := by
  rw [backgroundMetric_sesquilinear g e he hz, pullbackMatrix_sesquilinear]
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  apply hermitianNormSq_pos
  intro hzero
  have hi := chart_mfderiv_injective e he hei hz
  have hu0 := hi (hzero.trans (map_zero _).symm)
  exact hu (by convert! hu0 using 1)

theorem backgroundMetric_nondegenerate (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (u : ComplexVector n)
    (hu : ∀ v, backgroundMetric g e z u v = 0) : u = 0 := by
  by_contra hne
  exact (backgroundMetric_pos g e he hei hz hne).ne' (hu u)

theorem backgroundMetric_transition (g : HermitianField M)
    (e d : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hd : MDifferentiableOn (ComplexModel n) (ComplexModel n) d d.source)
    (hdi : MDifferentiableOn (ComplexModel n) (ComplexModel n) d.symm d.target)
    {z : ComplexVector n} (hz : z ∈ transitionDomain e d) (u v : ComplexVector n) :
    backgroundMetric g e z u v =
      backgroundMetric g d (d.symm (e z))
        (fderiv ℝ (fun w => d.symm (e w)) z u)
        (fderiv ℝ (fun w => d.symm (e w)) z v) := by
  simp only [backgroundMetric_apply, transition_frame e d he hd hdi hz]
  rw [d.right_inv hz.2]

theorem BoundedChartFamily.backgroundMetric_smooth
    {g : HermitianField M} (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (backgroundMetric g (A.chart p)) (ball 0 A.radius) := by
  apply L12Aux.contDiffOn_realBilin_of_basis
  intro a b
  have hc : ContDiffOn ℝ ∞
      (fun z => 2 * scalarRealification (pullbackMatrix g (A.chart p) z) a b)
      (ball 0 A.radius) := by
    unfold scalarRealification
    split_ifs
    · exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
        (A.coefficient_smooth p a.1 b.1))
    · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
        (A.coefficient_smooth p a.1 b.1)).neg
    · exact contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn
        (A.coefficient_smooth p a.1 b.1))
  apply hc.congr
  intro z hz
  exact backgroundMetric_basis g (A.chart p) (A.differentiable p)
    (A.closedBall_source p (ball_subset_closedBall hz)) a b

end Yau.LeafProofs.L17Aux

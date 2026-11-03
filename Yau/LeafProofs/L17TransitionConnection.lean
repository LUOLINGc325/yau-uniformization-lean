import Yau.LeafProofs.L17CoordinateConnection

/-! The true second-derivative equation for original background chart transitions. -/

noncomputable section

open Set Metric Filter
open scoped Topology ContDiff Manifold Matrix

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem backgroundMetric_bilinearMatrix (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    bilinearMatrix (backgroundMetric g e z) =
      (2 : ℝ) • scalarRealification (pullbackMatrix g e z) := by
  ext a b
  exact backgroundMetric_basis g e he hz a b

theorem backgroundMetric_bilinearMatrix_isUnit (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    IsUnit (bilinearMatrix (backgroundMetric g e z)).det := by
  rw [backgroundMetric_bilinearMatrix g e he hz]
  exact isUnit_iff_ne_zero.mpr
    ((scalarRealification_posDef (pullbackMatrix_posDef g e he hei hz)).smul
      (by norm_num : (0 : ℝ) < 2)).det_pos.ne'

def backgroundConnection (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) (z : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n :=
  connectionBilinear (backgroundMetric g e z) (fderiv ℝ (backgroundMetric g e) z)

theorem backgroundConnection_koszul (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (u v w : ComplexVector n) :
    backgroundMetric g e z (backgroundConnection g e z u v) w =
      ((fderiv ℝ (backgroundMetric g e) z u) v w +
        (fderiv ℝ (backgroundMetric g e) z v) u w -
        (fderiv ℝ (backgroundMetric g e) z w) u v) / 2 :=
  connectionBilinear_koszul _ _ (backgroundMetric_symm g e z)
    (backgroundMetric_bilinearMatrix_isUnit g e he hei hz) u v w

theorem BoundedChartFamily.transition_secondDerivative
    {g : HermitianField M} (A : BoundedChartFamily g) (p q : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ ball 0 A.radius)
    (hq : A.chart p z ∈ A.chart q '' ball 0 A.radius) (u v : ComplexVector n) :
    fderiv ℝ (fun w => (A.chart q).symm (A.chart p w)) z
        (backgroundConnection g (A.chart p) z u v) =
      (fderiv ℝ (fderiv ℝ (fun w => (A.chart q).symm (A.chart p w))) z u) v +
        backgroundConnection g (A.chart q) ((A.chart q).symm (A.chart p z))
          (fderiv ℝ (fun w => (A.chart q).symm (A.chart p w)) z u)
          (fderiv ℝ (fun w => (A.chart q).symm (A.chart p w)) z v) := by
  let e := A.chart p
  let d := A.chart q
  let T : ComplexVector n → ComplexVector n := fun w => d.symm (e w)
  have hzs : z ∈ e.source := A.closedBall_source p (ball_subset_closedBall hz)
  have hTz : T z ∈ ball 0 A.radius := by
    obtain ⟨w, hw, hweq⟩ := hq
    change d.symm (e z) ∈ ball 0 A.radius
    rw [← hweq, d.left_inv (A.closedBall_source q (ball_subset_closedBall hw))]
    exact hw
  have hzq : e z ∈ d.target := by
    obtain ⟨w, hw, hweq⟩ := hq
    rw [← hweq]
    exact d.map_source (A.closedBall_source q (ball_subset_closedBall hw))
  have hdom : z ∈ transitionDomain e d := ⟨hzs, hzq⟩
  have hU := (transitionDomain_isOpen e d).mem_nhds hdom
  have hTs : ContDiffAt ℝ ∞ T z :=
    (transition_real_contDiffOn e d (A.differentiable p)
      (A.inverse_differentiable q)).contDiffAt hU
  have hTd : DifferentiableAt ℝ T z := hTs.differentiableAt (by simp)
  have hTD : DifferentiableAt ℝ (fderiv ℝ T) z :=
    (hTs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hB₁ : DifferentiableAt ℝ (backgroundMetric g e) z :=
    ((A.backgroundMetric_smooth p).contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt
      (by simp)
  have hB₂ : DifferentiableAt ℝ (backgroundMetric g d) (T z) :=
    ((A.backgroundMetric_smooth q).contDiffAt (isOpen_ball.mem_nhds hTz)).differentiableAt
      (by simp)
  refine koszul_coordinate_change
    (backgroundMetric g e z) (backgroundMetric g d (T z))
    (fderiv ℝ (backgroundMetric g e) z) (fderiv ℝ (backgroundMetric g d) (T z))
    (backgroundConnection g e z) (backgroundConnection g d (T z))
    (fderiv ℝ T z) (fderiv ℝ (fderiv ℝ T) z)
    (backgroundMetric_symm g d (T z))
    (backgroundMetric_nondegenerate g d (A.differentiable q) (A.inverse_differentiable q)
      (d.map_target hzq))
    (transition_fderiv_surjective e d (A.differentiable p) (A.inverse_differentiable p)
      (A.differentiable q) (A.inverse_differentiable q) hdom)
    (hTs.isSymmSndFDerivAt (by simp))
    (backgroundMetric_transition g e d (A.differentiable p) (A.differentiable q)
      (A.inverse_differentiable q) hdom)
    ?_
    (backgroundConnection_koszul g e (A.differentiable p) (A.inverse_differentiable p) hzs)
    (backgroundConnection_koszul g d (A.differentiable q) (A.inverse_differentiable q)
      (d.map_target hzq)) u v
  intro a b c
  have heq : (fun w => backgroundMetric g e w b c) =ᶠ[𝓝 z]
      (fun w => backgroundMetric g d (T w) (fderiv ℝ T w b) (fderiv ℝ T w c)) := by
    filter_upwards [hU] with w hw
    exact backgroundMetric_transition g e d (A.differentiable p) (A.differentiable q)
      (A.inverse_differentiable q) hw b c
  rw [← L12Aux.fderiv_bilin_apply_const hB₁ a b c, heq.fderiv_eq]
  exact fderiv_bilinear_pullback hB₂ hTd hTD a b c

end Yau.LeafProofs.L17Aux

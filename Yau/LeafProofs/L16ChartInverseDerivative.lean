import Yau.LeafProofs.L16NonlinearChartCalculus

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartInverseDerivative_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_thirdGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_thirdSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartInverseDerivative_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartInverseDerivative_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- Both inverse-Jacobian identities follow from the genuine local inverse
    identities and the actual first derivative chain rule. -/
theorem openPartialHomeomorph_derivative_inverse {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {y : Space n} (hy : y ∈ c.target) :
    (fderiv ℝ c.symm y).comp (fderiv ℝ c (c.symm y)) = ContinuousLinearMap.id ℝ (Space n) ∧
      (fderiv ℝ c (c.symm y)).comp (fderiv ℝ c.symm y) = ContinuousLinearMap.id ℝ (Space n) := by
  have hx := c.map_target hy
  have hcD := (hc.contDiffAt (c.open_source.mem_nhds hx)).differentiableAt (by norm_num)
  have hciD := (hci.contDiffAt (c.open_target.mem_nhds hy)).differentiableAt (by norm_num)
  have hLeft : (fun z => c.symm (c z)) =ᶠ[𝓝 (c.symm y)] id := c.eventually_left_inverse hx
  have hRight : (fun z => c (c.symm z)) =ᶠ[𝓝 y] id := c.eventually_right_inverse hy
  constructor
  · have hciDx : DifferentiableAt ℝ c.symm (c (c.symm y)) := by simpa only [c.right_inv hy] using hciD
    have hh := fderiv_fun_comp (c.symm y) hciDx hcD
    rw [c.right_inv hy] at hh
    simpa only [fderiv_id] using hh.symm.trans hLeft.fderiv_eq
  · have hh := fderiv_fun_comp y hcD hciD
    simpa only [fderiv_id] using hh.symm.trans hRight.fderiv_eq

/-- The original covector is recovered from its actual chart pullback by the
    genuine inverse Jacobian, with no linear-algebra assumption added. -/
theorem spatialD_chart_recover {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {y : Space n} (hy : y ∈ c.target) {u : Point n → ℝ} (t : ℝ)
    (hu : DifferentiableAt ℝ (fun x => u (x,t)) (c.symm y)) :
    spatialD u (c.symm y,t) =
      (spatialD (chartSpaceTimePullback c.symm u) (y,t)).comp (fderiv ℝ c (c.symm y)) := by
  have hciD := (hci.contDiffAt (c.open_target.mem_nhds hy)).differentiableAt (by norm_num)
  rw [spatialD_chartSpaceTimePullback (y,t) hciD hu,ContinuousLinearMap.comp_assoc,
    (openPartialHomeomorph_derivative_inverse c hc hci hy).1,ContinuousLinearMap.comp_id]

/-- The derivative of the inverse-Jacobian field is the actual second chart
    derivative composed with the actual inverse derivative. -/
theorem fderiv_chart_inverse_jacobian {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {y : Space n} (hy : y ∈ c.target) :
    fderiv ℝ (fun z => fderiv ℝ c (c.symm z)) y =
      (fderiv ℝ (fderiv ℝ c) (c.symm y)).comp (fderiv ℝ c.symm y) := by
  have hcAt := hc.contDiffAt (c.open_source.mem_nhds (c.map_target hy))
  have hciAt := hci.contDiffAt (c.open_target.mem_nhds hy)
  exact fderiv_fun_comp y ((hcAt.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
    (hciAt.differentiableAt (by norm_num))

/-- Compact convex chart buffers give a genuine bounded Lipschitz inverse
    Jacobian field, with constants selected before any boundary data. -/
theorem compact_chart_inverse_jacobian_bound {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {K : Set (Space n)} (hK : IsCompact K) (hConv : Convex ℝ K) (hKT : K ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧ (∀ y ∈ K, ‖fderiv ℝ c (c.symm y)‖ ≤ C) ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ c (c.symm x)-fderiv ℝ c (c.symm y)‖ ≤ C*‖x-y‖ := by
  have hImage : IsCompact (c.symm '' K) := hK.image_of_continuousOn (hci.continuousOn.mono hKT)
  have hImageSource : c.symm '' K ⊆ c.source := by
    rintro z ⟨y,hy,rfl⟩
    exact c.map_target (hKT hy)
  obtain ⟨A,hA,hABound⟩ := compact_actual_three_jet_bound c.open_source hImage hImageSource hc
  obtain ⟨B,hB,hBBound⟩ := compact_actual_three_jet_bound c.open_target hK hKT hci
  have hD (y : Space n) (hy : y ∈ K) : DifferentiableAt ℝ (fun z => fderiv ℝ c (c.symm z)) y :=
    (((hc.contDiffAt (c.open_source.mem_nhds (c.map_target (hKT hy)))).fderiv_right
      (m := 2) (by norm_num)).differentiableAt (by norm_num)).comp y
      ((hci.contDiffAt (c.open_target.mem_nhds (hKT hy))).differentiableAt (by norm_num))
  have hDerivBound (y : Space n) (hy : y ∈ K) :
      ‖fderiv ℝ (fun z => fderiv ℝ c (c.symm z)) y‖ ≤ A*B := by
    rw [fderiv_chart_inverse_jacobian c hc hci (hKT hy)]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hABound _ ⟨y,hy,rfl⟩).2.1 (hBBound y hy).1 (norm_nonneg _) hA.le)
  refine ⟨A+A*B,by positivity,?_,?_⟩
  · intro y hy
    exact (hABound _ ⟨y,hy,rfl⟩).1.trans (by nlinarith)
  · intro x hx y hy
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hD hDerivBound hConv hy hx
    exact hh.trans (mul_le_mul_of_nonneg_right (by nlinarith : A*B ≤ A+A*B) (norm_nonneg _))

end Yau.LeafProofs.L16Aux

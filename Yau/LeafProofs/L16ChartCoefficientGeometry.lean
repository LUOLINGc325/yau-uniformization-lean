import Yau.LeafProofs.L16ChartLowJetTransport

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartCoefficientGeometry_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientGeometry_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientGeometry_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientGeometry_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientGeometry_thirdGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartCoefficientGeometry_thirdSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance

/-- The actual first and second chart jets at inverse points are Holder
    fields on every buffered model cylinder. All budgets are geometric. -/
theorem compact_chart_coefficient_geometry_holder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {K : Set (Space n)} (hK : IsCompact K) (hConv : Convex ℝ K) (hKT : K ⊆ c.target) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x ∈ K, ∀ y ∈ K, ‖c.symm x-c.symm y‖ ≤ C*‖x-y‖) ∧
      ∀ T : ℝ,
        HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ c (c.symm p.1)) C ∧
        HolderBound α (cylinder K 0 T) (fun p => fderiv ℝ (fderiv ℝ c) (c.symm p.1)) C := by
  have hImage : IsCompact (c.symm '' K) := hK.image_of_continuousOn (hci.continuousOn.mono hKT)
  have hImageSource : c.symm '' K ⊆ c.source := by
    rintro z ⟨y,hy,rfl⟩
    exact c.map_target (hKT hy)
  obtain ⟨A,hA,hABound⟩ := compact_actual_three_jet_bound c.open_source hImage hImageSource hc
  obtain ⟨B,hB,hBBound⟩ := compact_actual_three_jet_bound c.open_target hK hKT hci
  obtain ⟨E,hE,hENorm,hELip⟩ := compact_chart_inverse_jacobian_bound c hc hci hK hConv hKT
  have hD (y : Space n) (hy : y ∈ K) :
      DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ c) (c.symm z)) y :=
    ((((hc.contDiffAt (c.open_source.mem_nhds (c.map_target (hKT hy)))).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).comp y
      ((hci.contDiffAt (c.open_target.mem_nhds (hKT hy))).differentiableAt (by norm_num))
  have hDeriv (y : Space n) (hy : y ∈ K) :
      ‖fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ c) (c.symm z)) y‖ ≤ A*B := by
    rw [fderiv_fun_comp y
      (((((hc.contDiffAt (c.open_source.mem_nhds (c.map_target (hKT hy)))).fderiv_right
        (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      ((hci.contDiffAt (c.open_target.mem_nhds (hKT hy))).differentiableAt (by norm_num))]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hABound _ ⟨y,hy,rfl⟩).2.2 (hBBound y hy).1 (norm_nonneg _) hA.le)
  let D : ℝ := A+A*B
  have hD0 : 0 < D := by dsimp only [D]; positivity
  have hDDNorm : ∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ c) (c.symm y)‖ ≤ D := by
    intro y hy
    exact (hABound _ ⟨y,hy,rfl⟩).2.1.trans (by dsimp only [D]; nlinarith)
  have hDDLip : ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (fderiv ℝ c) (c.symm x)-fderiv ℝ (fderiv ℝ c) (c.symm y)‖ ≤ D*‖x-y‖ := by
    intro x hx y hy
    exact (Convex.norm_image_sub_le_of_norm_fderiv_le hD hDeriv hConv hy hx).trans
      (mul_le_mul_of_nonneg_right (by dsimp only [D]; nlinarith : A*B ≤ D) (norm_nonneg _))
  let C : ℝ := 2*E+2*D+B
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_,?_⟩
  · intro x hx y hy
    exact (chart_actual_two_jet_lipschitz c.open_target hConv hKT hci hBBound hx hy).1.trans
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith : B ≤ C) (norm_nonneg _))
  · intro T
    exact ⟨holderBound_mono_const (holderBound_spatial_lipschitz_field hα hα1 hE.le hENorm hELip)
        (by dsimp only [C]; linarith),
      holderBound_mono_const (holderBound_spatial_lipschitz_field hα hα1 hD0.le hDDNorm hDDLip)
        (by dsimp only [C]; linarith)⟩

end Yau.LeafProofs.L16Aux

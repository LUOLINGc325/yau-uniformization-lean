import Yau.LeafProofs.L16ChartOperatorAlgebra
import Yau.LeafProofs.L16ChartInverseDerivative

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartEllipticity_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartEllipticity_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartEllipticity_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartEllipticity_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

theorem chartPrincipalMatrix_isSymm {n : ℕ} (L : Space n →L[ℝ] Space n)
    {A : Mat n} (hA : A.IsSymm) : (chartPrincipalMatrix L A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro k l
  dsimp only [chartPrincipalMatrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply i j]
  ring

theorem chartPrincipalMatrix_quadratic {n : ℕ} (L : Space n →L[ℝ] Space n)
    (A : Mat n) (x : Space n) :
    (∑ k : Yau.RIdx n, ∑ l : Yau.RIdx n,
      chartPrincipalMatrix L A k l*Yau.realCoord x k*Yau.realCoord x l) =
    ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      A i j*Yau.realCoord (ContinuousLinearMap.adjoint L x) i*
        Yau.realCoord (ContinuousLinearMap.adjoint L x) j := by
  let D : Space n →L[ℝ] ℝ := innerSL ℝ x
  have h := chartPrincipalMatrix_contraction L A (D.smulRight D)
  have hD (i : Yau.RIdx n) : inner ℝ x (L (Yau.realVec i)) =
      Yau.realCoord (ContinuousLinearMap.adjoint L x) i := by
    rw [← ContinuousLinearMap.adjoint_inner_left L (Yau.realVec i) x,real_inner_realVec]
  simpa only [ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul,
    D,innerSL_apply_apply,real_inner_realVec,hD,mul_assoc] using h

theorem realCoord_realVec_sum {n : ℕ} (v : Yau.RIdx n → ℝ) (k : Yau.RIdx n) :
    Yau.realCoord (∑ i : Yau.RIdx n, v i • Yau.realVec i) k = v k := by
  rw [← realCoordLinear_apply]
  simp only [map_sum,map_smul,smul_eq_mul,realCoordLinear_apply,
    ← real_inner_realVec,realVec_inner]
  simp

/-- Both ellipticity constants follow from actual Jacobian/inverse-Jacobian
    norm bounds; no chart-ellipticity premise is introduced. -/
theorem chartPrincipalMatrix_elliptic_bounds {n : ℕ}
    (L K : Space n →L[ℝ] Space n) (hLK : L.comp K = ContinuousLinearMap.id ℝ (Space n))
    {A : Mat n} {lam upper C : ℝ} (hLam : 0 < lam) (hLamUpper : lam ≤ upper)
    (hC : 1 ≤ C) (hL : ‖L‖ ≤ C) (hK : ‖K‖ ≤ C)
    (hA : ∀ v : Yau.RIdx n → ℝ,
      lam*(∑ i, (v i)^2) ≤ ∑ i, ∑ j, A i j*v i*v j ∧
        (∑ i, ∑ j, A i j*v i*v j) ≤ upper*(∑ i, (v i)^2)) :
    ∀ v : Yau.RIdx n → ℝ,
      (lam/C^2)*(∑ i, (v i)^2) ≤ ∑ i, ∑ j, chartPrincipalMatrix L A i j*v i*v j ∧
        (∑ i, ∑ j, chartPrincipalMatrix L A i j*v i*v j) ≤ (upper*C^2)*(∑ i, (v i)^2) := by
  intro v
  let x : Space n := ∑ i : Yau.RIdx n, v i • Yau.realVec i
  have hx (i) : Yau.realCoord x i = v i := realCoord_realVec_sum v i
  have hxNorm : (∑ i : Yau.RIdx n, (v i)^2) = ‖x‖^2 := by
    simpa only [hx] using sum_realCoord_sq x
  have hC0 : 0 < C := by linarith
  have hAdj : (ContinuousLinearMap.adjoint K).comp (ContinuousLinearMap.adjoint L) =
      ContinuousLinearMap.id ℝ (Space n) := by
    rw [← ContinuousLinearMap.adjoint_comp,hLK,ContinuousLinearMap.adjoint_id]
  have hU : ‖ContinuousLinearMap.adjoint L x‖ ≤ C*‖x‖ :=
    ((ContinuousLinearMap.adjoint L).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (by simpa only [LinearIsometryEquiv.norm_map] using hL) (norm_nonneg _))
  have hLower : ‖x‖ ≤ C*‖ContinuousLinearMap.adjoint L x‖ := by
    have hh := (ContinuousLinearMap.adjoint K).le_opNorm (ContinuousLinearMap.adjoint L x)
    have he := congrArg (fun F : Space n →L[ℝ] Space n => F x) hAdj
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at he
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by simpa only [LinearIsometryEquiv.norm_map] using hK) (norm_nonneg _))
  have hUpperSq : ‖ContinuousLinearMap.adjoint L x‖^2 ≤ C^2*‖x‖^2 := by
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint L x),norm_nonneg x]
  have hLowerSq : ‖x‖^2 ≤ C^2*‖ContinuousLinearMap.adjoint L x‖^2 := by
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint L x),norm_nonneg x]
  have hForm := hA (Yau.realCoord (ContinuousLinearMap.adjoint L x))
  simp only [sum_realCoord_sq] at hForm
  rw [← chartPrincipalMatrix_quadratic L A x] at hForm
  simp only [hx] at hForm
  rw [hxNorm]
  constructor
  · calc
      (lam/C^2)*‖x‖^2 ≤ (lam/C^2)*(C^2*‖ContinuousLinearMap.adjoint L x‖^2) :=
        mul_le_mul_of_nonneg_left hLowerSq (by positivity)
      _ = lam*‖ContinuousLinearMap.adjoint L x‖^2 := by field_simp
      _ ≤ _ := hForm.1
  · exact hForm.2.trans (by nlinarith [hLam.trans_le hLamUpper])

/-- The literal transformed coefficient field is uniformly elliptic on an
    actual model cylinder, with its two Jacobian bounds explicitly accounted for. -/
theorem chartTransformedPrincipal_elliptic {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {S X : Set (Space n)} {T lam upper C : ℝ} (hST : S ⊆ c.target)
    (hMap : MapsTo c.symm S X) (hC : 1 ≤ C)
    (hBounds : ∀ y ∈ S, ‖fderiv ℝ c (c.symm y)‖ ≤ C ∧ ‖fderiv ℝ c.symm y‖ ≤ C)
    {a : Point n → Mat n} (ha : Elliptic (cylinder X 0 T) a lam upper) :
    Elliptic (cylinder S 0 T) (chartTransformedPrincipal c a) (lam/C^2) (upper*C^2) := by
  have hC0 : 0 < C := by linarith
  have hC2 : 1 ≤ C^2 := by nlinarith
  have hUpper0 : 0 ≤ upper := (ha.1.trans_le ha.2.1).le
  refine ⟨div_pos ha.1 (sq_pos_of_pos hC0),?_,?_⟩
  · calc
      lam/C^2 ≤ lam := (div_le_iff₀ (sq_pos_of_pos hC0)).mpr (by nlinarith [ha.1])
      _ ≤ upper := ha.2.1
      _ ≤ upper*C^2 := by nlinarith
  · intro p hp
    have hOrig := ha.2.2 (c.symm p.1,p.2) ⟨hMap hp.1,hp.2⟩
    refine ⟨chartPrincipalMatrix_isSymm _ hOrig.1,?_⟩
    exact chartPrincipalMatrix_elliptic_bounds _ _
      (openPartialHomeomorph_derivative_inverse c hc hci (hST hp.1)).2
      ha.1 ha.2.1 hC (hBounds p.1 hp.1).1 (hBounds p.1 hp.1).2 hOrig.2

/-- Compact buffered smooth charts fix their ellipticity loss before any
    coefficient field is chosen. No transformed ellipticity is assumed. -/
theorem compact_chart_ellipticity_budget {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    {K : Set (Space n)} (hK : IsCompact K) (hConv : Convex ℝ K) (hKT : K ⊆ c.target) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S X : Set (Space n)) (T lam upper : ℝ) (a : Point n → Mat n),
      S ⊆ K → MapsTo c.symm S X → Elliptic (cylinder X 0 T) a lam upper →
      Elliptic (cylinder S 0 T) (chartTransformedPrincipal c a) (lam/C^2) (upper*C^2) := by
  obtain ⟨A,hA,hABound,hALip⟩ := compact_chart_inverse_jacobian_bound c hc hci hK hConv hKT
  obtain ⟨B,hB,hBBound⟩ := compact_actual_three_jet_bound c.open_target hK hKT hci
  let C : ℝ := 1+A+B
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro S X T lam upper a hSK hMap ha
  apply chartTransformedPrincipal_elliptic c hc hci (hSK.trans hKT) hMap hC _ ha
  intro y hy
  exact ⟨(hABound y (hSK hy)).trans (by dsimp only [C]; linarith),
    (hBBound y (hSK hy)).1.trans (by dsimp only [C]; linarith)⟩

end Yau.LeafProofs.L16Aux

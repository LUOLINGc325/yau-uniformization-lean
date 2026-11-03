import Yau.LeafProofs.L16NonlinearChartCalculus

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance chartOperator_firstGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance chartOperator_firstSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance chartOperator_secondGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartOperator_secondSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance chartOperator_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance chartOperator_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance chartOperator_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance chartOperator_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Expansion in the actual real orthonormal frame of complex coordinate space. -/
theorem realVec_coordinate_expansion {n : ℕ} (x : Space n) :
    (∑ i : Yau.RIdx n, Yau.realCoord x i • Yau.realVec i) = x := by
  simpa only [spaceRealBasis_apply,real_inner_comm,real_inner_realVec] using
    (spaceRealBasis n).sum_repr' x

theorem realCovector_coordinate_expansion {n : ℕ} (L : Space n →L[ℝ] ℝ) (x : Space n) :
    L x = ∑ i : Yau.RIdx n, Yau.realCoord x i*L (Yau.realVec i) := by
  nth_rw 1 [← realVec_coordinate_expansion x]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem realBilinear_coordinate_expansion {n : ℕ}
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) (x y : Space n) :
    H x y = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
      Yau.realCoord x i*Yau.realCoord y j*H (Yau.realVec i) (Yau.realVec j) := by
  nth_rw 1 [← realVec_coordinate_expansion x]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [realCovector_coordinate_expansion (H (Yau.realVec i)) y,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual principal matrix after a nonlinear spatial coordinate change. -/
def chartPrincipalMatrix {n : ℕ} (L : Space n →L[ℝ] Space n) (A : Mat n) : Mat n :=
  fun k l => ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n,
    A i j*Yau.realCoord (L (Yau.realVec i)) k*Yau.realCoord (L (Yau.realVec j)) l

/-- The transformed drift retains the actual second derivative of the chart. -/
def chartDriftVector {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Mat n) (b : Yau.RIdx n → ℝ) :
    Yau.RIdx n → ℝ := fun k =>
  (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*Yau.realCoord (B (Yau.realVec i) (Yau.realVec j)) k)+
  ∑ i : Yau.RIdx n, b i*Yau.realCoord (L (Yau.realVec i)) k

theorem chartPrincipalMatrix_contraction {n : ℕ} (L : Space n →L[ℝ] Space n) (A : Mat n)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) :
    (∑ k : Yau.RIdx n, ∑ l : Yau.RIdx n,
      chartPrincipalMatrix L A k l*H (Yau.realVec k) (Yau.realVec l)) =
    ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (L (Yau.realVec i)) (L (Yau.realVec j)) := by
  simp only [chartPrincipalMatrix,Finset.sum_mul]
  calc
    _ = ∑ k : Yau.RIdx n, ∑ i : Yau.RIdx n, ∑ l : Yau.RIdx n, ∑ j : Yau.RIdx n,
      A i j*Yau.realCoord (L (Yau.realVec i)) k*Yau.realCoord (L (Yau.realVec j)) l*
        H (Yau.realVec k) (Yau.realVec l) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = ∑ i : Yau.RIdx n, ∑ k : Yau.RIdx n, ∑ l : Yau.RIdx n, ∑ j : Yau.RIdx n,
      A i j*Yau.realCoord (L (Yau.realVec i)) k*Yau.realCoord (L (Yau.realVec j)) l*
        H (Yau.realVec k) (Yau.realVec l) := Finset.sum_comm
    _ = ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, ∑ k : Yau.RIdx n, ∑ l : Yau.RIdx n,
      A i j*Yau.realCoord (L (Yau.realVec i)) k*Yau.realCoord (L (Yau.realVec j)) l*
        H (Yau.realVec k) (Yau.realVec l) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ k : Yau.RIdx n, ∑ j : Yau.RIdx n, ∑ l : Yau.RIdx n,
          A i j*Yau.realCoord (L (Yau.realVec i)) k*Yau.realCoord (L (Yau.realVec j)) l*
            H (Yau.realVec k) (Yau.realVec l) := by
          apply Finset.sum_congr rfl
          intro k _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [realBilinear_coordinate_expansion H (L (Yau.realVec i)) (L (Yau.realVec j)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

theorem chartDriftVector_eq_coords {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Mat n) (b : Yau.RIdx n → ℝ)
    (k : Yau.RIdx n) :
    chartDriftVector L B A b k = Yau.realCoord
      ((∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j • B (Yau.realVec i) (Yau.realVec j))+
        ∑ i : Yau.RIdx n, b i • L (Yau.realVec i)) k := by
  rw [← realCoordLinear_apply]
  simp only [map_add,map_sum,map_smul,smul_eq_mul,realCoordLinear_apply,chartDriftVector]

theorem chartDriftVector_contraction {n : ℕ} (L : Space n →L[ℝ] Space n)
    (B : Space n →L[ℝ] Space n →L[ℝ] Space n) (A : Mat n) (b : Yau.RIdx n → ℝ)
    (D : Space n →L[ℝ] ℝ) :
    (∑ k : Yau.RIdx n, chartDriftVector L B A b k*D (Yau.realVec k)) =
      (∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*D (B (Yau.realVec i) (Yau.realVec j)))+
        ∑ i : Yau.RIdx n, b i*D (L (Yau.realVec i)) := by
  simp_rw [chartDriftVector_eq_coords]
  rw [← realCovector_coordinate_expansion D]
  simp only [map_add,map_sum,map_smul,smul_eq_mul]

/-- Pointwise operator transport by an actual nonlinear spatial map. Its
    curvature is included in the transformed first-order coefficient. -/
theorem linearOp_chartSpaceTimePullback {n : ℕ} {S X : Set (Space n)} {T : ℝ}
    {ψ : Space n → Space n} {u : Point n → ℝ} (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) {p : Point n} (hp : p.1 ∈ X) (hψp : ψ p.1 ∈ S)
    (hψ : ContDiffAt ℝ 2 ψ p.1)
    (hu : ContDiffAt ℝ 2 (fun x => u (x,p.2)) (ψ p.1)) :
    linearOp (cylinder X 0 T) a b (chartSpaceTimePullback ψ u) p =
      linearOp (cylinder S 0 T)
        (fun _ => chartPrincipalMatrix (fderiv ℝ ψ p.1) (a p))
        (fun _ => chartDriftVector (fderiv ℝ ψ p.1)
          (fderiv ℝ (fderiv ℝ ψ) p.1) (a p) (b p)) u (ψ p.1,p.2) := by
  simp only [linearOp]
  rw [timeD_chartSpaceTimePullback ψ u hp hψp,
    spatialDD_chartSpaceTimePullback p hψ hu,
    spatialD_chartSpaceTimePullback p (hψ.differentiableAt (by norm_num))
      (hu.differentiableAt (by norm_num)),chartPrincipalMatrix_contraction,chartDriftVector_contraction]
  simp only [chartSecondJet_apply,ContinuousLinearMap.comp_apply,mul_add,Finset.sum_add_distrib]
  ring

/-- Actual model coefficients, evaluated at the inverse chart point. -/
def chartTransformedPrincipal {n : ℕ} (c : OpenPartialHomeomorph (Space n) (Space n))
    (a : Point n → Mat n) (p : Point n) : Mat n :=
  chartPrincipalMatrix (fderiv ℝ c (c.symm p.1)) (a (c.symm p.1,p.2))

def chartTransformedDrift {n : ℕ} (c : OpenPartialHomeomorph (Space n) (Space n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (p : Point n) : Yau.RIdx n → ℝ :=
  chartDriftVector (fderiv ℝ c (c.symm p.1)) (fderiv ℝ (fderiv ℝ c) (c.symm p.1))
    (a (c.symm p.1,p.2)) (b (c.symm p.1,p.2))

theorem linearOp_actual_chart_coefficients {n : ℕ} {S X : Set (Space n)} {T : ℝ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) {u : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) {p : Point n}
    (hp : p.1 ∈ X) (hc : p.1 ∈ c.source) (hψp : c p.1 ∈ S)
    (hChart : ContDiffAt ℝ 2 c p.1)
    (hu : ContDiffAt ℝ 2 (fun x => u (x,p.2)) (c p.1)) :
    linearOp (cylinder X 0 T) a b (chartSpaceTimePullback c u) p =
      linearOp (cylinder S 0 T) (chartTransformedPrincipal c a)
        (chartTransformedDrift c a b) u (c p.1,p.2) := by
  rw [linearOp_chartSpaceTimePullback a b hp hψp hChart hu]
  simp only [linearOp,chartTransformedPrincipal,chartTransformedDrift,c.left_inv hc,Prod.eta]

end Yau.LeafProofs.L16Aux

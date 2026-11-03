import Yau.LeafProofs.L17LocalScalarAssemblyBounds

open Set Metric
open scoped Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalScalarAssemblyAux
open L17Aux L17HolderAux L17SchauderAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scalarAssemblyTerm_zero_of_not_cover (P : UniformChartPartition g) {T γ : ℝ}
    (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : Cylinder M T)
    (hq : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius) : scalarAssemblyTerm P u p q=0 := by
  rw [← rawLocalizedTerm_weighted_eq]
  exact rawLocalizedTerm_zero_of_not_cover P T p _ q hq

theorem scalarAssemblyTerm_add (P : UniformChartPartition g) {T γ : ℝ}
    (u v : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : Cylinder M T) :
    scalarAssemblyTerm P (u+v) p q=scalarAssemblyTerm P u p q+scalarAssemblyTerm P v p q := by
  unfold scalarAssemblyTerm
  split_ifs with hx hz
  · change _*(localFun ℝ u _+localFun ℝ v _)=_ * localFun ℝ u _+_ * localFun ℝ v _
    ring
  · simp
  · simp

theorem scalarAssemblyTerm_smul (P : UniformChartPartition g) {T γ : ℝ}
    (c : ℝ) (u : LocalHolderSpace ℝ P T γ) (p : P.centers) (q : Cylinder M T) :
    scalarAssemblyTerm P (c • u) p q=c • scalarAssemblyTerm P u p q := by
  unfold scalarAssemblyTerm
  split_ifs with hx hz
  · change _*(c*localFun ℝ u _)=c*(_ * localFun ℝ u _)
    ring
  · simp
  · simp

theorem scalarAssemblyFunction_add (P : UniformChartPartition g) {T γ : ℝ}
    (u v : LocalHolderSpace ℝ P T γ) :
    scalarAssemblyFunction P (u+v)=scalarAssemblyFunction P u+scalarAssemblyFunction P v := by
  funext q
  have h := supported_finsum_add P T (scalarAssemblyTerm P u) (scalarAssemblyTerm P v)
    (scalarAssemblyTerm_zero_of_not_cover P u) (scalarAssemblyTerm_zero_of_not_cover P v) q
  simpa only [scalarAssemblyFunction,scalarAssemblyTerm_add,Pi.add_apply] using h

theorem scalarAssemblyFunction_smul (P : UniformChartPartition g) {T γ : ℝ}
    (c : ℝ) (u : LocalHolderSpace ℝ P T γ) :
    scalarAssemblyFunction P (c • u)=c • scalarAssemblyFunction P u := by
  funext q
  have h := supported_finsum_smul P T (scalarAssemblyTerm P u) c
    (scalarAssemblyTerm_zero_of_not_cover P u) q
  simpa only [scalarAssemblyFunction,scalarAssemblyTerm_smul,Pi.smul_apply] using h

end Yau.LeafProofs.L17LocalScalarAssemblyAux

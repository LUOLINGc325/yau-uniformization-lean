import Yau.LeafProofs.L17BootstrapPatchHomeomorph
import Yau.LeafProofs.L17LocalScalarAssembly
import Yau.LeafProofs.L17LocalHolderAlgebraBilinear

/-! The actual selected-chart scalar extension, with no additional cutoff. -/
noncomputable section
open Set Metric
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L17BootstrapScalarCorrectionAux
open L17Aux L17HolderAux L17SchauderAux L17BootstrapPatchAux
open L17LocalHolderAlgebraAux L17LocalScalarAssemblyAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {x : M.Carrier} (D : BootstrapPatch P x)
variable {T gamma : ℝ}

/-- The dependent inverse-ball branch gives a genuine local-cylinder argument. -/
def patchScalarValue (d : LocalHolderSpace ℝ P T gamma) (q : Cylinder M T) : ℝ :=
  if hy : q.1 ∈ (P.charts.chart D.center).target then
    if hz : (P.charts.chart D.center).symm q.1 ∈ ball (0 : ComplexVector n) P.radius then
      localFun ℝ d ⟨D.center,(⟨(P.charts.chart D.center).symm q.1,hz⟩,q.2)⟩
    else 0
  else 0

/-- On the genuine chart ball, the extension has exactly the given local value. -/
theorem patchScalarValue_chart (d : LocalHolderSpace ℝ P T gamma)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    patchScalarValue D d (P.charts.chart D.center z,t) = localFun ℝ d ⟨D.center,(z,t)⟩ := by
  have hzSource : (z : ComplexVector n) ∈ (P.charts.chart D.center).source :=
    P.charts.closedBall_source D.center
      (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) z.property))
  have hy := (P.charts.chart D.center).map_source hzSource
  have hzInverse : (P.charts.chart D.center).symm (P.charts.chart D.center z) ∈
      ball (0 : ComplexVector n) P.radius := by
    rw [(P.charts.chart D.center).left_inv hzSource]
    exact z.property
  rw [patchScalarValue,dite_eq_left hy,dite_eq_left hzInverse]
  have heq : (⟨(P.charts.chart D.center).symm (P.charts.chart D.center z),hzInverse⟩ :
      ↥(ball (0 : ComplexVector n) P.radius)) = z :=
    Subtype.ext ((P.charts.chart D.center).left_inv hzSource)
  rw [heq]

/-- Local zero values outside the bump give zero outside its actual manifold image. -/
theorem patchScalarValue_zero_off_support (d : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0)
    (q : Cylinder M T) (hq : q.1 ∉ D.supportSet) : patchScalarValue D d q = 0 := by
  classical
  unfold patchScalarValue
  split_ifs with hy hz
  · apply hd
    right
    intro hSupport
    exact hq ⟨(P.charts.chart D.center).symm q.1,hSupport,
      (P.charts.chart D.center).right_inv hy⟩
  · rfl
  · rfl

/-- The ordinary function support is contained in the physical patch support. -/
theorem patchScalarValue_support_subset (d : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0) :
    Function.support (patchScalarValue D d) ⊆ {q : Cylinder M T | q.1 ∈ D.supportSet} := by
  intro q hq
  by_contra hNot
  exact hq (patchScalarValue_zero_off_support D d hd q hNot)

/-- Every non-selected term vanishes, without a finite-support assumption. -/
theorem scalarAssemblyTerm_mul_zero (d sigma : LocalHolderSpace ℝ P T gamma)
    (hd : ∀ q : LocalCylinder P T,
      q.1 ≠ D.center ∨ (q.2.1 : ComplexVector n) ∉ tsupport D.bump → localFun ℝ d q = 0)
    (p : P.centers) (hp : p ≠ D.center) (q : Cylinder M T) :
    scalarAssemblyTerm P (localBilinearCLM (ContinuousLinearMap.mul ℝ ℝ) sigma d) p q = 0 := by
  classical
  unfold scalarAssemblyTerm
  split_ifs with hy hz
  · rw [localBilinearCLM_value]
    change P.weight p q.1 * (localFun ℝ sigma ⟨p,(⟨_,hz⟩,q.2)⟩ *
      localFun ℝ d ⟨p,(⟨_,hz⟩,q.2)⟩) = 0
    rw [hd _ (Or.inl hp),mul_zero,mul_zero]
  · rfl
  · rfl

end Yau.LeafProofs.L17BootstrapScalarCorrectionAux

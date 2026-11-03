import Yau.LeafProofs.L17LocalizedSchauderLocalEstimates
import Yau.LeafProofs.L17LocalizedSchauderHolderContinuity

open Set Metric
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

abbrev UnitCylinder (n : ℕ) (T : ℝ) := ↥(ball (0 : ComplexVector n) 1) × Time T

theorem continuous_unit_family_of_parabolic_difference {T rho gamma C : ℝ} (hρ : 0 < rho)
    (hγ : 0 < gamma) {F : Type*} [NormedAddCommGroup F]
    (f : ComplexVector n × Time T → F)
    (hDiff : ∀ z w, z ∈ ball (0 : ComplexVector n) 1 → w ∈ ball 0 1 → ∀ t s : Time T,
      ‖f (z,t)-f (w,s)‖ ≤ C*(unitParabolicDistance rho (z,t) (w,s))^gamma) :
    Continuous (fun q : UnitCylinder n T => f (q.1,q.2)) := by
  apply continuous_of_power_difference (d := fun q r : UnitCylinder n T =>
    unitParabolicDistance rho ((q.1 : ComplexVector n),q.2) ((r.1 : ComplexVector n),r.2)) hγ
  · intro q
    unfold unitParabolicDistance
    fun_prop
  · intro q
    simp only [unitParabolicDistance,sub_self,norm_zero,abs_zero,Real.sqrt_zero,zero_div,add_zero]
  · intro q r
    exact unitParabolicDistance_nonneg hρ ((q.1 : ComplexVector n),q.2) ((r.1 : ComplexVector n),r.2)
  · intro q r
    exact hDiff q.1 r.1 q.1.property r.1.property q.2 r.2

def globalUnitGradient (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier) (t : Time T) : ComplexVector n → D1 n :=
  fderiv ℝ (globalUnitValue P T v q t)

def globalUnitHessian (P : UniformChartPartition g) (T : ℝ)
    (v : P.centers → ComplexVector n × Time T → ℝ) (q : M.Carrier) (t : Time T) : ComplexVector n → D2 n :=
  fderiv ℝ (globalUnitGradient P T v q t)

variable (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma B : ℝ}
    (hB : 0 ≤ B) (hLocal : LocalizedFourJetBounds P T gamma B v b)

include hTrue

theorem globalUnitValue_hasFDerivAt (q : M.Carrier) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 1) :
    HasFDerivAt (globalUnitValue P T v q t) (globalUnitGradient P T v q t z) z :=
  ((globalUnitValue_contDiffAt_two P T hT v D H b hTrue q t hz).differentiableAt (by norm_num)).hasFDerivAt

theorem globalUnitGradient_hasFDerivAt (q : M.Carrier) (t : Time T) {z : ComplexVector n} (hz : z ∈ ball 0 1) :
    HasFDerivAt (globalUnitGradient P T v q t) (globalUnitHessian P T v q t z) z := by
  have hC := (globalUnitValue_contDiffAt_two P T hT v D H b hTrue q t hz).fderiv_right
    (m := 1) (by norm_num)
  exact (hC.differentiableAt (by norm_num)).hasFDerivAt

include hB hLocal

theorem globalUnit_derivative_bounds (q : M.Carrier) (t s : Time T) {z w : ComplexVector n}
    (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1) :
    (‖globalUnitGradient P T v q t z‖ ≤ (P.overlapBudget : ℝ)*B ∧
      ‖globalUnitHessian P T v q t z‖ ≤ (P.overlapBudget : ℝ)*B) ∧
    (‖globalUnitGradient P T v q t z-globalUnitGradient P T v q s w‖ ≤
        (2*(P.overlapBudget : ℝ))*B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma ∧
      ‖globalUnitHessian P T v q t z-globalUnitHessian P T v q s w‖ ≤
        (2*(P.overlapBudget : ℝ))*B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma) := by
  have hOne := globalUnitValue_jet_bounds P T hT v D H b hTrue hB hLocal.1 q t s hz hw 1 (by norm_num)
  have hTwo := globalUnitValue_jet_bounds P T hT v D H b hTrue hB hLocal.1 q t s hz hw 2 (by norm_num)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · simpa only [norm_iteratedFDeriv_one,globalUnitGradient] using hOne.1
  · rw [← norm_iteratedFDeriv_fderiv (n := 1),norm_iteratedFDeriv_one] at hTwo
    exact hTwo.1
  · simpa only [norm_iteratedFDeriv_one_sub,globalUnitGradient] using hOne.2
  · simpa only [norm_iteratedFDeriv_two_sub,globalUnitGradient,globalUnitHessian] using hTwo.2

theorem globalUnitGradient_continuous (hγ : 0 < gamma) (q : M.Carrier) :
    Continuous (fun r : UnitCylinder n T => globalUnitGradient P T v q r.2 r.1) := by
  exact continuous_unit_family_of_parabolic_difference P.radius_pos hγ
    (fun r => globalUnitGradient P T v q r.2 r.1)
    (fun z w hz hw t s => (globalUnit_derivative_bounds P T hT v D H b hTrue hB hLocal q t s hz hw).2.1)

theorem globalUnitHessian_continuous (hγ : 0 < gamma) (q : M.Carrier) :
    Continuous (fun r : UnitCylinder n T => globalUnitHessian P T v q r.2 r.1) := by
  exact continuous_unit_family_of_parabolic_difference P.radius_pos hγ
    (fun r => globalUnitHessian P T v q r.2 r.1)
    (fun z w hz hw t s => (globalUnit_derivative_bounds P T hT v D H b hTrue hB hLocal q t s hz hw).2.2)

end Yau.LeafProofs.L17LocalizedSchauderAux

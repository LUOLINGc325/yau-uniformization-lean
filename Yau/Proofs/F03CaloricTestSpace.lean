import Yau.LeafProofs.L16WeakL2Representation
import Yau.LeafProofs.L16EnergyEquation

/-! Explicit bounded test constraints for the fixed local weak-caloric space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

abbrev CaloricL2 (D : Set (Point d)) := Lp ℝ 2 (volume.restrict D)
abbrev CaloricAmbient (D : Set (Point d)) := CaloricL2 D × (RIdx d → CaloricL2 D)

def caloricValueCLM (D : Set (Point d)) : CaloricAmbient D →L[ℝ] CaloricL2 D :=
  ContinuousLinearMap.fst ℝ (CaloricL2 D) (RIdx d → CaloricL2 D)

def caloricGradientCLM (D : Set (Point d)) (i : RIdx d) : CaloricAmbient D →L[ℝ] CaloricL2 D :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (CaloricL2 D) (RIdx d → CaloricL2 D))

def caloricSpatialTest (D : Set (Point d)) (φ : testFunctionSpace D) (i : RIdx d) :
    testFunctionSpace D :=
  ⟨fun p => Parabolic.d (fun x => φ.val (x,p.2)) p.1 i,test_spatialDerivative φ.2 i⟩

def caloricTimeTest (D : Set (Point d)) (φ : testFunctionSpace D) : testFunctionSpace D :=
  ⟨fun p => deriv (fun t => φ.val (p.1,t)) p.2,test_timeDerivative φ.2⟩

def caloricCoefficientTest (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (i j : RIdx d) : testFunctionSpace D := by
  refine ⟨fun p => a p i j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i,?_⟩
  change Test D (fun p => a p i j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)
  have h := test_mul_contDiffOn hD (test_spatialDerivative φ.2 i)
    ((matrixEntryCLM i j).contDiff.comp_contDiffOn hAB.1)
  simpa only [Function.comp_def,matrixEntryCLM_apply,mul_comm] using h

def caloricDriftTest (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (j : RIdx d) : testFunctionSpace D := by
  refine ⟨fun p => energyDrift a b p j*φ.val p,?_⟩
  change Test D (fun p => energyDrift a b p j*φ.val p)
  have h := test_mul_contDiffOn hD φ.2 (energyDrift_smooth hD hAB j)
  simpa only [mul_comm] using h

def caloricEquationTest (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (j : RIdx d) : testFunctionSpace D :=
  (∑ i, caloricCoefficientTest D hD a b hAB φ i j)-caloricDriftTest D hD a b hAB φ j

theorem caloricEquationTest_apply (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) (j : RIdx d) (p : Point d) :
    (caloricEquationTest D hD a b hAB φ j).val p =
      (∑ i, a p i j*Parabolic.d (fun x => φ.val (x,p.2)) p.1 i)-energyDrift a b p j*φ.val p := by
  simp only [caloricEquationTest,caloricCoefficientTest,caloricDriftTest,
    Submodule.coe_sub,Submodule.coe_sum,Pi.sub_apply,Finset.sum_apply]

def caloricTestPair (D : Set (Point d)) (φ : testFunctionSpace D) : CaloricL2 D →L[ℝ] ℝ :=
  innerSL ℝ (testToL2 D φ)

theorem caloricTestPair_apply (D : Set (Point d)) (φ : testFunctionSpace D) (v : CaloricL2 D) :
    caloricTestPair D φ v=∫ p, v p*φ.val p ∂volume.restrict D := by
  change inner ℝ (testToL2 D φ) v=_
  rw [real_inner_comm,inner_testToL2]

def caloricGradientTestCLM (D : Set (Point d)) (φ : testFunctionSpace D) (i : RIdx d) :
    CaloricAmbient D →L[ℝ] ℝ :=
  (caloricTestPair D (caloricSpatialTest D φ i)).comp (caloricValueCLM D)+
    (caloricTestPair D φ).comp (caloricGradientCLM D i)

def caloricEquationTestCLM (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b)
    (φ : testFunctionSpace D) : CaloricAmbient D →L[ℝ] ℝ :=
  -((caloricTestPair D (caloricTimeTest D φ)).comp (caloricValueCLM D))+
    ∑ j, (caloricTestPair D (caloricEquationTest D hD a b hAB φ j)).comp (caloricGradientCLM D j)

def caloricSubmodule (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b) :
    Submodule ℝ (CaloricAmbient D) where
  carrier := {e | (∀ φ i, caloricGradientTestCLM D φ i e=0) ∧
    ∀ φ, caloricEquationTestCLM D hD a b hAB φ e=0}
  zero_mem' := by simp
  add_mem' := by
    intro e f he hf
    exact ⟨fun φ i => by rw [map_add,he.1 φ i,hf.1 φ i,zero_add],
      fun φ => by rw [map_add,he.2 φ,hf.2 φ,zero_add]⟩
  smul_mem' := by
    intro c e he
    exact ⟨fun φ i => by rw [map_smul,he.1 φ i,smul_zero],
      fun φ => by rw [map_smul,he.2 φ,smul_zero]⟩

theorem caloricSubmodule_isClosed (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b) :
    IsClosed (caloricSubmodule D hD a b hAB : Set (CaloricAmbient D)) := by
  change IsClosed {e | (∀ φ i, caloricGradientTestCLM D φ i e=0) ∧
    ∀ φ, caloricEquationTestCLM D hD a b hAB φ e=0}
  simpa only [setOf_and,setOf_forall] using
    (isClosed_iInter (fun φ => isClosed_iInter (fun i =>
      isClosed_eq (caloricGradientTestCLM D φ i).continuous continuous_const))).inter
    (isClosed_iInter (fun φ => isClosed_eq (caloricEquationTestCLM D hD a b hAB φ).continuous continuous_const))

abbrev CaloricSpace (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b) :=
  ↥(caloricSubmodule D hD a b hAB)

instance caloricSpace_completeSpace (D : Set (Point d)) (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ) (hAB : SmoothCoefficients D a b) :
    CompleteSpace (CaloricSpace D hD a b hAB) :=
  (caloricSubmodule_isClosed D hD a b hAB).completeSpace_coe

end Yau.Proofs.F03Aux

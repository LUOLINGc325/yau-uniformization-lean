import Yau.Proofs.F05VectorHolder
import Yau.LeafProofs.L16CompatibleHolderGraph

/-! The actual four Banach components for a spatial C2, temporal C1 jet.
No differentiability or realization is stored as data in this ambient space. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

abbrev F05Dual (n : ℕ) := Space n →L[ℝ] ℝ
abbrev F05Hessian (n : ℕ) := Space n →L[ℝ] Space n →L[ℝ] ℝ

local instance f05_jetHessianGroup : NormedAddCommGroup (F05Hessian n) := inferInstance
local instance f05_jetHessianSpace : NormedSpace ℝ (F05Hessian n) := inferInstance
local instance f05_jetHessianComplete : CompleteSpace (F05Hessian n) := inferInstance
local instance f05_jetHolderGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (holderGraph α Q) := inferInstance
local instance f05_jetHolderSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (holderGraph α Q) := inferInstance
local instance f05_jetVectorGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (vectorHolderGraph (F05Hessian n) α Q) := inferInstance
local instance f05_jetVectorSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (vectorHolderGraph (F05Hessian n) α Q) := inferInstance

abbrev F05JetComponent (α : ℝ) (Q : Set (Point n)) :=
  BoundedContinuousFunction Q ℝ × BoundedContinuousFunction Q (F05Dual n) ×
    vectorHolderGraph (F05Hessian n) α Q × holderGraph α Q

instance F05_jetComponent_normedAddCommGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (F05JetComponent α Q) := inferInstance
instance F05_jetComponent_normedSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (F05JetComponent α Q) := inferInstance

def F05JetValues (α : ℝ) (Q : Set (Point n)) :
    F05JetComponent α Q →L[ℝ] BoundedContinuousFunction Q ℝ :=
  ContinuousLinearMap.fst ℝ _ _

def F05JetGradients (α : ℝ) (Q : Set (Point n)) :
    F05JetComponent α Q →L[ℝ] BoundedContinuousFunction Q (F05Dual n) :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

def F05JetHessians (α : ℝ) (Q : Set (Point n)) :
    F05JetComponent α Q →L[ℝ] BoundedContinuousFunction Q (F05Hessian n) :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (vectorHolderGraph (F05Hessian n) α Q).subtypeL).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))

def F05JetTimeDerivatives (α : ℝ) (Q : Set (Point n)) :
    F05JetComponent α Q →L[ℝ] BoundedContinuousFunction Q ℝ :=
  ((ContinuousLinearMap.fst ℝ _ _).comp (holderGraph α Q).subtypeL).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)))

theorem F05JetValues_apply (α : ℝ) (Q : Set (Point n)) (u : F05JetComponent α Q) :
    F05JetValues α Q u = u.1 := rfl
theorem F05JetGradients_apply (α : ℝ) (Q : Set (Point n)) (u : F05JetComponent α Q) :
    F05JetGradients α Q u = u.2.1 := rfl
theorem F05JetHessians_apply (α : ℝ) (Q : Set (Point n)) (u : F05JetComponent α Q) :
    F05JetHessians α Q u = u.2.2.1.val.1 := rfl
theorem F05JetTimeDerivatives_apply (α : ℝ) (Q : Set (Point n)) (u : F05JetComponent α Q) :
    F05JetTimeDerivatives α Q u = u.2.2.2.val.1 := rfl

instance F05_jetComponent_completeSpace (α : ℝ) (Q : Set (Point n)) :
    CompleteSpace (F05JetComponent α Q) := inferInstance

end Yau.Proofs.F05Aux

import Yau.Proofs.F05JetZeroData

/-! The actual chart value, gradient, Hessian, and time overlap equations are
closed linear constraints on the finite product of genuine local FTC graphs. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_ambientDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_ambientDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_ambientHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_ambientHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

local instance f05_overlapLocalGroup (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : NormedAddCommGroup (F05LocalZeroFTCGraph A i α hT) :=
  F05_localZeroFTCGraph_normedAddCommGroup A i α hT
local instance f05_overlapLocalSpace (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : NormedSpace ℝ (F05LocalZeroFTCGraph A i α hT) :=
  F05_localZeroFTCGraph_normedSpace A i α hT
local instance f05_overlapComponentGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (F05JetComponent α Q) := F05_jetComponent_normedAddCommGroup α Q
local instance f05_overlapComponentSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (F05JetComponent α Q) := F05_jetComponent_normedSpace α Q

def F05JetAmbient (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :=
  ∀ i : Fin A.count, F05LocalZeroFTCGraph A i α hT

instance F05_jetAmbient_normedAddCommGroup (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    NormedAddCommGroup (F05JetAmbient A α hT) := by
  unfold F05JetAmbient
  infer_instance
instance F05_jetAmbient_normedSpace (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    NormedSpace ℝ (F05JetAmbient A α hT) := by
  unfold F05JetAmbient
  infer_instance

instance F05_jetAmbient_completeSpace (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    CompleteSpace (F05JetAmbient A α hT) := by
  unfold F05JetAmbient
  infer_instance

def F05GlobalComponent (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (i : Fin A.count) :
    F05JetAmbient A α hT →L[ℝ] F05JetComponent α (F05Q A i T) :=
  (F05LocalZeroFTCGraph A i α hT).subtypeL.comp (ContinuousLinearMap.proj i)

def F05GlobalValueEval (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  (F05JetValueEval α (F05Q A i T) p).comp (F05GlobalComponent A α hT i)

def F05GlobalTimeEval (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  (F05JetTimeEval α (F05Q A i T) p).comp (F05GlobalComponent A α hT i)

def F05GlobalGradientEval (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) : F05JetAmbient A α hT →L[ℝ] F05Dual n :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp
    ((F05JetGradients α (F05Q A i T)).comp (F05GlobalComponent A α hT i))

def F05GlobalHessianEval (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) : F05JetAmbient A α hT →L[ℝ] F05Hessian n :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp
    ((F05JetHessians α (F05Q A i T)).comp (F05GlobalComponent A α hT i))

end Yau.Proofs.F05Aux

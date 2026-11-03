import Yau.Proofs.F05JetAmbient

/-! Actual overlap constraints define a closed subspace of the finite jet product. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_overlapDualGroup : NormedAddCommGroup (F05Dual n) := f05_ambientDualGroup
local instance f05_overlapDualSpace : NormedSpace ℝ (F05Dual n) := f05_ambientDualSpace
local instance f05_overlapHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_ambientHessianGroup
local instance f05_overlapHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_ambientHessianSpace

structure F05OverlapPoint (A : AtlasData M) (T : ℝ) where
  left : Fin A.count
  right : Fin A.count
  leftCoord : F05D A left
  rightCoord : F05D A right
  time : Icc 0 T
  samePoint : lift A left leftCoord.val = lift A right rightCoord.val

def F05OverlapPoint.leftPoint {A : AtlasData M} {T : ℝ} (p : F05OverlapPoint A T) : F05Q A p.left T :=
  ⟨(p.leftCoord.val,p.time.val),p.leftCoord.property,p.time.property⟩
def F05OverlapPoint.rightPoint {A : AtlasData M} {T : ℝ} (p : F05OverlapPoint A T) : F05Q A p.right T :=
  ⟨(p.rightCoord.val,p.time.val),p.rightCoord.property,p.time.property⟩

def F05ValueOverlapResidual (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (p : F05OverlapPoint A T) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  F05GlobalValueEval A α hT p.left p.leftPoint - F05GlobalValueEval A α hT p.right p.rightPoint

def F05TimeOverlapResidual (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (p : F05OverlapPoint A T) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  F05GlobalTimeEval A α hT p.left p.leftPoint - F05GlobalTimeEval A α hT p.right p.rightPoint

def F05GradientOverlapResidual (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (p : F05OverlapPoint A T) (v : Space n) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ v).comp (F05GlobalGradientEval A α hT p.left p.leftPoint) -
    (ContinuousLinearMap.apply ℝ ℝ
      (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v)).comp
        (F05GlobalGradientEval A α hT p.right p.rightPoint)

def F05HessianOverlapResidual (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (p : F05OverlapPoint A T) (v w : Space n) : F05JetAmbient A α hT →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (F05Dual n) v)).comp
      (F05GlobalHessianEval A α hT p.left p.leftPoint) -
    ((ContinuousLinearMap.apply ℝ ℝ
      (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val w)).comp
        (ContinuousLinearMap.apply ℝ (F05Dual n)
          (fderiv ℝ (F05Transition A p.left p.right) p.leftCoord.val v))).comp
            (F05GlobalHessianEval A α hT p.right p.rightPoint) -
    (ContinuousLinearMap.apply ℝ ℝ
      (fderiv ℝ (fderiv ℝ (F05Transition A p.left p.right)) p.leftCoord.val v w)).comp
        (F05GlobalGradientEval A α hT p.right p.rightPoint)

def F05ValueOverlapGraph (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetAmbient A α hT) := ⨅ p, (F05ValueOverlapResidual A α hT p).ker
def F05TimeOverlapGraph (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetAmbient A α hT) := ⨅ p, (F05TimeOverlapResidual A α hT p).ker
def F05GradientOverlapGraph (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetAmbient A α hT) := ⨅ p, ⨅ v, (F05GradientOverlapResidual A α hT p v).ker
def F05HessianOverlapGraph (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetAmbient A α hT) := ⨅ p, ⨅ v, ⨅ w, (F05HessianOverlapResidual A α hT p v w).ker

theorem F05ValueOverlapGraph_isClosed (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05ValueOverlapGraph A α hT : Set (F05JetAmbient A α hT)) := by
  rw [F05ValueOverlapGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun p => (F05ValueOverlapResidual A α hT p).isClosed_ker
theorem F05TimeOverlapGraph_isClosed (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05TimeOverlapGraph A α hT : Set (F05JetAmbient A α hT)) := by
  rw [F05TimeOverlapGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun p => (F05TimeOverlapResidual A α hT p).isClosed_ker
theorem F05GradientOverlapGraph_isClosed (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05GradientOverlapGraph A α hT : Set (F05JetAmbient A α hT)) := by
  simp only [F05GradientOverlapGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun p => isClosed_iInter fun v => (F05GradientOverlapResidual A α hT p v).isClosed_ker
theorem F05HessianOverlapGraph_isClosed (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05HessianOverlapGraph A α hT : Set (F05JetAmbient A α hT)) := by
  simp only [F05HessianOverlapGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun p => isClosed_iInter fun v => isClosed_iInter fun w =>
    (F05HessianOverlapResidual A α hT p v w).isClosed_ker

def F05CompatibleJetGraph (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetAmbient A α hT) :=
  F05ValueOverlapGraph A α hT ⊓ F05TimeOverlapGraph A α hT ⊓
    F05GradientOverlapGraph A α hT ⊓ F05HessianOverlapGraph A α hT

set_option backward.isDefEq.respectTransparency.types true in
theorem F05CompatibleJetGraph_isClosed (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05CompatibleJetGraph A α hT : Set (F05JetAmbient A α hT)) := by
  change IsClosed ((((F05ValueOverlapGraph A α hT : Set (F05JetAmbient A α hT)) ∩
    (F05TimeOverlapGraph A α hT : Set (F05JetAmbient A α hT))) ∩
    (F05GradientOverlapGraph A α hT : Set (F05JetAmbient A α hT))) ∩
    (F05HessianOverlapGraph A α hT : Set (F05JetAmbient A α hT)))
  exact (((F05ValueOverlapGraph_isClosed A α hT).inter
    (F05TimeOverlapGraph_isClosed A α hT)).inter
    (F05GradientOverlapGraph_isClosed A α hT)).inter (F05HessianOverlapGraph_isClosed A α hT)

instance F05_compatibleJetGraph_completeSpace (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    CompleteSpace (F05CompatibleJetGraph A α hT) :=
  (F05CompatibleJetGraph_isClosed A α hT).completeSpace_coe

instance F05_compatibleJetGraph_normedAddCommGroup (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    NormedAddCommGroup (F05CompatibleJetGraph A α hT) := inferInstance
instance F05_compatibleJetGraph_normedSpace (A : AtlasData M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    NormedSpace ℝ (F05CompatibleJetGraph A α hT) := inferInstance

end Yau.Proofs.F05Aux

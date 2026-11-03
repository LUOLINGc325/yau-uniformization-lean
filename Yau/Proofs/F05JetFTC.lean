import Yau.Proofs.F05JetComponents
import Yau.Proofs.F05Paths
import Yau.Proofs.F05IntegralOperator

/-! The spatial and temporal fundamental theorem constraints form an actual
closed Banach submodule of the four-component jet product. -/

open Set MeasureTheory
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_ftcDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_ftcDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_ftcHessianGroup : NormedAddCommGroup (F05Hessian n) := inferInstance
local instance f05_ftcHessianSpace : NormedSpace ℝ (F05Hessian n) := inferInstance
local instance f05_ftcComponentGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (F05JetComponent α Q) := inferInstance
local instance f05_ftcComponentSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (F05JetComponent α Q) := inferInstance

def F05JetSpatialValueResidual (A : AtlasData M) (i : Fin A.count) (α T : ℝ)
    (z w : F05D A i) (t : Icc 0 T) : F05JetComponent α (F05Q A i T) →L[ℝ] ℝ :=
  ((BoundedContinuousFunction.evalCLM ℝ ⟨(w.val,t.val),w.property,t.property⟩).comp
      (F05JetValues α (F05Q A i T)) -
    (BoundedContinuousFunction.evalCLM ℝ ⟨(z.val,t.val),z.property,t.property⟩).comp
      (F05JetValues α (F05Q A i T))) -
    (ContinuousLinearMap.apply ℝ ℝ (w.val-z.val)).comp
      ((F05PathIntegral (F05SpatialPath A i T z.property w.property t.property)
        (F05SpatialPath_continuous A i T z.property w.property t.property) 0 1).comp
          (F05JetGradients α (F05Q A i T)))

def F05JetSpatialGradientResidual (A : AtlasData M) (i : Fin A.count) (α T : ℝ)
    (z w : F05D A i) (t : Icc 0 T) : F05JetComponent α (F05Q A i T) →L[ℝ] F05Dual n :=
  ((BoundedContinuousFunction.evalCLM ℝ ⟨(w.val,t.val),w.property,t.property⟩).comp
      (F05JetGradients α (F05Q A i T)) -
    (BoundedContinuousFunction.evalCLM ℝ ⟨(z.val,t.val),z.property,t.property⟩).comp
      (F05JetGradients α (F05Q A i T))) -
    (ContinuousLinearMap.apply ℝ (F05Dual n) (w.val-z.val)).comp
      ((F05PathIntegral (F05SpatialPath A i T z.property w.property t.property)
        (F05SpatialPath_continuous A i T z.property w.property t.property) 0 1).comp
          (F05JetHessians α (F05Q A i T)))

def F05JetTimeResidual (A : AtlasData M) (i : Fin A.count) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (z : F05D A i) (s t : Icc 0 T) : F05JetComponent α (F05Q A i T) →L[ℝ] ℝ :=
  ((BoundedContinuousFunction.evalCLM ℝ ⟨(z.val,t.val),z.property,t.property⟩).comp
      (F05JetValues α (F05Q A i T)) -
    (BoundedContinuousFunction.evalCLM ℝ ⟨(z.val,s.val),z.property,s.property⟩).comp
      (F05JetValues α (F05Q A i T))) -
    (F05PathIntegral (F05TimePath A i hT z.property)
      (F05TimePath_continuous A i hT z.property) s.val t.val).comp
        (F05JetTimeDerivatives α (F05Q A i T))

def F05LocalFTCGraph (A : AtlasData M) (i : Fin A.count) (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    Submodule ℝ (F05JetComponent α (F05Q A i T)) :=
  (⨅ z : F05D A i, ⨅ w : F05D A i, ⨅ t : Icc 0 T,
    (F05JetSpatialValueResidual A i α T z w t).ker) ⊓
  (⨅ z : F05D A i, ⨅ w : F05D A i, ⨅ t : Icc 0 T,
    (F05JetSpatialGradientResidual A i α T z w t).ker) ⊓
  (⨅ z : F05D A i, ⨅ s : Icc 0 T, ⨅ t : Icc 0 T,
    (F05JetTimeResidual A i α hT z s t).ker)

instance F05_localFTCGraph_normedAddCommGroup (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : NormedAddCommGroup (F05LocalFTCGraph A i α hT) := inferInstance
instance F05_localFTCGraph_normedSpace (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : NormedSpace ℝ (F05LocalFTCGraph A i α hT) := inferInstance

theorem F05LocalFTCGraph_isClosed (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05LocalFTCGraph A i α hT : Set (F05JetComponent α (F05Q A i T))) := by
  simp only [F05LocalFTCGraph,Submodule.coe_inf,Submodule.coe_iInf]
  exact ((isClosed_iInter fun z => isClosed_iInter fun w => isClosed_iInter fun t =>
    (F05JetSpatialValueResidual A i α T z w t).isClosed_ker).inter
      (isClosed_iInter fun z => isClosed_iInter fun w => isClosed_iInter fun t =>
        (F05JetSpatialGradientResidual A i α T z w t).isClosed_ker)).inter
    (isClosed_iInter fun z => isClosed_iInter fun s => isClosed_iInter fun t =>
      (F05JetTimeResidual A i α hT z s t).isClosed_ker)

instance F05_localFTCGraph_completeSpace (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : CompleteSpace (F05LocalFTCGraph A i α hT) :=
  (F05LocalFTCGraph_isClosed A i α hT).completeSpace_coe

theorem F05LocalFTCGraph_spatial_value (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (z w : F05D A i) (t : Icc 0 T) :
    u.val.1 ⟨(w.val,t.val),w.property,t.property⟩ -
      u.val.1 ⟨(z.val,t.val),z.property,t.property⟩ =
    (∫ r in (0 : ℝ)..1,
      u.val.2.1 (F05SpatialPath A i T z.property w.property t.property r)) (w.val-z.val) := by
  have hh := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp u.property.1.1 z) w) t
  change F05JetSpatialValueResidual A i α T z w t u.val = 0 at hh
  exact sub_eq_zero.mp hh

theorem F05LocalFTCGraph_spatial_gradient (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (z w : F05D A i) (t : Icc 0 T) :
    u.val.2.1 ⟨(w.val,t.val),w.property,t.property⟩ -
      u.val.2.1 ⟨(z.val,t.val),z.property,t.property⟩ =
    (∫ r in (0 : ℝ)..1,
      u.val.2.2.1.val.1 (F05SpatialPath A i T z.property w.property t.property r))
        (w.val-z.val) := by
  have hh := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp u.property.1.2 z) w) t
  change F05JetSpatialGradientResidual A i α T z w t u.val = 0 at hh
  exact sub_eq_zero.mp hh

theorem F05LocalFTCGraph_time (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (u : F05LocalFTCGraph A i α hT)
    (z : F05D A i) (s t : Icc 0 T) :
    u.val.1 ⟨(z.val,t.val),z.property,t.property⟩ -
      u.val.1 ⟨(z.val,s.val),z.property,s.property⟩ =
    ∫ r in s.val..t.val, u.val.2.2.2.val.1 (F05TimePath A i hT z.property r) := by
  have hh := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp u.property.2 z) s) t
  change F05JetTimeResidual A i α hT z s t u.val = 0 at hh
  exact sub_eq_zero.mp hh

end Yau.Proofs.F05Aux

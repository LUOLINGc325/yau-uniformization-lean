import Yau.Proofs.F05JetFTC

/-! Actual homogeneous initial and physical lateral data are closed linear
constraints. There is no data condition on the artificial chart rim. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_zeroComponentGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (F05JetComponent α Q) := inferInstance
local instance f05_zeroComponentSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (F05JetComponent α Q) := inferInstance

def F05JetValueEval (α : ℝ) (Q : Set (Point n)) (p : Q) :
    F05JetComponent α Q →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp (F05JetValues α Q)

def F05JetTimeEval (α : ℝ) (Q : Set (Point n)) (p : Q) :
    F05JetComponent α Q →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ p).comp (F05JetTimeDerivatives α Q)

def F05LocalInitialValueGraph (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : Submodule ℝ (F05JetComponent α (F05Q A i T)) :=
  ⨅ z : F05D A i, (F05JetValueEval α (F05Q A i T) ⟨(z.val,0),z.property,le_rfl,hT⟩).ker

def F05LocalInitialTimeGraph (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : Submodule ℝ (F05JetComponent α (F05Q A i T)) :=
  ⨅ z : F05D A i, (F05JetTimeEval α (F05Q A i T) ⟨(z.val,0),z.property,le_rfl,hT⟩).ker

def F05LocalLateralGraph (A : AtlasData M) (i : Fin A.count) (α T : ℝ) :
    Submodule ℝ (F05JetComponent α (F05Q A i T)) :=
  ⨅ z : F05D A i, ⨅ t : Icc 0 T, ⨅ j : RIdx n, ⨅ _hν : A.normal i = some j,
    ⨅ _hz : realCoord z.val j = 0,
      (F05JetValueEval α (F05Q A i T) ⟨(z.val,t.val),z.property,t.property⟩).ker

def F05LocalZeroFTCGraph (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : Submodule ℝ (F05JetComponent α (F05Q A i T)) :=
  F05LocalFTCGraph A i α hT ⊓ F05LocalInitialValueGraph A i α hT ⊓
    F05LocalInitialTimeGraph A i α hT ⊓ F05LocalLateralGraph A i α T

instance F05_localZeroFTCGraph_normedAddCommGroup (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) : NormedAddCommGroup (F05LocalZeroFTCGraph A i α hT) := inferInstance
instance F05_localZeroFTCGraph_normedSpace (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) : NormedSpace ℝ (F05LocalZeroFTCGraph A i α hT) := inferInstance

theorem F05LocalInitialValueGraph_isClosed (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05LocalInitialValueGraph A i α hT : Set (F05JetComponent α (F05Q A i T))) := by
  rw [F05LocalInitialValueGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun z => (F05JetValueEval α (F05Q A i T)
    ⟨(z.val,0),z.property,le_rfl,hT⟩).isClosed_ker

theorem F05LocalInitialTimeGraph_isClosed (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05LocalInitialTimeGraph A i α hT : Set (F05JetComponent α (F05Q A i T))) := by
  rw [F05LocalInitialTimeGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun z => (F05JetTimeEval α (F05Q A i T)
    ⟨(z.val,0),z.property,le_rfl,hT⟩).isClosed_ker

theorem F05LocalLateralGraph_isClosed (A : AtlasData M) (i : Fin A.count)
    (α T : ℝ) :
    IsClosed (F05LocalLateralGraph A i α T : Set (F05JetComponent α (F05Q A i T))) := by
  simp only [F05LocalLateralGraph,Submodule.coe_iInf]
  exact isClosed_iInter fun z => isClosed_iInter fun t => isClosed_iInter fun j =>
    isClosed_iInter fun hν => isClosed_iInter fun hz =>
      (F05JetValueEval α (F05Q A i T) ⟨(z.val,t.val),z.property,t.property⟩).isClosed_ker

set_option backward.isDefEq.respectTransparency.types true in
theorem F05LocalZeroFTCGraph_isClosed (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IsClosed (F05LocalZeroFTCGraph A i α hT : Set (F05JetComponent α (F05Q A i T))) := by
  change IsClosed ((((F05LocalFTCGraph A i α hT : Set (F05JetComponent α (F05Q A i T))) ∩
    (F05LocalInitialValueGraph A i α hT : Set (F05JetComponent α (F05Q A i T)))) ∩
    (F05LocalInitialTimeGraph A i α hT : Set (F05JetComponent α (F05Q A i T)))) ∩
    (F05LocalLateralGraph A i α T : Set (F05JetComponent α (F05Q A i T))))
  exact (((F05LocalFTCGraph_isClosed A i α hT).inter
    (F05LocalInitialValueGraph_isClosed A i α hT)).inter
    (F05LocalInitialTimeGraph_isClosed A i α hT)).inter (F05LocalLateralGraph_isClosed A i α T)

instance F05_localZeroFTCGraph_completeSpace (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) : CompleteSpace (F05LocalZeroFTCGraph A i α hT) :=
  (F05LocalZeroFTCGraph_isClosed A i α hT).completeSpace_coe

def F05LocalZeroToFTC (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 ≤ T) : F05LocalZeroFTCGraph A i α hT →L[ℝ] F05LocalFTCGraph A i α hT :=
  ({ toFun := fun u => ⟨u.val,u.property.1.1.1⟩
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } :
    F05LocalZeroFTCGraph A i α hT →ₗ[ℝ] F05LocalFTCGraph A i α hT).mkContinuous 1
      (by intro u; change ‖u.val‖ ≤ 1 * ‖u.val‖; rw [one_mul])

theorem F05LocalZeroFTCGraph_initial_value (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    (z : F05D A i) : u.val.1 ⟨(z.val,0),z.property,le_rfl,hT⟩ = 0 :=
  (Submodule.mem_iInf _).mp u.property.1.1.2 z

theorem F05LocalZeroFTCGraph_initial_time (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    (z : F05D A i) : u.val.2.2.2.val.1 ⟨(z.val,0),z.property,le_rfl,hT⟩ = 0 :=
  (Submodule.mem_iInf _).mp u.property.1.2 z

theorem F05LocalZeroFTCGraph_lateral (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    (z : F05D A i) (t : Icc 0 T) (j : RIdx n) (hν : A.normal i = some j)
    (hz : realCoord z.val j = 0) : u.val.1 ⟨(z.val,t.val),z.property,t.property⟩ = 0 :=
  (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp u.property.2 z) t) j) hν) hz

end Yau.Proofs.F05Aux

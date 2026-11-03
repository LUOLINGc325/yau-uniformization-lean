import Yau.Geometry.HolomorphicBundle
import Yau.Proofs.P03Frames

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine inverse-chart differential, with its chart differential inverse. -/
def chartFrameEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    ComplexVector n ≃L[ℂ] TangentVector M x where
  toFun := chartVec a x
  invFun := tangentCoords a x
  map_add' := (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) a).symm (chartPt a x)).map_add
  map_smul' := (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) a).symm (chartPt a x)).map_smul
  left_inv := tangentCoords_chartVec a x hx
  right_inv := chartVec_tangentCoords a x hx
  continuous_toFun := (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) a).symm (chartPt a x)).continuous
  continuous_invFun := (mfderiv (ComplexModel n) (ComplexModel n)
    (extChartAt (ComplexModel n) a) x).continuous

@[simp] theorem chartFrameEquiv_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector n) :
    chartFrameEquiv a x hx v = chartVec a x v := rfl

@[simp] theorem chartFrameEquiv_symm_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (v : TangentVector M x) :
    (chartFrameEquiv a x hx).symm v = tangentCoords a x v := rfl

def determinantFrameBasis (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    Module.Basis (Fin n) ℂ (TangentVector M x) :=
  (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.map (chartFrameEquiv a x hx).toLinearEquiv

@[simp] theorem determinantFrameBasis_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (i : Fin n) :
    determinantFrameBasis a x hx i = chartVec a x (stdVec i) := by
  simp [determinantFrameBasis, EuclideanSpace.basisFun_apply, stdVec]

/-- The actual continuous top form dual to the local chart frame. -/
theorem basisDet_continuous {V : Type*} [TopologicalSpace V] [AddCommGroup V]
    [Module ℂ V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (b : Module.Basis (Fin n) ℂ V) : Continuous b.det := by
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hc (i j : Fin n) : Continuous (fun v : Fin n → V => b.repr (v j) i) :=
    (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  have hm : Continuous (fun v : Fin n → V =>
      (fun i j => b.repr (v j) i : Matrix (Fin n) (Fin n) ℂ)) :=
    continuous_pi fun i => continuous_pi fun j => hc i j
  exact hm.matrix_det

def basisContinuousDet {V : Type*} [TopologicalSpace V] [AddCommGroup V]
    [Module ℂ V] [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V]
    (b : Module.Basis (Fin n) ℂ V) : V [⋀^Fin n]→L[ℂ] ℂ :=
  { b.det with cont := basisDet_continuous b }

def chartTopForm (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) : CanonicalFiber M x :=
  basisContinuousDet (n := n) (V := TangentVector M x) (determinantFrameBasis a x hx)

@[simp] theorem chartTopForm_frame (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    chartTopForm a x hx (determinantFrameBasis a x hx) = 1 :=
  (determinantFrameBasis a x hx).det_self

theorem canonical_eq_smul_chartTopForm (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (η : CanonicalFiber M x) :
    η = η (determinantFrameBasis a x hx) • chartTopForm a x hx := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact η.toAlternatingMap.eq_smul_basis_det (determinantFrameBasis a x hx)

/-- Evaluation on the local frame is a genuine continuous dual vector. -/
def chartTopEvaluation (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) : AntiCanonicalFiber M x :=
  ContinuousAlternatingMap.apply ℂ (TangentVector M x) ℂ (determinantFrameBasis a x hx)

@[simp] theorem chartTopEvaluation_apply (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (η : CanonicalFiber M x) :
    chartTopEvaluation a x hx η = η (determinantFrameBasis a x hx) := rfl

@[simp] theorem chartTopEvaluation_topForm (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) :
    chartTopEvaluation a x hx (chartTopForm a x hx) = 1 := chartTopForm_frame a x hx

def canonicalScalarEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) : CanonicalFiber M x ≃L[ℂ] ℂ where
  toFun := chartTopEvaluation a x hx
  invFun := fun c => c • chartTopForm a x hx
  map_add' := (chartTopEvaluation a x hx).map_add
  map_smul' := (chartTopEvaluation a x hx).map_smul
  left_inv := fun η => (canonical_eq_smul_chartTopForm a x hx η).symm
  right_inv := by intro c; simp
  continuous_toFun := (chartTopEvaluation a x hx).continuous
  continuous_invFun := continuous_id.smul continuous_const

theorem anticanonical_eq_smul_chartTopEvaluation (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) (ℓ : AntiCanonicalFiber M x) :
    ℓ = ℓ (chartTopForm a x hx) • chartTopEvaluation a x hx := by
  ext η
  have h := congrArg ℓ (canonical_eq_smul_chartTopForm a x hx η)
  simpa only [map_smul, ContinuousLinearMap.smul_apply, chartTopEvaluation_apply,
    smul_eq_mul, mul_comm] using h

def antiCanonicalScalarEquiv (a x : M.Carrier)
    (hx : x ∈ (extChartAt (ComplexModel n) a).source) : AntiCanonicalFiber M x ≃L[ℂ] ℂ where
  toFun := fun ℓ => ℓ (chartTopForm a x hx)
  invFun := fun c => c • chartTopEvaluation a x hx
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl
  left_inv := fun ℓ => (anticanonical_eq_smul_chartTopEvaluation a x hx ℓ).symm
  right_inv := by intro c; simp
  continuous_toFun := continuous_eval_const (chartTopForm a x hx)
  continuous_invFun := continuous_id.smul continuous_const

end Yau.NodeProofs.P03Aux

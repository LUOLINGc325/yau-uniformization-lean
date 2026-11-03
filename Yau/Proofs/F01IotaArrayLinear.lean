import Yau.Proofs.F01TransformedMatrixIdentity

/-! The actual realification is a continuous real linear map from its
finite array of complex entries to the original Frobenius symmetric matrix
space. The array domain fixes its norm independently of matrix norm scopes. -/
noncomputable section
open scoped Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance iotaSymNormedSpace (n : ℕ) : NormedSpace ℝ (Sym n) where
  toModule := inferInstance
  norm_smul_le c A := norm_smul_le c (A : Mat n)

local instance iotaSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

local instance iotaArrayOpNorm (n : ℕ) : Norm (((Fin n × Fin n) → ℂ) →L[ℝ] Sym n) :=
  ContinuousLinearMap.hasOpNorm

def iotaArrayLinear : ((Fin n × Fin n) → ℂ) →ₗ[ℝ] Sym n where
  toFun v := iota (fun i j => v (i, j))
  map_add' v w := iota_add _ _
  map_smul' c v := by
    change iota (fun i j => c • v (i, j)) = c • iota (fun i j => v (i, j))
    have heq : (fun i j : Fin n => c • v (i, j)) = (c : ℂ) • (fun i j => v (i, j)) := by
      ext i j
      simp only [Pi.smul_apply, Algebra.smul_def]
      rfl
    rw [heq]
    exact iota_real_smul c (fun i j => v (i, j))

def iotaArrayCLM : ((Fin n × Fin n) → ℂ) →L[ℝ] Sym n :=
  iotaArrayLinear.toContinuousLinearMap

theorem iotaArrayCLM_apply (v : (Fin n × Fin n) → ℂ) :
    iotaArrayCLM v = iota (fun i j => v (i, j)) := rfl

end Yau.NodeProofs.F01Aux

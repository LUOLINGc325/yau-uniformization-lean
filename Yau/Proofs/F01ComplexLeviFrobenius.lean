import Yau.Proofs.F01RealHessianLeviLinear
import Yau.Proofs.F01HolderComposition

/-! The actual native Levi matrix is a bounded real linear image of the
spatial Hessian, into the original complex Frobenius matrix norm. This gives
its numerical Holder budget from the genuine Schauder spatial second jet. -/
noncomputable section
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance complexLeviFrobeniusOpNorm (n : ℕ) :
    Norm ((Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.hasOpNorm

def complexArrayToFrobeniusCLM : ((Fin n × Fin n) → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := (Fin n × Fin n) → ℂ) (F' := Matrix (Fin n) (Fin n) ℂ)
    { toFun := fun v i j => v (i, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def leviSecondMatrixCLM :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  complexArrayToFrobeniusCLM.comp leviSecondArrayCLM

theorem leviSecondMatrixCLM_eq_native {q : Space n → ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q z) :
    leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ q) z) = leviC q z := by
  rw [leviSecondMatrixCLM, ContinuousLinearMap.comp_apply, leviSecondArrayCLM_eq_native hq]
  rfl

theorem native_levi_holder_of_spatialDD {u : Point n → ℝ} {Q : Set (Point n)} {β C : ℝ}
    (hu : ∀ p ∈ Q, ContDiffAt ℝ 2 (fun z => u (z, p.2)) p.1)
    (hDD : HolderBound β Q (spatialDD u) C) :
    HolderBound β Q (fun p => leviC (fun z => u (z, p.2)) p.1)
      (‖leviSecondMatrixCLM (n := n)‖ * C) := by
  have hb := holderBound_continuousLinearMap hDD (leviSecondMatrixCLM (n := n))
  have he (p : Point n) (hp : p ∈ Q) :
      leviSecondMatrixCLM (spatialDD u p) = leviC (fun z => u (z, p.2)) p.1 :=
    leviSecondMatrixCLM_eq_native (hu p hp)
  refine ⟨hb.1, ?_, ?_⟩
  · intro p hp
    change ‖leviC (fun z => u (z, p.2)) p.1‖ ≤ _
    rw [← he p hp]
    exact hb.2.1 p hp
  · intro p hp q hq
    change ‖leviC (fun z => u (z, p.2)) p.1 - leviC (fun z => u (z, q.2)) q.1‖ ≤ _
    rw [← he p hp, ← he q hq]
    exact hb.2.2 p hp q hq

end Yau.NodeProofs.F01Aux

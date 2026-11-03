import Yau.Proofs.F05NonlinearInitial
import Yau.Proofs.F05IntrinsicAdd

/-! Solving the displayed zero-data correction equation gives exactly the
original nonlinear PDE on the same metric family and original domain. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_correction_recompose {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (T : ℝ)
    (p z : M.Carrier → ℝ → ℝ)
    (hP : ∀ i, C2 (F05Q A i T) (pull A i p))
    (hZ : ∀ i, C2 (F05Q A i T) (pull A i z))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hEq : F05IntrinsicLinearOperator (fun x t => Real.exp (-p x t)) h T z x t =
      F05NonlinearCorrection h T p z x t) :
    derivWithin (fun s => p x s+z x s) (Icc 0 T) t =
      Real.exp (-(p x t+z x t))*laplacian (h t) (fun y => p y t+z y t) x+
        (1-Real.exp (-(p x t+z x t)))*scalarCurvature (h t) x := by
  have hAdd := F05_intrinsic_operator_add hA h (fun x t => Real.exp (-p x t)) T p z hP hZ hx ht
  rw [hEq] at hAdd
  unfold F05NonlinearCorrection at hAdd
  dsimp only [F05IntrinsicLinearOperator] at hAdd
  nlinarith [hAdd]

theorem F05_nonlinear_correction_recompose_deriv {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (T : ℝ)
    (p z : M.Carrier → ℝ → ℝ)
    (hP : ∀ i, C2 (F05Q A i T) (pull A i p))
    (hZ : ∀ i, C2 (F05Q A i T) (pull A i z))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hEq : F05IntrinsicLinearOperator (fun x t => Real.exp (-p x t)) h T z x t =
      F05NonlinearCorrection h T p z x t) :
    deriv (fun s => p x s+z x s) t =
      Real.exp (-(p x t+z x t))*laplacian (h t) (fun y => p y t+z y t) x+
        (1-Real.exp (-(p x t+z x t)))*scalarCurvature (h t) x := by
  have hEquation := F05_nonlinear_correction_recompose hA h T p z hP hZ hx ⟨ht.1.le,ht.2.le⟩ hEq
  rwa [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)] at hEquation

end Yau.Proofs.F05Aux

import Yau.Proofs.F01SecondOrderSpatialJetMap
import Yau.Proofs.F01LeviSpatialCommutation

/-! Every spatial jet of the native Levi matrix is a fixed continuous
linear image of the scalar jet two orders higher. The generic
second-order operator theorem supplies its actual derivative identity. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def leviSpatialJetCLM (k : ℕ) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 2) => Space n) ℝ) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) (Matrix (Fin n) (Fin n) ℂ) :=
  secondOrderSpatialJetCLM (leviSecondMatrixCLM.comp secondSpatialJetCurryingCLM) k

theorem leviSpatialJetCLM_native
    {q : Space n → ℝ} {O : Set (Space n)} (hO : IsOpen O)
    (hq : ContDiffOn ℝ ∞ q O) (k : ℕ) {x : Space n} (hx : x ∈ O) :
    leviSpatialJetCLM k (iteratedFDeriv ℝ (k + 2) q x) =
      iteratedFDeriv ℝ k (fun z => leviC q z) x := by
  apply secondOrderSpatialJetCLM_native
    (leviSecondMatrixCLM.comp secondSpatialJetCurryingCLM) hO hq ?_ k hx
  intro y hy
  change leviC q y = leviSecondMatrixCLM (secondSpatialJetCurryingCLM (iteratedFDeriv ℝ 2 q y))
  rw [secondSpatialJetCurryingCLM_native]
  exact (leviSecondMatrixCLM_eq_native ((hq.contDiffAt (hO.mem_nhds hy)).of_le (by simp))).symm

end Yau.NodeProofs.F01Aux

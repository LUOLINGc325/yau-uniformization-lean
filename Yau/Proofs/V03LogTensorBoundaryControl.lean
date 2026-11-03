import Yau.Proofs.V03ClearedAmbientLogTensor
import Yau.Proofs.V03CoefficientBoundaryEnergy

/-! The actual cleared logarithmic ambient tensor has uniform entry
bounds and its original matrix seminorm is controlled by the full energy. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem ambientLogTensor_uniform_boundary_control {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F →
      (∀ θ b c, ‖ambientLogTensor d j a (F.f (circlePoint θ)) b c‖ ≤ M) ∧
      matrixDSq (fun θ => ambientLogTensor d j a (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F := by
  classical
  have hentry (bc : Fin q × Fin q) := cotangentCoefficient_uniform_boundary_control hd j
    (b := fun y => ambientLogTensor d j a y bc.1 bc.2)
    (fun x => ambientLogTensor_chart_entry_contDiffOn hd j a ha x bc.1 bc.2)
  choose C M hC hM hbound using hentry
  let C₀ : ℝ := ∑ bc, C bc
  let M₀ : ℝ := ∑ bc, M bc
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun bc _ => hC bc)
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg (fun bc _ => hM bc)
  refine ⟨C₀, M₀, hC₀, hM₀, fun F hF => ⟨?_, ?_⟩⟩
  · intro θ b c
    exact ((hbound (b, c) F hF).1 θ).trans
      (Finset.single_le_sum (fun bc _ => hM bc) (Finset.mem_univ (b, c)))
  change boundaryDSq (fun θ (bc : Fin q × Fin q) =>
    ambientLogTensor d j a (F.f (circlePoint θ)) bc.1 bc.2) ≤ _
  rw [boundaryDSq_eq_sum_singleton]
  calc
    _ ≤ ∑ bc : Fin q × Fin q, ENNReal.ofReal (C bc) * variationEnergy d j F :=
      Finset.sum_le_sum (fun bc _ => (hbound bc F hF).2)
    _ = ENNReal.ofReal C₀ * variationEnergy d j F := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun bc _ => hC bc)]

end Yau.Blueprint.V03Proof

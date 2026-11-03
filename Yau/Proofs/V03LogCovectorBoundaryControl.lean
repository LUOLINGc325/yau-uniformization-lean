import Yau.Proofs.V03ClearedAmbientLogCovector
import Yau.Proofs.V03CoefficientBoundaryEnergy

/-! The actual cleared logarithmic covector has uniform entry bounds
and its original vector seminorm is controlled by the complete energy. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem ambientLogCovector_uniform_boundary_control {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F →
      (∀ θ b, ‖ambientLogCovector d j a (F.f (circlePoint θ)) b‖ ≤ M) ∧
      boundaryDSq (fun θ => ambientLogCovector d j a (F.f (circlePoint θ))) ≤
        ENNReal.ofReal C * variationEnergy d j F := by
  classical
  have hentry (b : Fin q) := cotangentCoefficient_uniform_boundary_control hd j
    (b := fun y => ambientLogCovector d j a y b)
    (fun x => ambientLogCovector_chart_entry_contDiffOn hd j a ha x b)
  choose C M hC hM hbound using hentry
  let C₀ : ℝ := ∑ b, C b
  let M₀ : ℝ := ∑ b, M b
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun b _ => hC b)
  have hM₀ : 0 ≤ M₀ := Finset.sum_nonneg (fun b _ => hM b)
  refine ⟨C₀, M₀, hC₀, hM₀, fun F hF => ⟨?_, ?_⟩⟩
  · intro θ b
    exact ((hbound b F hF).1 θ).trans
      (Finset.single_le_sum (fun b _ => hM b) (Finset.mem_univ b))
  rw [boundaryDSq_eq_sum_singleton]
  calc
    _ ≤ ∑ b : Fin q, ENNReal.ofReal (C b) * variationEnergy d j F :=
      Finset.sum_le_sum (fun b _ => (hbound b F hF).2)
    _ = ENNReal.ofReal C₀ * variationEnergy d j F := by
      rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun b _ => hC b)]

end Yau.Blueprint.V03Proof

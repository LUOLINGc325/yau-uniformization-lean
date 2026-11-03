import Yau.Proofs.D05FrameExistence
import Yau.Proofs.D05UniformCenter
import spec.CHAIN.CONTRACTS

/-! All three clauses of the original disc-frame contract, for the supplied
immersion, with estimates for every normalized closed-disc frame. -/

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

theorem discFramesContract_all {n : ℕ} (M : ComplexManifold n) : DiscFramesContract M := by
  classical
  intro q G hG
  let chooseE : (ℂ → CotangentPoint M) → ℂ → CotangentMatrix n := fun f =>
    if hf : ExtendedCotangentDisc f then Classical.choose (original_normalized_frame_exists hG hf)
    else fun _ => 1
  refine ⟨chooseE, ?_, normalizedFrame_uniform_bivector hG,
    normalizedFrame_uniform_center hG⟩
  intro f hf
  dsimp only [chooseE]
  rw [dif_pos hf]
  exact Classical.choose_spec (original_normalized_frame_exists hG hf)

end Yau.Blueprint.D05Proof

namespace Yau.NodeProofs

theorem D05_proved : Yau.Blueprint.D05 := by
  intro n X
  exact Yau.Blueprint.D05Proof.discFramesContract_all X.manifold

theorem D05_contract_proved : Yau.BlueprintContracts.D05_contract := D05_proved

end Yau.NodeProofs

import Yau.Proofs.F01TaylorIntegral
import Yau.Proofs.F01PartialTaylorFamily

/-! Smoothness of a fixed interval integral of a genuinely jointly smooth
map. The input contains neither partial-jet regularity nor the conclusion. -/
open Set
open scoped ContDiff Interval
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_fixed_intervalIntegral_of_joint
    {U : Set E} (hU : IsOpen U) {W : Set (E × ℝ)} (hW : IsOpen W)
    {f : E × ℝ → F} (hf : ContDiffOn ℝ ∞ f W)
    (hUW : U ×ˢ Icc (0 : ℝ) 1 ⊆ W) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, f (x, t)) U :=
  (hasFTaylorSeriesUpToOn_intervalIntegral hU
    (fun _ ht => partialTaylorFamily_isTaylor hW hf hUW ht)
    (fun m => partialTaylorFamily_continuous hW hf hUW m)).contDiffOn

end Yau.NodeProofs.F01Aux

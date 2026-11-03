import Yau.Proofs.F01NativeRestartPasteIdentity
import Yau.Proofs.F01PotentialMetricSmooth

/-! Joint smoothness of the actual pasted potential proves joint
smoothness of the same explicit native pasted metric family. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_restart_paste_metricFamilySmooth
    (g : HermitianField M) (hg : MetricSmooth g) (h hR : ℝ → HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ) (W : M.Carrier → ℝ → ℝ)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hW0 : ∀ y, W y 0 = u y)
    (hpot : ∀ s ∈ Ico 0 T, ∀ y,
      gMat (h s) y = gMat g y - (s : ℂ) • ricci g y + levi (fun z => U z s) y)
    (hRpot : ∀ s ∈ Icc 0 ε, ∀ y,
      gMat (hR s) y = gMat g y - ((T + s : ℝ) : ℂ) • ricci g y + levi (fun z => W z s) y)
    (hSmooth : SmoothSpaceTime (nativePastedRestartPotential U u W T) (Icc 0 (T + ε / 2))) :
    MetricFamilySmooth (nativePastedRestartFlow h hR T) (Icc 0 (T + ε / 2)) := by
  apply metricFamilySmooth_of_potential_identity g hg _ _
    (uniqueDiffOn_Icc (by linarith : 0 < T + ε / 2)) hSmooth
  intro t ht x
  exact nativePastedRestartFlow_potential_identity g h hR U u W T ε hW0 hpot hRpot t
    ⟨ht.1, by linarith [ht.2]⟩ x

end Yau.NodeProofs.F01Aux

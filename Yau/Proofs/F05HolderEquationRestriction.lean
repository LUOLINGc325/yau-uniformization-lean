import Yau.Proofs.F05HolderCaps
import Yau.LeafProofs.L16ExpBoundaryHolderCoefficients

/-! Restricting the spatial equation region preserves its actual time fiber. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_exp_equation_mono_space {O V : Set (Space n)} {T : ℝ}
    (hOV : O ⊆ V) {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {R q : Point n → ℝ} (heq : ExpDivergenceEquation (V ×ˢ Ioc 0 T) a b R q) :
    ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q := by
  intro z hz
  have hO : {t | (z.1,t) ∈ O ×ˢ Ioc 0 T} = Ioc 0 T := by
    ext t
    simp only [mem_prod,hz.1,true_and,mem_ofPred_eq]
  have hV : {t | (z.1,t) ∈ V ×ˢ Ioc 0 T} = Ioc 0 T := by
    ext t
    simp only [mem_prod,hOV hz.1,true_and,mem_ofPred_eq]
  simpa only [timeD,hO,hV] using heq z ⟨hOV hz.1,hz.2⟩

theorem F05_cap_radius_mono (k : Option (RIdx n)) {r R : ℝ} (hr : r ≤ R) :
    F05CapOpen k r ⊆ F05CapOpen k R := fun _ hz =>
  ⟨hz.1,Metric.ball_subset_ball hr hz.2⟩

end Yau.Proofs.F05Aux

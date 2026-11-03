import Yau.Proofs.F05InteriorWideHolder
import Yau.Proofs.F05InteriorWideOscillation

/-! The actual exponential divergence equation has a uniform positive-time
interior value modulus. All constants precede the candidate and its
derivative bounds; no datum on the initial face or chart rim is supplied. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16ExpBoundaryHolderAux
variable {n : ℕ}

theorem F05_exp_wide_interior_value_holder_uniform (hn : 0 < n) {S lam upper m B s : ℝ}
    (hm : 0 < m) (hmB : m ≤ B) (hs : 0 < s)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients (Metric.ball 0 3 ×ˢ Icc 0 S) a b)
    (hR : ContDiffOn ℝ ∞ R (Metric.ball 0 3 ×ˢ Icc 0 S))
    (he : Elliptic (cylinder (Metric.closedBall 0 (11/4)) 0 S) a lam upper) :
    ∃ γ M : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < M ∧ ∀ T : ℝ, 0 < T → T ≤ S →
      ∀ q : Point n → ℝ,
      C2 (cylinder (region none (11/4)) 0 T) q →
      ContDiffOn ℝ ∞ q (F05CapOpen none 3 ×ˢ Ioc 0 T) →
      (∀ z ∈ cylinder (region none (11/4)) 0 T, m ≤ q z ∧ q z ≤ B) →
      ExpDivergenceEquation (F05CapOpen none 3 ×ˢ Ioc 0 T) a b R q →
      HolderBound γ (cylinder (region none (5/2)) s T) q M := by
  have hConstants := expDivergence_ellipticity_constants he hm hmB
  obtain ⟨γ,Cdg,hγ,hγ1,hCdg,hCore⟩ :=
    exists_interiorOscillationEstimate hn hConstants.1 hConstants.2
  obtain ⟨F,ρ,hF,hρ,hρsmall,hOsc⟩ :=
    F05_exp_wide_model_oscillation none hm hmB hCore hab hR he
  obtain ⟨M,hM,hHolder⟩ := F05_wide_interior_oscillation_holder
    (hm.trans_le hmB).le hγ hγ1 hCdg.le hF.le hρ hρsmall hs
  refine ⟨γ,M,hγ,hγ1,hM,?_⟩
  intro T hT hTS q hq hqSmooth hbound heq
  apply hHolder T hT q
  · intro z hz
    rw [abs_of_pos (hm.trans_le (hbound z hz).1)]
    exact (hbound z hz).2
  · exact hOsc T hT hTS q hq hqSmooth hbound heq

end Yau.Proofs.F05Aux

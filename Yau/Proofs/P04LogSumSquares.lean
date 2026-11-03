import Yau.Proofs.P04FiniteSumNumerator
import Yau.Proofs.P04LeviJetLimits
import Yau.Proofs.P04LogLeviPositivity

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs

/-- Actual C2 jet convergence of the same finite sums gives the positive
infinite log sum. The finite sums are never divided by their values. -/
theorem levi_log_sumSquares_posSemidef {n : ℕ}
    (U : Set (ComplexVector n)) (hU : IsOpen U)
    (f : ℕ → ComplexVector n → ℂ) (c : ℕ → ℝ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) U) (hc : ∀ i, 0 ≤ c i)
    (F : ComplexVector n → ℝ) (hF : ContDiffOn ℝ 2 F U)
    (hFpos : ∀ z ∈ U, 0 < F z)
    (hjets : ∀ q ≤ 2, ∀ z ∈ U,
      Tendsto (fun N => iteratedFDeriv ℝ q
        (fun y => ∑ i ∈ Finset.range N, c i*‖f i y‖^2) z)
        atTop (𝓝 (iteratedFDeriv ℝ q F z))) :
    ∀ z ∈ U, (leviC (fun y => Real.log (F y)) z).PosSemidef := by
  intro z hz
  have hf2 (i : ℕ) : ContDiffAt ℂ 2 (f i) z :=
    ((L17Holomorphic.contDiffOn_of_complexDiff hU (hf i)).contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hpartials (N : ℕ) : ContDiffAt ℝ 2
      (fun y => ∑ i ∈ Finset.range N, c i*‖f i y‖^2) z := by
    apply ContDiffAt.sum
    intro i _
    have hreal : ContDiffAt ℝ 2 (f i) z := (hf2 i).restrict_scalars ℝ
    have hnorm : ContDiffAt ℝ 2 (fun y => ‖f i y‖^2) z :=
      ContDiffAt.norm_sq (𝕜 := ℝ) hreal
    exact contDiffAt_const.mul hnorm
  have hF2 : ContDiffAt ℝ 2 F z := (hF z hz).contDiffAt (hU.mem_nhds hz)
  apply leviC_log_posSemidef_of_numerator hF2 (hFpos z hz)
  apply levi_numerator_posSemidef_of_jets hpartials hF2 (fun q hq => hjets q hq z hz)
  intro N
  exact finite_sumSquares_numerator N c f hc (fun i _ => hf2 i)

end Yau.Proofs.P04Aux

import Yau.Proofs.F04ZeroPastCutoff
import Yau.Proofs.F04ClassicalWeakEquation

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux Yau.LeafProofs.L16ExpBoundaryAux

theorem zeroPastCutoff_test {n : ℕ} {O : Set (Space n)} {l s δ : ℝ}
    (hδ : 0 < δ) {φ : Point n → ℝ} (hφ : Test (O ×ˢ Ioo l s) φ) :
    Test (O ×ˢ Ioo 0 s) (fun p => φ p * zeroPastCutoff δ p.2) := by
  have hLow : tsupport (fun p : Point n => φ p * zeroPastCutoff δ p.2) ⊆
      {p | δ ≤ p.2} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_snd)
    intro p hp
    by_contra h
    have ht : p.2 ≤ δ := (lt_of_not_ge h).le
    exact hp (by change φ p * zeroPastCutoff δ p.2 = 0; rw [zeroPastCutoff_zero hδ ht, mul_zero])
  refine ⟨hφ.1.mul ((zeroPastCutoff_contDiff δ).comp contDiff_snd), hφ.2.1.mul_right, ?_⟩
  intro p hp
  have hOrig := hφ.2.2 (tsupport_mul_subset_left hp)
  exact ⟨hOrig.1, hδ.trans_le (hLow hp), hOrig.2.2⟩

theorem zeroPastCutoff_test_time_deriv {n : ℕ} {φ : Point n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (δ : ℝ) (p : Point n) :
    deriv (fun t => φ (p.1, t) * zeroPastCutoff δ t) p.2 =
      deriv (fun t => φ (p.1, t)) p.2 * zeroPastCutoff δ p.2 +
        φ p * deriv (zeroPastCutoff δ) p.2 := by
  have hs : ContDiff ℝ ∞ (fun t => φ (p.1, t)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  exact deriv_mul (hs.differentiable (by simp) _) ((zeroPastCutoff_contDiff δ).differentiable (by simp) _)

theorem zeroPastCutoff_test_space_deriv {n : ℕ} {φ : Point n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (δ : ℝ) (p : Point n) (i : Yau.RIdx n) :
    d (fun x => φ (x, p.2) * zeroPastCutoff δ p.2) p.1 i =
      d (fun x => φ (x, p.2)) p.1 i * zeroPastCutoff δ p.2 := by
  have hs : ContDiff ℝ ∞ (fun x => φ (x, p.2)) :=
    hφ.comp (contDiff_id.prodMk contDiff_const)
  rw [d_mul (hs.differentiable (by simp) _) (differentiableAt_const _) i]
  simp only [d, fderiv_fun_const, Pi.zero_apply, zero_apply, mul_zero, add_zero]

end Yau.F04Proof

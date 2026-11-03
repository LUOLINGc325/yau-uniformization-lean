import Yau.Proofs.F05SpatialCutoffHolder
import Yau.LeafProofs.L16CurvedPatchCommutator

/-! The outer product retains both the native residual and the actual cutoff
commutator. Its constant is fixed before the current cylinder or solution. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05OuterResidual (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β : Space n → ℝ) (W H : Point n → ℝ) (p : Point n) : ℝ :=
  β p.1 * H p + spatialCutoffCommutator a b β W p

theorem F05OuterResidual_initial (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
    (β : Space n → ℝ) (W H : Point n → ℝ)
    (hW : ∀ x, W (x,0) = 0) (hH : ∀ x, H (x,0) = 0) (x : Space n) :
    F05OuterResidual a b β W H (x,0) = 0 := by
  unfold F05OuterResidual
  rw [hH x,mul_zero,spatialCutoffCommutator_initial_zero a b β hW x,zero_add]

theorem F05_outer_residual_budget (β : Space n → ℝ) (hβ : ContDiff ℝ ∞ β)
    (hc : HasCompactSupport β) {α M₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hM : 0 ≤ M₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Set (Point n)) (a : Point n → Mat n)
      (b : Point n → RIdx n → ℝ) (W H : Point n → ℝ) (L : ℝ),
      HolderBound α Q a M₀ → (∀ i, HolderBound α Q (fun p => b p i) M₀) →
      HolderBound α Q (fun p => (W p,spatialD W p)) L → HolderBound α Q H L →
      HolderBound α Q (F05OuterResidual a b β W H) (C*L) := by
  obtain ⟨P,hP,hCoeff⟩ := F05_smooth_cutoff_three_holder hβ hc
  let B := spatialCutoffCommutatorBudget n M₀ P P
  have hB : 0 ≤ B := by unfold B spatialCutoffCommutatorBudget; positivity
  refine ⟨1+2*P+B,by positivity,?_⟩
  intro Q a b W H L ha hb hLow hH
  have hCoeffα := hCoeff α hα hα1
  have hβQ := holderBound_mono hCoeffα.1 (subset_univ Q)
  have hProd := holderBound_mul hβQ hH
  have hLow' : HolderBound α (((univ : Set (Space n)) ×ˢ (univ : Set ℝ)) ∩ Q)
      (fun p => (W p,spatialD W p)) L := by simpa only [univ_prod_univ,univ_inter] using hLow
  have hComm := spatialCutoffCommutator_holderBound_on ha hb
    (holderBound_mono hCoeffα.2.1 (subset_univ Q))
    (holderBound_mono hCoeffα.2.2 (subset_univ Q)) (subset_univ (tsupport β)) hLow'
  have hBoth := holderBound_add hProd hComm
  apply holderBound_mono_const hBoth
  change 2*P*L+B*L ≤ (1+2*P+B)*L
  nlinarith [hLow.1]

end Yau.Proofs.F05Aux

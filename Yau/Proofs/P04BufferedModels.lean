import Yau.Proofs.P04BufferedCharts
import Yau.Proofs.P04HolomorphicNormSmooth

noncomputable section
open Set
open scoped Topology Manifold ContDiff

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- Genuine buffered multiplication makes a coordinate-smooth function
globally smooth on the model vector space, by actual support locality. -/
theorem buffered_model_smooth (a : M.Carrier) {β f : ComplexVector n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hs : tsupport β ⊆ chartTarget a)
    (hf : ContDiffOn ℝ ∞ f (chartTarget a)) :
    ContDiff ℝ ∞ (fun z => β z*f z) :=
  L18Aux.contDiff_mul_of_contDiffAt_tsupport hβ
    (fun z hz => hf.contDiffAt ((isOpen_extChartAt_target a).mem_nhds (hs hz)))

theorem buffered_model_compact {β f : ComplexVector n → ℝ}
    (hβ : HasCompactSupport β) : HasCompactSupport (fun z => β z*f z) :=
  hβ.mul_right

theorem buffered_canonical_norm_smooth (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (a : M.Carrier) {β : ComplexVector n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hs : tsupport β ⊆ chartTarget a) :
    ContDiff ℝ ∞ (fun z => β z*inChart a (canonicalNormSq g.form S) z) :=
  buffered_model_smooth a hβ hs (canonicalNormSq_smooth g S hS a)

theorem buffered_canonical_coefficient_smooth (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (a : M.Carrier) {β : ComplexVector n → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hs : tsupport β ⊆ chartTarget a) :
    ContDiff ℝ ∞ (fun z => β z*‖canonicalCoeff S a z‖^2) := by
  have hf : ContDiffOn ℝ ∞ (canonicalCoeff S a) (chartTarget a) :=
    L17Holomorphic.real_contDiffOn_of_complexDiff (isOpen_extChartAt_target a) (hS a)
  exact buffered_model_smooth a hβ hs (ContDiffOn.norm_sq (𝕜 := ℝ) hf)

end Yau.Proofs.P04Aux

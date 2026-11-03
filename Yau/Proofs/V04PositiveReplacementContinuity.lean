import Yau.Proofs.V04PositiveReplacementSpectral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-! Continuity of the same smoothing follows directly from continuous
functional calculus on a common spectral interval. -/
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem smoothMajorant_entry_continuous_of_bound {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    {A : ℝ → CotangentMatrix n} (hA : ∀ i j, Continuous (fun θ => A θ i j))
    (hHerm : ∀ θ, (A θ).IsHermitian) (hbound : ∀ θ, rectOpNorm (A θ) ≤ M)
    (i j : CotangentIndex n) : Continuous (fun θ => smoothMajorant δ (A θ) i j) := by
  have hcont : Continuous A := continuous_pi (fun i => continuous_pi (hA i))
  have hs (θ : ℝ) : spectrum ℝ (A θ) ⊆ Set.Icc (-M) M := by
    intro x hx
    have hn := IsometricContinuousFunctionalCalculus.norm_spectrum_le (A θ) hx
      (show IsSelfAdjoint (A θ) from hHerm θ)
    have haA : |x| ≤ ‖A θ‖ := by simpa only [Real.norm_eq_abs] using hn
    have ha : |x| ≤ M := haA.trans (hbound θ)
    exact abs_le.mp ha
  have hc : Continuous (fun θ => cfc (scalarMajorant δ) (A θ)) :=
    (continuousOn_cfc (CotangentMatrix n) (isCompact_Icc : IsCompact (Set.Icc (-M) M))
      (scalarMajorant δ) (scalarMajorant_contDiff hδ).continuous.continuousOn).comp_continuous
        hcont (fun θ => ⟨hHerm θ, hs θ⟩)
  have heq : (fun θ => smoothMajorant δ (A θ)) =
      (fun θ => cfc (scalarMajorant δ) (A θ)) := by
    funext θ
    exact smoothMajorant_eq_cfc δ (A θ) (hHerm θ)
  rw [show (fun θ => smoothMajorant δ (A θ) i j) =
    (fun θ => (cfc (scalarMajorant δ) (A θ)) i j) from congrArg (fun f θ => f θ i j) heq]
  exact (hc.matrix_elem i j)

theorem bivectorCost_continuous {A J : ℝ → CotangentMatrix n}
    (hA : ∀ i j, Continuous (fun θ => A θ i j))
    (hJ : ∀ i j, Continuous (fun θ => J θ i j)) :
    Continuous (fun θ => bivectorCost (A θ) (J θ)) := by
  unfold bivectorCost
  apply continuous_const.mul
  apply Complex.continuous_re.comp
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro l _
  exact (((hJ i j).mul (hJ k l).star).mul (hA k i)).mul (hA l j)

end Yau.Blueprint.V04Proof.PositiveReplacementAux

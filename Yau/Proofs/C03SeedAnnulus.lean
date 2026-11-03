import Yau.Proofs.C03SeedDbarBounds
import Yau.Proofs.C03SheetPole

/-! The actual Dolbeault source is supported on the fixed seed annulus,
where every smaller target pole is identically zero. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def scalarDbarVector (f : ComplexVector n → ℂ) (z : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (fun i => wirtBar f z (stdVec i))

theorem scalarDbarVector_zero_of_germ (f : ComplexVector n → ℂ) (z : ComplexVector n)
    (hg : f =ᶠ[𝓝 z] fun _ => (0 : ℂ)) : scalarDbarVector f z = 0 := by
  have hD : fderiv ℝ f z = 0 := by
    rw [hg.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z).fderiv
  ext i
  change wirtBar f z (stdVec i) = 0
  simp only [wirtBar, hD, ContinuousLinearMap.zero_apply, mul_zero, add_zero]

theorem sheetSeed_annular_source (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℂ ∞ θ O) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 : ComplexVector n) (hsub : closedBall w0 δ ⊆ W)
    (z : ComplexVector n) :
    scalarDbarVector (sheetSeed O θ δ hδ η w0) z = 0 ∨
      z ∈ σ '' closedBall w0 δ ∧ δ / 2 ≤ ‖θ z - w0‖ ∧ ‖θ z - w0‖ ≤ δ := by
  classical
  by_cases hz : z ∈ O
  · have hd : DifferentiableAt ℂ θ z :=
      (hθ.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    by_cases hout : ‖θ z - w0‖ ≤ δ
    · by_cases hin : δ / 2 ≤ ‖θ z - w0‖
      · exact Or.inr ⟨⟨θ z, by simpa only [mem_closedBall, dist_eq_norm] using hout, hστ z hz⟩,
          hin, hout⟩
      · left
        have hzero := seedCutoffDbar_zero_inner δ hδ (θ z - w0)
          (by simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hin)
        ext i
        change wirtBar (sheetSeed O θ δ hδ η w0) z (stdVec i) = 0
        rw [sheetSeed_wirtBar O hO θ δ hδ η w0 z (stdVec i) hz hd,
          wirtBar_direction_coordinates]
        have hc (j : Fin n) : wirtBar (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ))
            (θ z - w0) (stdVec j) = 0 := congrArg (fun v : ComplexVector n => v j) hzero
        simp only [hc, mul_zero, Finset.sum_const_zero]
    · left
      have hzero := seedCutoffDbar_zero_outside δ hδ (θ z - w0)
        (by simpa only [mem_closedBall, dist_zero_right] using hout)
      ext i
      change wirtBar (sheetSeed O θ δ hδ η w0) z (stdVec i) = 0
      rw [sheetSeed_wirtBar O hO θ δ hδ η w0 z (stdVec i) hz hd,
        wirtBar_direction_coordinates]
      have hc (j : Fin n) : wirtBar (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ))
          (θ z - w0) (stdVec j) = 0 := congrArg (fun v : ComplexVector n => v j) hzero
      simp only [hc, mul_zero, Finset.sum_const_zero]
  · left
    apply scalarDbarVector_zero_of_germ
    apply sheetExtension_zero_germ O W σ θ hσ hσW hστ _
      (translatedTargetSeed_hasCompactSupport δ hδ η w0)
      ((translatedTargetSeed_tsupport_subset δ hδ η w0).trans hsub)
    rintro ⟨w, hw, rfl⟩
    exact hz (hσW (hsub (translatedTargetSeed_tsupport_subset δ hδ η w0 hw)))

theorem sheetPole_zero_on_seed_annulus (O : Set (ComplexVector n))
    (θ : ComplexVector n → ComplexVector n) (δp : ℝ) (hδp : 0 < δp)
    (m : ℕ) (w0 : ComplexVector n) (j : ℕ) (z : ComplexVector n)
    (hz : δp < ‖θ z - w0‖) : sheetPole O θ δp hδp m w0 j z = 0 := by
  classical
  by_cases hzo : z ∈ O
  · change (if z ∈ O then _ else _) = _
    rw [if_pos hzo]
    exact (TargetPole.translatedPole_zero_germ_outside δp hδp m j w0
      (by simpa only [mem_closedBall, dist_eq_norm] using hz.not_ge)).eq_of_nhds
  · simp only [sheetPole, sheetExtension, if_neg hzo]

end Yau.Proofs.C03Aux

import Yau.Proofs.C03TargetSeed
import Yau.Proofs.C03ScalarChartCoefficients
import Yau.Proofs.C03CovectorCoordinates

/-! The same compact scalar seed on the genuine sheet has its exact
holomorphic first jet and the actual L14 source coefficients. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux L17Aux Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n => WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

def sheetSeed (O : Set (ComplexVector n)) (θ : ComplexVector n → ComplexVector n)
    (δ : ℝ) (hδ : 0 < δ) (η : Covector n) (w0 : ComplexVector n) :
    ComplexVector n → ℂ :=
  sheetExtension O θ (fun w => targetSeed δ hδ η (w - w0))

theorem sheetSeed_smooth_compact (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℝ ∞ θ O) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 : ComplexVector n) (hsub : closedBall w0 δ ⊆ W) :
    ContDiff ℝ ∞ (sheetSeed O θ δ hδ η w0) ∧
      HasCompactSupport (sheetSeed O θ δ hδ η w0) ∧
      tsupport (sheetSeed O θ δ hδ η w0) ⊆ σ '' closedBall w0 δ := by
  have hs := (translatedTargetSeed_tsupport_subset δ hδ η w0).trans hsub
  have hc := translatedTargetSeed_hasCompactSupport δ hδ η w0
  exact ⟨sheetExtension_contDiff O W hO σ θ hσ hσW hστ hθ _
      (translatedTargetSeed_contDiff δ hδ η w0) hc hs,
    sheetExtension_compactSupport O W σ θ hσ hσW hστ _ hc hs,
    (sheetExtension_tsupport_subset O W σ θ hσ hσW hστ _ hc hs).trans
      (image_mono (translatedTargetSeed_tsupport_subset δ hδ η w0))⟩

theorem sheetSeed_norm_le (O : Set (ComplexVector n))
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 z : ComplexVector n) :
    ‖sheetSeed O θ δ hδ η w0 z‖ ≤ ‖η‖ * δ := by
  classical
  by_cases hz : z ∈ O
  · simpa only [sheetSeed, sheetExtension, if_pos hz] using targetSeed_norm_le δ hδ η (θ z - w0)
  · simp only [sheetSeed, sheetExtension, if_neg hz, norm_zero]
    positivity

theorem sheetSeed_holomorphic_germ (O : Set (ComplexVector n)) (hO : IsOpen O)
    (h0 : (0 : ComplexVector n) ∈ O) (θ : ComplexVector n → ComplexVector n)
    (hθ : ContinuousAt θ 0) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 : ComplexVector n) (hθ0 : θ 0 = w0) :
    sheetSeed O θ δ hδ η w0 =ᶠ[𝓝 (0 : ComplexVector n)] fun z => η (θ z - w0) := by
  have ht : Tendsto (fun z => θ z - w0) (𝓝 (0 : ComplexVector n)) (𝓝 0) := by
    simpa only [hθ0, sub_self] using hθ.sub_const w0
  exact (sheetExtension_eq_comp_germ O hO θ _ 0 h0).trans
    (ht.eventually (targetSeed_germ δ hδ η))

theorem sheetSeed_zero_and_derivative (O : Set (ComplexVector n)) (hO : IsOpen O)
    (h0 : (0 : ComplexVector n) ∈ O) (θ : ComplexVector n → ComplexVector n)
    (hθ : DifferentiableAt ℂ θ 0) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 : ComplexVector n) (hθ0 : θ 0 = w0) :
    sheetSeed O θ δ hδ η w0 0 = 0 ∧
      fderiv ℂ (sheetSeed O θ δ hδ η w0) 0 = η.comp (fderiv ℂ θ 0) := by
  have heq := sheetSeed_holomorphic_germ O hO h0 θ hθ.continuousAt δ hδ η w0 hθ0
  constructor
  · rw [heq.eq_of_nhds, hθ0, sub_self, map_zero]
  · rw [heq.fderiv_eq]
    exact (η.hasFDerivAt.comp 0 (hθ.hasFDerivAt.sub_const w0)).fderiv

def seedCutoffDbar (δ : ℝ) (hδ : 0 < δ) (w : ComplexVector n) : ComplexVector n :=
  WithLp.toLp 2 (fun i => wirtBar (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ)) w (stdVec i))

theorem sheetSeed_wirtBar (O : Set (ComplexVector n)) (hO : IsOpen O)
    (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 z v : ComplexVector n) (hz : z ∈ O)
    (hθ : DifferentiableAt ℂ θ z) :
    wirtBar (sheetSeed O θ δ hδ η w0) z v =
      η (θ z - w0) *
        wirtBar (fun x => ((seedCutoff δ hδ x : ℝ) : ℂ)) (θ z - w0) (fderiv ℂ θ z v) := by
  have heq : sheetSeed O θ δ hδ η w0 =ᶠ[𝓝 z]
      fun x => targetSeed δ hδ η (θ x - w0) :=
    sheetExtension_eq_comp_germ O hO θ _ z hz
  have hder := heq.fderiv_eq (𝕜 := ℝ)
  unfold wirtBar
  rw [hder]
  change wirtBar (fun x => targetSeed δ hδ η (θ x - w0)) z v = _
  rw [wirtBar_comp_complex_differentiable _ _ z v (hθ.sub_const w0)
    ((targetSeed_contDiff δ hδ η).differentiable (by simp) _)]
  change wirtBar (fun w => ((seedCutoff δ hδ w : ℝ) : ℂ) * η w) (θ z - w0) _ = _
  have hc : DifferentiableAt ℝ (fun w : ComplexVector n => ((seedCutoff δ hδ w : ℝ) : ℂ))
      (θ z - w0) := by
    have hcs : ContDiff ℝ ∞ (fun w : ComplexVector n => ((seedCutoff δ hδ w : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (seedCutoff δ hδ).contDiff
    exact hcs.differentiable (by simp) _
  rw [wirtBar_mul_rule (fun w : ComplexVector n => ((seedCutoff δ hδ w : ℝ) : ℂ))
    (η : ComplexVector n → ℂ) _ _ hc (η.differentiableAt.restrictScalars ℝ),
    wirtBar_eq_zero_of_complex_differentiable _ _ _ η.differentiableAt, mul_zero, add_zero]
  simp only [fderiv_sub_const, mul_comm, wirtBar]

theorem sheetSeed_actual_source_vector (hn : 1 ≤ n) (O : Set (ComplexVector n))
    (hO : IsOpen O) (θ : ComplexVector n → ComplexVector n) (δ : ℝ) (hδ : 0 < δ)
    (η : Covector n) (w0 z : ComplexVector n) (hz : z ∈ O)
    (hθ : DifferentiableAt ℂ θ z) :
    WithLp.toLp 2 (fun i => BundleDbar.coefficients (r := 1)
      (Yau.Proofs.P04Aux.CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (scalarSeedDbar hn (sheetSeed O θ δ hδ η w0)) z
      (chartPt (M := ComplexEuclideanManifold n hn) z z) (fun _ => i) 0) =
      η (θ z - w0) • matrixFiberMap (linearMatrix (fderiv ℂ θ z))ᴴ
        (seedCutoffDbar δ hδ (θ z - w0)) := by
  ext i
  rw [scalarSeedDbar_centered_coefficient, sheetSeed_wirtBar O hO θ δ hδ η w0 z (stdVec i) hz hθ,
    wirtBar_direction_coordinates]
  rfl

end Yau.Proofs.C03Aux

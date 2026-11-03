import Yau.Proofs.C03SeedAnnulus
import Yau.Proofs.C03SeedInverseBound
import Yau.Proofs.C03SourceIntegralSupport

/-! The actual sheet seed and smaller sheet poles satisfy the original
smooth L14 source integral estimate with uniform constants. -/

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L14Aux L17Aux Yau.NodeProofs.E01Aux
open Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem sheetSeed_source_integral_bound (hn : 1 ≤ n)
    (O W : Set (ComplexVector n)) (hO : IsOpen O)
    (σ θ : ComplexVector n → ComplexVector n) (hσ : ContinuousOn σ W)
    (hσW : MapsTo σ W O) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (hθ : ContDiffOn ℂ ∞ θ O) (hθW : MapsTo θ O W)
    (δs δp : ℝ) (hδs : 0 < δs) (hδp : 0 < δp) (hsep : δp < δs / 2)
    (η : Covector n) (w0 : ComplexVector n) (hsub : closedBall w0 δs ⊆ W)
    (R d U G : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hU : 0 ≤ U) (hG : 0 ≤ G)
    (hη : ‖η‖ ≤ Real.sqrt U)
    (hcut : ∀ w : ComplexVector n, ‖seedCutoffDbar δs hδs w‖ ≤ G)
    (hT : σ '' closedBall w0 δs ⊆ closedBall (0 : ComplexVector n) R)
    (Ht Hs : ComplexVector n → Herm n)
    (hHt : ∀ w ∈ W, (Ht w).PosDef)
    (hlo : ∀ w ∈ W, HermLE ((d : ℂ) • (1 : Herm n)) (Ht w))
    (hJ : ∀ z ∈ O, IsUnit (linearMatrix (fderiv ℂ θ z)).det)
    (hcong : ∀ z ∈ O, Hs z =
      (linearMatrix (fderiv ℂ θ z))ᴴ * Ht (θ z) * linearMatrix (fderiv ℂ θ z))
    (φ : ComplexVector n → ℝ) (m : ℕ)
    (hφ : ∀ z ∈ σ '' closedBall w0 δs, 0 ≤ φ z)
    (hPSD : ∀ j z, (leviC (fun w => φ w + sheetPole O θ δp hδp m w0 j w) z).PosSemidef)
    (hLevi : ∀ j z, z ∈ σ '' closedBall w0 δs →
      HermLE (Hs z) (leviC (fun w => φ w + sheetPole O θ δp hδp m w0 j w) z)) :
    ∀ j, inverseCurvatureIntegral (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn)
      (fun z => φ z + sheetPole O θ δp hδp m w0 j z)
      (scalarSeedDbar hn (sheetSeed O θ δs hδs η w0)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * (U * δs ^ 2) * (G ^ 2 / d)) *
        (volume : Measure (ComplexVector n)).real (closedBall 0 R)) := by
  let S : Set (ComplexVector n) := {z | z ∈ O ∧ δs / 2 ≤ ‖θ z - w0‖ ∧ ‖θ z - w0‖ ≤ δs}
  have hST : S ⊆ σ '' closedBall w0 δs := by
    intro z hz
    exact ⟨θ z, by simpa only [mem_closedBall, dist_eq_norm] using hz.2.2, hστ z hz.1⟩
  intro j
  apply SourceIntegral.inverseCurvatureIntegral_le_coefficient_support hn R
    ((2 : ℝ) ^ n * (U * δs ^ 2) * (G ^ 2 / d)) hR (by positivity)
    (fun z => φ z + sheetPole O θ δp hδp m w0 j z)
    (scalarSeedDbar hn (sheetSeed O θ δs hδs η w0)) S (hST.trans hT)
    (flat_weightedNakano_of_source_levi hn _ (hPSD j))
  · intro z hz
    have hD : DifferentiableAt ℂ θ z :=
      (hθ.contDiffAt (hO.mem_nhds hz.1)).differentiableAt (by simp)
    apply sheetSeed_inverse_bound hn _ O hO θ δs hδs η w0 z hz.1 hD hz.2.2
      (Ht (θ z)) (hHt _ (hθW hz.1)) d U G hd hU hG hη (hlo _ (hθW hz.1))
      (hcut _) (hJ z hz.1)
    rw [← hcong z hz.1]
    exact hLevi j z (hST hz)
  · intro z hz
    rw [sheetPole_zero_on_seed_annulus O θ δp hδp m w0 j z (hsep.trans_le hz.2.1), add_zero]
    exact hφ z (hST hz)
  · intro z hz i α
    have hv : scalarDbarVector (sheetSeed O θ δs hδs η w0) z = 0 := by
      rcases sheetSeed_annular_source O W hO σ θ hσ hσW hστ hθ δs hδs η w0 hsub z with H | H
      · exact H
      · exfalso
        apply hz
        refine ⟨?_, H.2⟩
        rcases H.1 with ⟨w, hw, rfl⟩
        exact hσW (hsub hw)
    have hα : α = 0 := Subsingleton.elim _ _
    subst α
    rw [scalarSeedDbar_centered_coefficient]
    exact congrArg (fun v : ComplexVector n => v i) hv

end Yau.Proofs.C03Aux

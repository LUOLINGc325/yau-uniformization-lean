import Yau.Proofs.P04CommonWeightedSolution
import Yau.Proofs.P04UniformInverseIntegral
import Yau.Proofs.P04CutoffSupportAnnulus
import Yau.Proofs.P04PoleStrictWeight
import Yau.Proofs.P04LeviAlgebra
import Yau.Proofs.P04NonzeroCorrection

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Matrix ComplexOrder ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs BundleDbar
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual weighted canonical interpolation. The cutoff, one uniform
regularization scalar, uniform inverse-curvature bound, common solution,
holomorphic representative and nonvanishing are all constructed here. -/
theorem canonical_weighted_interpolation (g : SmoothMetric M)
    {ψ : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (p : M.Carrier) :
    ∃ k : ℝ, 0 < k ∧ ∃ S : CanonicalSection M,
      IsHolomorphicCanonical S ∧ S p ≠ 0 ∧
      (∫⁻ x, ENNReal.ofReal (canonicalNormSq g.form S x*Real.exp (-(k*ψ x))) ∂μ) < ⊤ := by
  obtain ⟨ρ,hρ,hsmall,htarget,χ,hχ,hcχ,hsupp,hone,hχbounds⟩ := exists_pole_cutoff p
  have hs : tsupport χ ⊆ chartTarget p := pole_cutoff_support_in_chart p hρ htarget hsupp
  have hball : Metric.ball (chartPt p p) ρ ⊆ chartTarget p :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (by linarith : ρ ≤ 2*ρ))).trans htarget
  have hc : (0 : ℝ) < (n : ℝ)+1 := by positivity
  obtain ⟨k,hk,hweights⟩ := exists_uniform_strict_pole_weights p hχ hcχ hρ htarget hsupp hone hc.le hψ
  have horder (ε : ℝ) (hε : 0 < ε) (hερ : ε ≤ ρ) (x : M.Carrier) :
      (levi (regularizedPoleWeight p χ ((n : ℝ)+1) k ψ ε) x-levi ψ x).PosSemidef := by
    rw [pole_weight_levi_sub_background p hχ hcχ hs _ k hψ.1 hε]
    exact (hweights ε hε hερ).1 x
  have hN (ε : ℝ) (hε : 0 < ε) (hερ : ε ≤ ρ) := (hweights ε hε hερ).2.2
  obtain ⟨B,hB,hBbound⟩ := exists_uniform_pole_inverse_integral_bound g μ hμ p hχ ((n : ℝ)+1) k hψ hρ
    (fun z hz => htarget hz.1) (cutoffDbar p χ) (cutoffDbar_smooth p hχ hcχ hs)
    (cutoffDbar_compact p hcχ hs) (cutoffDbar_support_in_annulus p hcχ hs hρ hsupp hone) hN horder
  let Φ : M.Carrier → ℝ := fun x => k*ψ x
  have hΦ : SmoothFn Φ := fun a => contDiffOn_const.mul (hψ.1 a)
  let P : ℕ → M.Carrier → ℝ := fun j => globalPolePart p χ ((n : ℝ)+1) (poleEpsilon ρ j)
  have hP (j : ℕ) : SmoothFn (P j) := globalPolePart_smooth p hχ hcχ hs _ (poleEpsilon_pos hρ j)
  have hcP (j : ℕ) : HasCompactSupport (P j) := globalPolePart_compact p hχ hcχ hs _ (poleEpsilon_pos hρ j)
  have hnonpos (j : ℕ) (x : M.Carrier) : P j x ≤ 0 := globalPolePart_nonpos p
    (fun z => (hχbounds z).1) hc.le hρ hsmall hsupp (poleEpsilon_pos hρ j) (poleEpsilon_le hρ j) x
  have hanti (x : M.Carrier) : Antitone (fun j => P j x) := by
    intro i j hij
    exact globalPolePart_mono p (fun z => (hχbounds z).1) hc.le
      (poleEpsilon_pos hρ j) (poleEpsilon_antitone hρ hij) x
  have hNj (j : ℕ) : WeightedNakanoNonnegative (r := 1) (CanonicalCoefficients M) flatMetric
      (fun x => Φ x+P j x) := hN _ (poleEpsilon_pos hρ j) (poleEpsilon_le hρ j)
  obtain ⟨u,hdu,hu,hnorm⟩ := exists_common_weighted_solution g μ hμ Φ hΦ P hP hcP hnonpos hanti hNj
    (cutoffDbar p χ) (cutoffDbar_weightedL2 g μ hμ Φ hΦ p hχ hcχ hs)
    (cutoff_weaklyClosed p hχ hcχ hs) B hB
    (fun j => hBbound _ (poleEpsilon_pos hρ j) (poleEpsilon_le hρ j))
  obtain ⟨S,hS,hSp,hfinite⟩ := canonical_nonzero_of_uniform_correction g μ hμ p hχ hcχ hs hρ hball hone
    k hψ.1 u hu hdu (ENNReal.ofReal B) ENNReal.ofReal_lt_top hnorm
  exact ⟨k,by linarith,S,hS,hSp,hfinite⟩

end Yau.Proofs.P04Aux

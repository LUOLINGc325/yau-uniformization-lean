import Yau.Proofs.F04EuclideanSupportedCutoff
import Yau.Proofs.F04LocalCauchyParticular
import Yau.Proofs.F04SmoothInitialGrowth

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- A smooth forced particular solution on an actual compact buffer is
 produced internally: choose a genuine cutoff, construct full-space data,
 apply the exact native Cauchy producer and prove its compact O(t) growth.
 No coefficient extension, solver, initial compatibility or time-growth
 conclusion is supplied as an extra premise. -/
theorem local_zeroInitial_particular_exists
    {n : ℕ} (hn : 0 < n) {O : Set (Space n)} (hO : IsOpen O)
    (K : Set (Space n)) (hK : IsCompact K) (hKO : K ⊆ O)
    {S lam upper : ℝ} (hS : 0 < S)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S))
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper) :
    ∃ (W : Set (Space n)) (p : Point n → ℝ), IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧
      ContDiffOn ℝ ∞ p (univ ×ˢ Icc 0 S) ∧ (∀ x, p (x, 0) = 0) ∧
      (∃ B : ℝ, ∀ q ∈ univ ×ˢ Icc 0 S, |p q| ≤ B) ∧
      (∀ q ∈ W ×ˢ Icc 0 S, linearOp (W ×ˢ Icc 0 S) a b p q = f q) ∧
      ∀ L : Set (Space n), IsCompact L →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ t ∈ Icc 0 S, |p (x, t)| ≤ C * t := by
  obtain ⟨χ, W, hχ, hcχ, hχO, hW, hKW, hWO, hχone, hχrange⟩ :=
    exists_euclidean_supported_smooth_cutoff K O hK hO hKO
  have hEllχ : Elliptic (tsupport χ ×ˢ Icc 0 S) a lam upper :=
    elliptic_mono hEll (prod_mono hχO (Subset.refl _))
  obtain ⟨p, hp, h0, hB, hEq⟩ := localCauchy_particular_of_spatial_cutoff hn hO hS
    hχ hcχ hχO hχrange hχone hSmooth hf hEllχ
  refine ⟨W, p, hW, hKW, hWO, hp, h0, hB, hEq, ?_⟩
  intro L hL
  exact smooth_zeroInitial_compact_growth hS hp (fun x _ => h0 x) L hL (subset_univ L)

end Yau.F04Proof

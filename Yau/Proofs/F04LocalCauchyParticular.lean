import Yau.Proofs.F04SpatialCauchyExtension
import Yau.LeafProofs.L16Cauchy

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- The native exact Cauchy producer is applied to constructed full-space
 data. It produces an actual smooth zero-initial particular solution for
 the original local forcing on the region where the spatial cutoff is one. -/
theorem localCauchy_particular_of_spatial_cutoff
    {n : ℕ} (hn : 0 < n) {O W : Set (Space n)} (hO : IsOpen O)
    {S lam upper : ℝ} (hS : 0 < S)
    {χ : Space n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ O) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hχone : ∀ x ∈ W, χ x = 1)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S))
    (hEll : Elliptic (tsupport χ ×ˢ Icc 0 S) a lam upper) :
    ∃ p : Point n → ℝ, ContDiffOn ℝ ∞ p (univ ×ˢ Icc 0 S) ∧
      (∀ x, p (x, 0) = 0) ∧ (∃ B : ℝ, ∀ q ∈ univ ×ˢ Icc 0 S, |p q| ≤ B) ∧
      ∀ q ∈ W ×ˢ Icc 0 S, linearOp (W ×ˢ Icc 0 S) a b p q = f q := by
  have hData := spatialCauchyExtension_properties hO hχ hcχ hχO hχrange hSmooth hf hEll
  obtain ⟨p, hp, h0, hB, hEq⟩ := zeroInitialCauchySolution n hn S (min lam 1) (max upper 1) hS
    (spatialCauchyPrincipal χ a) (spatialCauchyDrift χ b) (spatialCauchySource χ f)
    hData.1 hData.2.1 hData.2.2.1 hData.2.2.2.1
  refine ⟨p, hp, h0, hB, ?_⟩
  intro q hq
  have he := hEq q ⟨mem_univ _, hq.2⟩
  have hm := hData.2.2.2.2 q (hχone q.1 hq.1)
  have hW : {t : ℝ | (q.1, t) ∈ W ×ˢ Icc 0 S} = Icc 0 S := by
    ext t
    simp only [mem_setOf_eq, mem_prod, hq.1, true_and]
  have hU : {t : ℝ | (q.1, t) ∈ (univ : Set (Space n)) ×ˢ Icc 0 S} = Icc 0 S := by
    ext t
    simp only [mem_setOf_eq, mem_prod, mem_univ, true_and]
  have hTime : timeD (W ×ˢ Icc 0 S) p q = timeD (univ ×ˢ Icc 0 S) p q := by
    simp only [timeD, hW, hU]
  unfold linearOp at he ⊢
  rw [hm.1, hm.2.1, hm.2.2] at he
  rw [hTime]
  exact he

end Yau.F04Proof

import Yau.Proofs.F04SpatialCutoffSmooth
import Yau.LeafProofs.L16HolderExtension

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

def spatialCauchyPrincipal {n : ℕ} (χ : Space n → ℝ) (a : Point n → Mat n) (p : Point n) : Mat n :=
  χ p.1 • a p + (1 - χ p.1) • (1 : Mat n)

def spatialCauchyDrift {n : ℕ} (χ : Space n → ℝ) (b : Point n → RIdx n → ℝ)
    (p : Point n) (i : RIdx n) : ℝ := χ p.1 * b p i

def spatialCauchySource {n : ℕ} (χ : Space n → ℝ) (f : Point n → ℝ) (p : Point n) : ℝ :=
  χ p.1 * f p

/-- Actual full-space Cauchy data are constructed by a spatial cutoff.
 Closed-face smoothness follows from spatial zero germs, ellipticity is
 the genuine convex combination with the identity, and the exterior is
 exactly Euclidean heat with zero forcing. -/
theorem spatialCauchyExtension_properties
    {n : ℕ} {O : Set (Space n)} (hO : IsOpen O) {S lam upper : ℝ}
    {χ : Space n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ O) (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S))
    (hEll : Elliptic (tsupport χ ×ˢ Icc 0 S) a lam upper) :
    SmoothCoefficients (univ ×ˢ Icc 0 S) (spatialCauchyPrincipal χ a) (spatialCauchyDrift χ b) ∧
    ContDiffOn ℝ ∞ (spatialCauchySource χ f) (univ ×ˢ Icc 0 S) ∧
    Elliptic (univ ×ˢ Icc 0 S) (spatialCauchyPrincipal χ a) (min lam 1) (max upper 1) ∧
    (∃ K : Set (Space n), IsCompact K ∧ ∀ x ∉ K, ∀ t ∈ Icc 0 S,
      spatialCauchyPrincipal χ a (x, t) = 1 ∧ spatialCauchyDrift χ b (x, t) = 0 ∧
        spatialCauchySource χ f (x, t) = 0) ∧
    ∀ p : Point n, χ p.1 = 1 →
      spatialCauchyPrincipal χ a p = a p ∧ spatialCauchyDrift χ b p = b p ∧
        spatialCauchySource χ f p = f p := by
  have hχJ : ContDiff ℝ ∞ (fun p : Point n => χ p.1) := hχ.comp contDiff_fst
  have hPA : ContDiffOn ℝ ∞ (spatialCauchyPrincipal χ a) (univ ×ˢ Icc 0 S) :=
    (spatialCutoff_smul_contDiffOn hO hχ hχO hSmooth.1).add
      ((contDiffOn_const.sub hχJ.contDiffOn).smul contDiffOn_const)
  have hBD (i : RIdx n) : ContDiffOn ℝ ∞ (fun p => spatialCauchyDrift χ b p i) (univ ×ˢ Icc 0 S) := by
    simpa only [spatialCauchyDrift, smul_eq_mul] using
      spatialCutoff_smul_contDiffOn hO hχ hχO (hSmooth.2 i)
  have hSF : ContDiffOn ℝ ∞ (spatialCauchySource χ f) (univ ×ˢ Icc 0 S) := by
    change ContDiffOn ℝ ∞ (fun p => χ p.1 * f p) (univ ×ˢ Icc 0 S)
    simpa only [smul_eq_mul] using spatialCutoff_smul_contDiffOn hO hχ hχO hf
  have hEA : Elliptic (univ ×ˢ Icc 0 S) (spatialCauchyPrincipal χ a) (min lam 1) (max upper 1) :=
    elliptic_cutoff_extension (χ := fun p => χ p.1) (φ := id) hEll
      (fun p _ => hχrange p.1) (fun p hp hn => ⟨subset_tsupport χ hn, hp.2⟩)
  refine ⟨⟨hPA, hBD⟩, hSF, hEA, ⟨tsupport χ, hcχ, ?_⟩, ?_⟩
  · intro x hx t _ht
    have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
    refine ⟨?_, ?_, ?_⟩
    · simp only [spatialCauchyPrincipal, hz, zero_smul, sub_zero, one_smul, zero_add]
    · funext i
      simp only [spatialCauchyDrift, hz, zero_mul, Pi.zero_apply]
    · simp only [spatialCauchySource, hz, zero_mul]
  · intro p hp
    refine ⟨?_, ?_, ?_⟩
    · simp only [spatialCauchyPrincipal, hp, one_smul, sub_self, zero_smul, add_zero]
    · funext i
      simp only [spatialCauchyDrift, hp, one_mul]
    · simp only [spatialCauchySource, hp, one_mul]

end Yau.F04Proof

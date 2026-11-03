import Yau.Proofs.F04ZeroPastIntegral

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

/-- Spatial weak differentiation commutes with the genuine zero-past
 extension. The cutoff proof uses the actual positive-cylinder L2 data. -/
theorem zeroPast_weakGradient {n : ℕ} {O : Set (Space n)} (hO : MeasurableSet O)
    {l s : ℝ} (hl : l ≤ 0) {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hu : MemLp u 2 (productVolume O (Ioo 0 s)))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (productVolume O (Ioo 0 s)))
    (hWeak : WeakGradient O (Ioo 0 s) u G) :
    WeakGradient O (Ioo l s) (zeroPast u) (fun p i => zeroPast (fun q => G q i) p) := by
  intro φ hφ i
  have hφ2 : MemLp φ 2 (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
  have hDφ := test_spatialDerivative hφ i
  have hDφ2 : MemLp (fun p => d (fun x => φ (x, p.2)) p.1 i) 2
      (productVolume O (Ioo 0 s)) := by
    rw [productVolume_eq_restrict]
    exact (hDφ.1.continuous.memLp_of_hasCompactSupport hDφ.2.1).restrict _
  have hLeft := tendsto_integral_zeroPastCutoff hO (hu.integrable_mul hDφ2)
  have hRight := (tendsto_integral_zeroPastCutoff hO ((hG i).integrable_mul hφ2)).neg
  have hEq (j : ℕ) :
      (∫ p, (u p * d (fun x => φ (x, p.2)) p.1 i) * zeroPastCutoff (1 / ((j : ℝ) + 1)) p.2
        ∂productVolume O (Ioo 0 s)) =
      -(∫ p, (G p i * φ p) * zeroPastCutoff (1 / ((j : ℝ) + 1)) p.2
        ∂productVolume O (Ioo 0 s)) := by
    have hh := hWeak _ (zeroPastCutoff_test (by positivity : 0 < 1 / ((j : ℝ) + 1)) hφ) i
    simp_rw [zeroPastCutoff_test_space_deriv hφ.1] at hh
    simpa only [mul_assoc] using hh
  have hLimit : (∫ p, u p * d (fun x => φ (x, p.2)) p.1 i ∂productVolume O (Ioo 0 s)) =
      -(∫ p, G p i * φ p ∂productVolume O (Ioo 0 s)) := by
    exact tendsto_nhds_unique hLeft (hRight.congr' (Eventually.of_forall (fun j => (hEq j).symm)))
  rw [zeroPast_pairing_integral O hl u (fun p => d (fun x => φ (x, p.2)) p.1 i),
    zeroPast_pairing_integral O hl (fun p => G p i) φ]
  exact hLimit

end Yau.F04Proof

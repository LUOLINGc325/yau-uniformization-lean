import Yau.Proofs.C03ScalarL14
import Yau.Proofs.C03ScalarCoefficients
import Yau.Proofs.C03ScalarRecovery

/-! The genuine smooth L14 solution gives one entire scalar complement
and the same correction bound for every actual regularized pole weight. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff Manifold Matrix ComplexOrder ENNReal
namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L14Aux Yau.Proofs.P04Aux BundleDbar
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem exists_scalar_common_entire_solution (hn : 1 ≤ n)
    (f : ComplexVector n → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (p : ℕ → ComplexVector n → ℝ) (hp : ∀ j, ContDiff ℝ ∞ (p j))
    (hpc : ∀ j, HasCompactSupport (p j)) (hp0 : ∀ j z, p j z ≤ 0)
    (hpm : ∀ z, Antitone (fun j => p j z))
    (hcurv : ∀ j z, (leviC (fun w => φ w + p j w) z).PosSemidef)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ j, inverseCurvatureIntegral (r := 1)
      (CanonicalCoefficients (ComplexEuclideanManifold n hn))
      (FlatComplete.euclideanCompleteMetric n hn).form flatMetric
      (FlatComplete.euclideanVolume n hn) (fun z => φ z + p j z)
      (scalarSeedDbar hn f) ≤ ENNReal.ofReal B) :
    ∃ h : ComplexVector n → ℂ, Differentiable ℂ h ∧
      ∀ j, (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-(φ z + p j z)))
        ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B := by
  obtain ⟨u, hu, _, hb⟩ := exists_scalar_seed_common_solution hn f hf hfc φ hφ
    p hp hpc hp0 hpm hcurv B hB hsource
  obtain ⟨w, _, hh, _, hnorm⟩ := ScalarRecovery.exists_entire_scalar_complement hn
    (scalarSeedTop hn f) u (scalarSeedDbar hn f) (scalarSeed_weakDbar hn f hf hfc) hu
  have hseed : ScalarRecovery.scalarCoefficient hn (scalarSeedTop hn f) = f := by
    funext z
    exact scalarSeedTop_coefficient hn f z
  have hpower : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  refine ⟨ScalarRecovery.scalarCoefficient hn w, hh, ?_⟩
  intro j
  have H := (hnorm (fun z => φ z + p j z)
    (smoothFn_euclidean_of_contDiff hn _ (hφ.add (hp j)))).symm.le.trans (hb j)
  simp only [hseed] at H
  exact (le_mul_of_one_le_left' hpower).trans H

end Yau.Proofs.C03Aux

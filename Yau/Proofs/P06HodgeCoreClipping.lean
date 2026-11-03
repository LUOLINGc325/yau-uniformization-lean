import Yau.Proofs.P06PolynomialEnergy
import Yau.Proofs.P06FiberApproximation
import Yau.Proofs.P06HodgeEnergyLowerSemicontinuity

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual fiber functional calculus of a compact real (1,1) core element
lies in the original closed d/δ domain with the sharp q upper bound. -/
theorem hodgeEnergy_functionalForm_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11 : RealOneOne A) (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (h0 : F 0 = 0)
    (hL : L2RealForm g.form μ (FiberApprox.functionalForm g.form A F)) :
    ∃ v : HodgeEnergySpace g μ hμ,
      hodgeEnergyValue g μ hμ v = realizeActualForm g μ (FiberApprox.functionalForm g.form A F) hL ∧
        hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) := by
  obtain ⟨R, hR, hnorm, hspec⟩ :=
    FiberApprox.exists_global_spectral_and_pointNorm_bound g A hA hcA h11
  let p (j : ℕ) := P06ClipBernstein.zeroFixedBernstein R F j
  have hp (j : ℕ) : (p j).eval 0 = 0 := P06ClipBernstein.zeroFixedBernstein_zero R F j
  have hd (j : ℕ) (r : ℝ) (hr : r ∈ Set.Icc (-R) R) : |(p j).derivative.eval r| ≤ 1 :=
    P06ClipBernstein.zeroFixedBernstein_derivative_bound hR hF j hr
  let P (j : ℕ) := FiberPoly.polynomialForm g.form A h11 (p j)
  have hs (j : ℕ) : SmoothRealForm (P j) := FiberPoly.polynomialForm_smooth g A hA h11 (p j)
  have hc (j : ℕ) : CompactlySupportedRealForm (P j) :=
    FiberPoly.polynomialForm_compactlySupported g.form A h11 (p j) (hp j) hcA
  have hl2 (j : ℕ) : L2RealForm g.form μ (P j) := smooth_compactlySupported_l2RealForm g μ hμ _ (hs j) (hc j)
  let w (j : ℕ) := hodgeEnergyCore g μ hμ (P j) (hs j) (hc j)
  have hdist := FiberApprox.polynomialForm_l2_distance_tendsto g μ hμ A hA hcA h11 p F hF h0
    hR.le hspec hp hd (P06ClipBernstein.zeroFixedBernstein_uniform hR hF h0)
  have hstrong : Tendsto (fun j => hodgeEnergyValue g μ hμ (w j)) atTop
      (𝓝 (realizeActualForm g μ (FiberApprox.functionalForm g.form A F) hL)) := by
    exact (tendsto_realizeL2Form_iff g μ
      (fun j => L2FormSpace.ofSection (P j) (hl2 j))
      (L2FormSpace.ofSection (FiberApprox.functionalForm g.form A F) hL)).mpr hdist
  have hq (j : ℕ) : hodgeEnergy g μ hμ (w j) ≤
      hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) :=
    polynomialForm_hodgeEnergy_le g μ hμ hk hHBC A hA hcA h11 (p j) (hp j) hnorm (hd j)
  exact hodgeEnergy_strong_image_limit g μ hμ w _
    (fun _ => hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA)) _ hstrong hq tendsto_const_nhds

theorem hodgeEnergy_intervalForm_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11 : RealOneOne A) {C : ℝ} (hC : 0 ≤ C) :
    ∃ hL : L2RealForm g.form μ (Clip.intervalForm g.form C A),
      ∃ v : HodgeEnergySpace g μ hμ,
        hodgeEnergyValue g μ hμ v = realizeActualForm g μ (Clip.intervalForm g.form C A) hL ∧
          hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) := by
  let hL := FiberApprox.intervalForm_l2 g μ hμ A hA hcA h11 hC
  refine ⟨hL, ?_⟩
  exact hodgeEnergy_functionalForm_core g μ hμ hk hHBC A hA hcA h11
    (Clip.intervalClip C) (Clip.intervalClip_lipschitz C) (Clip.intervalClip_zero hC) hL

theorem hodgeEnergy_positiveForm_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (hHBC : ∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature g.form x u v)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (h11 : RealOneOne A) :
    ∃ hL : L2RealForm g.form μ (Clip.positiveForm g.form A),
      ∃ v : HodgeEnergySpace g μ hμ,
        hodgeEnergyValue g μ hμ v = realizeActualForm g μ (Clip.positiveForm g.form A) hL ∧
          hodgeEnergy g μ hμ v ≤ hodgeEnergy g μ hμ (hodgeEnergyCore g μ hμ A hA hcA) := by
  let hL := FiberApprox.positiveForm_l2 g μ hμ A hA hcA h11
  refine ⟨hL, ?_⟩
  have hLF : L2RealForm g.form μ (FiberApprox.functionalForm g.form A (fun r => max 0 r)) := by
    simpa only [FiberApprox.functionalForm_positive] using hL
  have he := hodgeEnergy_functionalForm_core g μ hμ hk hHBC A hA hcA h11
    (fun r => max 0 r) (LipschitzWith.id.const_max 0) (by simp) hLF
  simpa only [FiberApprox.functionalForm_positive] using he

end Yau.NodeProofs.P06Aux

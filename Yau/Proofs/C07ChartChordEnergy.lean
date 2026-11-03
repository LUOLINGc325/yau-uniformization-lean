import Yau.Proofs.C07ChartChordCompact
import Yau.Proofs.C07RadialCurveMetric

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07ChartChordAux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem pullbackMat_continuousOn (k : HermitianField M) (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (i j : Fin n) : ContinuousOn (fun q => pullbackMat k ψ q i j) (Metric.ball 0 r) := by
  have hQ (v : ComplexVector n) : ContinuousOn (fun q => chartEnergy k ψ q v) (Metric.ball 0 r) :=
    C07RadialCurveAux.pullback_energy_continuousOn k hk hψ v
  have hre (q : ComplexVector n) : (pullbackMat k ψ q i j).re =
      (chartEnergy k ψ q (stdVec i + stdVec j) - chartEnergy k ψ q (stdVec i) -
        chartEnergy k ψ q (stdVec j)) / 2 := by
    let L : ComplexVector n →L[ℂ] TangentVector M (ψ q) :=
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) ψ q).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℂ) q).symm.toContinuousLinearMap
    change ((k (ψ q)).toFun (L (stdVec i)) (L (stdVec j))).re =
      (hermitianNormSq (k (ψ q)) (L (stdVec i + stdVec j)) -
        hermitianNormSq (k (ψ q)) (L (stdVec i)) - hermitianNormSq (k (ψ q)) (L (stdVec j))) / 2
    rw [map_add]
    exact hermitian_re_from_norm _ _ _
  have him (q : ComplexVector n) : (pullbackMat k ψ q i j).im =
      (chartEnergy k ψ q (stdVec i) + chartEnergy k ψ q (stdVec j) -
        chartEnergy k ψ q (stdVec i + Complex.I • stdVec j)) / 2 := by
    let L : ComplexVector n →L[ℂ] TangentVector M (ψ q) :=
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) ψ q).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℂ) q).symm.toContinuousLinearMap
    change ((k (ψ q)).toFun (L (stdVec i)) (L (stdVec j))).im =
      (hermitianNormSq (k (ψ q)) (L (stdVec i)) + hermitianNormSq (k (ψ q)) (L (stdVec j)) -
        hermitianNormSq (k (ψ q)) (L (stdVec i + Complex.I • stdVec j))) / 2
    rw [map_add, map_smul]
    exact hermitian_im_from_norm _ _ _
  have hRe : ContinuousOn (fun q => (pullbackMat k ψ q i j).re) (Metric.ball 0 r) :=
    ((((hQ (stdVec i + stdVec j)).sub (hQ (stdVec i))).sub (hQ (stdVec j))).div_const 2).congr
      (fun q _ => hre q)
  have hIm : ContinuousOn (fun q => (pullbackMat k ψ q i j).im) (Metric.ball 0 r) :=
    ((((hQ (stdVec i)).add (hQ (stdVec j))).sub (hQ (stdVec i + Complex.I • stdVec j))).div_const 2).congr
      (fun q _ => him q)
  apply ((Complex.ofRealCLM.continuous.comp_continuousOn hRe).add
    ((continuousOn_const (c := Complex.I)).mul
      (Complex.ofRealCLM.continuous.comp_continuousOn hIm))).congr
  intro q _
  apply Complex.ext <;> simp

/-- Joint continuity is in the actual chart point and the tangent direction. -/
theorem chartEnergy_continuousOn (k : HermitianField M) (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r)) :
    ContinuousOn (fun p : ComplexVector n × ComplexVector n => chartEnergy k ψ p.1 p.2)
      (Metric.ball 0 r ×ˢ Set.univ) := by
  have hv (i : Fin n) : Continuous (fun p : ComplexVector n × ComplexVector n => p.2 i) :=
    (contDiff_piLp_apply (𝕜 := ℂ) (n := ∞) (p := 2) (i := i)).continuous.comp continuous_snd
  have hB (i j : Fin n) : ContinuousOn (fun p : ComplexVector n × ComplexVector n =>
      pullbackMat k ψ p.1 i j) (Metric.ball 0 r ×ˢ Set.univ) :=
    (pullbackMat_continuousOn k hk hψ i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hquad : ContinuousOn (fun p : ComplexVector n × ComplexVector n =>
      (star (WithLp.ofLp p.2) ⬝ᵥ (pullbackMat k ψ p.1 *ᵥ WithLp.ofLp p.2)).re)
      (Metric.ball 0 r ×ˢ Set.univ) := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact continuousOn_finset_sum _ fun i _ =>
      (Complex.continuous_conj.comp (hv i)).continuousOn.mul
        (continuousOn_finset_sum _ fun j _ => (hB i j).mul (hv j).continuousOn)
  exact hquad.congr fun p _ => (C07Aux.pullback_quadratic k ψ p.1 p.2).symm

/-- Metric smoothness and chart smoothness supply the joint continuity
used by the compact uniform bound. -/
theorem exists_uniform_differential_bound (k : HermitianField M) (hk : MetricSmooth k)
    {ψ : ComplexVector n → M.Carrier} {r R : ℝ}
    (hψ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ ψ (Metric.ball 0 r))
    (hRr : R < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Metric.closedBall (0 : ComplexVector n) R,
      ∀ v : ComplexVector n, chartEnergy k ψ q v ≤ C * ‖v‖ ^ 2 :=
  exists_uniform_differential_bound_of_continuous k (chartEnergy_continuousOn k hk hψ) hRr

end Yau.Proofs.C07ChartChordAux

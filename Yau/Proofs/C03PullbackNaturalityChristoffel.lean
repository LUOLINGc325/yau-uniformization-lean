import Yau.Proofs.C03PullbackNaturalityLocal
import Yau.Proofs.C03PullbackNaturalityConnection
import Yau.LeafProofs.L23FieldMetricCoordinatePairing

/-! The coordinate Christoffel chain rule for an actual Hermitian pullback
on an open set. Both fields are smooth; no global Kähler condition on the
source field is used. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Filter Yau Yau.LeafProofs L12Aux
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem chartChristoffel_pullback
    (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn)) (ks : MetricSmooth k)
    (h : HermitianField M) (hs : MetricSmooth h)
    {O : Set (ComplexVector n)} (hO : IsOpen O)
    {Φ : ComplexVector n → M.Carrier}
    (hΦ : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ Φ O)
    (hbij : ∀ z ∈ O, Function.Bijective (mfderiv (ComplexModel n) (ComplexModel n) Φ z))
    (heq : ∀ (z : (ComplexEuclideanManifold n hn).Carrier), z ∈ O →
      ∀ u v : TangentVector (ComplexEuclideanManifold n hn) z,
      (k z).toFun u v = (h (Φ z)).toFun
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v))
    (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source)
    (u v : ComplexVector n) :
    fderiv ℝ (fun p => chartPt c (Φ p)) z (chartChristoffelBilin k (0 : ComplexVector n) z u v) =
      fderiv ℝ (fderiv ℝ (fun p => chartPt c (Φ p))) z u v +
        chartChristoffelBilin h c (chartPt c (Φ z))
          (fderiv ℝ (fun p => chartPt c (Φ p)) z u)
          (fderiv ℝ (fun p => chartPt c (Φ p)) z v) := by
  have hOc := coordinate_domain_open hO hΦ.continuousOn c
  have hfc := coordinate_contDiff_complex hΦ c
  have hfr := coordinate_contDiff_real hΦ c
  have hfd := (hfc.contDiffAt (hOc.mem_nhds hz)).differentiableAt (by simp)
  have hΦd := (hΦ.contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)
  have hzt : z ∈ chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) := by
    rw [source_chartTarget hn]
    trivial
  have hyt : chartPt c (Φ z) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source hz.2
  have hmetric : ∀ᶠ p in 𝓝 z, ∀ a b,
      realMetricInChart k (0 : ComplexVector n) p a b =
      realMetricInChart h c (chartPt c (Φ p))
        (fderiv ℝ (fun q => chartPt c (Φ q)) p a)
        (fderiv ℝ (fun q => chartPt c (Φ q)) p b) := by
    filter_upwards [hOc.mem_nhds hz] with p hp a b
    exact realMetric_pullback hn k h c
      ((hΦ.contMDiffAt (hO.mem_nhds hp.1)).mdifferentiableAt (by simp)) hp.2
      ((hfc.contDiffAt (hOc.mem_nhds hp)).differentiableAt (by simp)) (heq p hp.1) a b
  apply connection_chain_of_metric_pullback
    (realMetricInChart k (0 : ComplexVector n)) (realMetricInChart h c)
    (chartChristoffelBilin k (0 : ComplexVector n)) (chartChristoffelBilin h c)
    (fun p => chartPt c (Φ p)) z
    ((hfr.contDiffAt (hOc.mem_nhds hz)).of_le (by simp))
    (((L23Aux.realMetricInChart_smooth k ks _).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) _).mem_nhds hzt)).differentiableAt (by simp))
    (((L23Aux.realMetricInChart_smooth h hs c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hyt)).differentiableAt (by simp))
    (realMetricInChart_symm h c _) _
    (coordinate_fderiv_bijective c hΦd hz.2 hfd (hbij z hz.1)).surjective
    (chartChristoffelBilin_symm k _ z) (chartChristoffelBilin_symm h c _)
    (L23Aux.realMetricInChart_connection_compatibility k ks _ z hzt)
    (L23Aux.realMetricInChart_connection_compatibility h hs c _ hyt) hmetric u v
  intro a ha
  exact (L23Aux.realMetricInChart_quadratic_eq_zero_iff h c (Φ z)
    (by simpa only [Set.mem_preimage, extChartAt_source] using hz.2) a).mp ha

end Yau.Proofs.C03Aux.PullbackNaturality

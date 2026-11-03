import Yau.Proofs.C03PullbackNaturalityGeometry
import Yau.Proofs.C03PullbackNaturalityPaperCoordinates

/-! Actual pullback bisectional curvature, with exactly the paper's real
curvature convention and the sign used by the moving-field energy. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Yau Yau.LeafProofs L12Aux L23Aux Yau.NodeProofs.P02Aux
open scoped Topology ContDiff Manifold
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

section ActualPullback

variable (hn : 1 ≤ n) (k : HermitianField (ComplexEuclideanManifold n hn)) (ks : MetricSmooth k)
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

include ks hs hO hΦ hbij heq

theorem coordinateBisectional_pullback_paper
    (c : M.Carrier) {z : (ComplexEuclideanManifold n hn).Carrier}
    (hz : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source)
    (u v : ComplexVector n) :
    coordinateBisectional k (0 : ComplexVector n) z u v =
      paperBisectionalNumerator h (Φ z)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z u)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z v) := by
  have hOc := coordinate_domain_open hO hΦ.continuousOn c
  have hf := ((coordinate_contDiff_complex hΦ c).contDiffAt
    (hOc.mem_nhds hz)).differentiableAt (by simp)
  have hΦd := (hΦ.contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)
  rw [paperBisectional_in_chart h hs c (Φ z)
    (by simpa only [Set.mem_preimage, extChartAt_source] using hz.2)]
  unfold coordinateBisectional
  rw [coordinateRm_pullback hn k ks h hs hO hΦ hbij heq c hz,
    coordinateRm_pullback hn k ks h hs hO hΦ hbij heq c hz,
    coordinate_fderiv_I hf,
    coordinate_fderiv_real c hΦd hz.2 hf u,
    coordinate_fderiv_real c hΦd hz.2 hf v]

theorem paired_energy_curvature_eq_neg_paper
    {z : (ComplexEuclideanManifold n hn).Carrier} (hz : z ∈ O)
    (T W : ComplexVector n) :
    realMetricInChart k (0 : ComplexVector n) z T
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) z W T W) +
      realMetricInChart k (0 : ComplexVector n) z T
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) z
          (Complex.I • W) T (Complex.I • W)) =
      -paperBisectionalNumerator h (Φ z)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z T)
        (mfderiv (ComplexModel n) (ComplexModel n) Φ z W) := by
  have hz0 : z ∈ chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) := by
    rw [source_chartTarget hn]
    trivial
  rw [connectionCurvature_bisectional_sign k ks _ hz0]
  congr 1
  apply coordinateBisectional_pullback_paper hn k ks h hs hO hΦ hbij heq (Φ z) _ T W
  refine ⟨hz, ?_⟩
  simpa only [Set.mem_preimage, extChartAt_source] using
    mem_chart_source (ComplexVector n) (Φ z)

theorem paired_energy_curvature_neg
    (hp : PaperPositiveBisectional h)
    {z : (ComplexEuclideanManifold n hn).Carrier} (hz : z ∈ O)
    {T W : ComplexVector n} (hT : T ≠ 0) (hW : W ≠ 0) :
    realMetricInChart k (0 : ComplexVector n) z T
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) z W T W) +
      realMetricInChart k (0 : ComplexVector n) z T
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) z
          (Complex.I • W) T (Complex.I • W)) < 0 := by
  rw [paired_energy_curvature_eq_neg_paper hn k ks h hs hO hΦ hbij heq hz T W]
  have hnz (v : ComplexVector n) (hv : v ≠ 0) :
      mfderiv (ComplexModel n) (ComplexModel n) Φ z v ≠ 0 := by
    intro he
    apply hv
    apply (hbij z hz).injective
    simpa only [map_zero] using he
  exact neg_neg_of_pos (hp (Φ z) _ _ (hnz T hT) (hnz W hW))

end ActualPullback

end Yau.Proofs.C03Aux.PullbackNaturality

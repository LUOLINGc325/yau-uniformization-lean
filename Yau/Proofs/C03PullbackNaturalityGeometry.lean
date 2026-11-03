import Yau.Proofs.C03PullbackNaturalityChristoffel
import Yau.Proofs.C03PullbackNaturalityComplex
import Yau.Proofs.C03PullbackNaturalityCurvature
import Yau.LeafProofs.L23FieldMetricParallelCalculus
import Yau.Proofs.P02BisectionalNaturality

/-! Local geometric naturality for the actual Hermitian pullback. The source
field may be an arbitrary smooth positive extension outside the open set. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

open Filter Yau Yau.LeafProofs L12Aux L23Aux Yau.NodeProofs.P02Aux
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

theorem chartChristoffel_pullback_I_right (hk : KahlerClosed h)
    {z : ComplexVector n} (hz : z ∈ O) (u v : ComplexVector n) :
    chartChristoffelBilin k (0 : ComplexVector n) z u (Complex.I • v) =
      Complex.I • chartChristoffelBilin k (0 : ComplexVector n) z u v := by
  let c := Φ z
  have hOc := coordinate_domain_open hO hΦ.continuousOn c
  have hzC : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source := by
    refine ⟨hz, ?_⟩
    simpa only [Set.mem_preimage, extChartAt_source] using mem_chart_source (ComplexVector n) c
  have hfc := coordinate_contDiff_complex hΦ c
  have hfd := (hfc.contDiffAt (hOc.mem_nhds hzC)).differentiableAt (by simp)
  apply connection_I_right_of_chain
    (chartChristoffelBilin k (0 : ComplexVector n) z)
    (chartChristoffelBilin h c (chartPt c (Φ z)))
    (fderiv ℝ (fun p => chartPt c (Φ p)) z)
    (fderiv ℝ (fderiv ℝ (fun p => chartPt c (Φ p))) z)
    (coordinate_fderiv_bijective c
      ((hΦ.contMDiffAt (hO.mem_nhds hz)).mdifferentiableAt (by simp)) hzC.2 hfd
      (hbij z hz)).injective
    (coordinate_fderiv_I hfd)
    (coordinate_hessian_I hOc hfc hzC)
    (Yau.NodeProofs.P02Aux.chartChristoffelBilin_I_right h hs hk c
      ((extChartAt (ComplexModel n) c).map_source hzC.2))
    (chartChristoffel_pullback hn k ks h hs hO hΦ hbij heq c hzC) u v

theorem chartChristoffel_pullback_I_I (hk : KahlerClosed h)
    {z : ComplexVector n} (hz : z ∈ O) (u v : ComplexVector n) :
    chartChristoffelBilin k (0 : ComplexVector n) z (Complex.I • u) (Complex.I • v) =
      -chartChristoffelBilin k (0 : ComplexVector n) z u v :=
  connection_I_I_of_I_right _ (chartChristoffelBilin_symm k _ z)
    (chartChristoffel_pullback_I_right hn k ks h hs hO hΦ hbij heq hk hz) u v

theorem connectionCurvature_pullback
    (c : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source)
    (u v w : ComplexVector n) :
    fderiv ℝ (fun p => chartPt c (Φ p)) z
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) z u v w) =
      connectionCurvature (chartChristoffelBilin h c) (chartPt c (Φ z))
        (fderiv ℝ (fun p => chartPt c (Φ p)) z u)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z v)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z w) := by
  apply curvature_chain_of_connection_chain
    (O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source)
    (coordinate_domain_open hO hΦ.continuousOn c)
    (chartChristoffelBilin k (0 : ComplexVector n)) (chartChristoffelBilin h c)
    (fun p => chartPt c (Φ p)) (coordinate_contDiff_real hΦ c) _ _
    (fun q hq => chartChristoffel_pullback hn k ks h hs hO hΦ hbij heq c hq) hz u v w
  · apply (chartChristoffelBilin_contDiffOn k ks (0 : ComplexVector n)).mono
    intro q _
    rw [source_chartTarget hn]
    trivial
  · intro q hq
    exact ((chartChristoffelBilin_contDiffOn h hs c).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds
        ((extChartAt (ComplexModel n) c).map_source hq.2))).differentiableAt (by simp)

theorem coordinateRm_pullback
    (c : M.Carrier) {z : (ComplexEuclideanManifold n hn).Carrier}
    (hz : z ∈ O ∩ Φ ⁻¹' (extChartAt (ComplexModel n) c).source)
    (u v w a : ComplexVector n) :
    coordinateRm k (0 : ComplexVector n) z u v w a =
      coordinateRm h c (chartPt c (Φ z))
        (fderiv ℝ (fun p => chartPt c (Φ p)) z u)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z v)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z w)
        (fderiv ℝ (fun p => chartPt c (Φ p)) z a) := by
  have hz0 : z ∈ chartTarget (M := ComplexEuclideanManifold n hn) (0 : ComplexVector n) := by
    rw [source_chartTarget hn]
    trivial
  have hzt : chartPt c (Φ z) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source hz.2
  have hOc := coordinate_domain_open hO hΦ.continuousOn c
  have hf := ((coordinate_contDiff_complex hΦ c).contDiffAt
    (hOc.mem_nhds hz)).differentiableAt (by simp)
  rw [← connectionCurvature_pair_eq_coordinateRm k ks _ hz0,
    realMetric_pullback hn k h c
      ((hΦ.contMDiffAt (hO.mem_nhds hz.1)).mdifferentiableAt (by simp)) hz.2 hf (heq z hz.1),
    connectionCurvature_pullback hn k ks h hs hO hΦ hbij heq c hz]
  exact connectionCurvature_pair_eq_coordinateRm h hs c hzt _ _ _ _

end ActualPullback

end Yau.Proofs.C03Aux.PullbackNaturality

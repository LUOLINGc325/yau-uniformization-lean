import Yau.Proofs.G01BisectionalNumerator
import Yau.Proofs.G01TangentCoordinates
import Yau.Proofs.G01DimensionOne
import Yau.Proofs.G01SurfacePlane

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem paper_hbc_eq_chern (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (u v : TangentVector M x) :
    paperHolomorphicBisectionalCurvature h x u v = ChernBisectionalCurvatureOnTangent h x u v := by
  unfold paperHolomorphicBisectionalCurvature ChernBisectionalCurvatureOnTangent
  rw [paperBisectionalNumerator_eq_four h hs hk]
  rw [show (2 * hermitianNormSq (h x) u) * (2 * hermitianNormSq (h x) v) =
    4 * (hermitianNormSq (h x) u * hermitianNormSq (h x) v) by ring]
  exact mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)

theorem paperPositive_iff_griffithsPositive (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) : PaperPositiveBisectional h ↔ GriffithsPositive h := by
  constructor
  · intro hp x ξ η hξ hη
    let u := chartVec x x ξ
    let v := chartVec x x η
    have hu : u ≠ 0 := (chartVec_ne_zero_iff x x (mem_extChartAt_source x) ξ).mpr hξ
    have hv : v ≠ 0 := (chartVec_ne_zero_iff x x (mem_extChartAt_source x) η).mpr hη
    have hcξ : tangentCoordinates x u = ξ :=
      L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) ξ
    have hcη : tangentCoordinates x v = η :=
      L12Aux.tangentCoords_chartVec x x (mem_extChartAt_source x) η
    have hr := hp x u v hu hv
    change 0 < paperBisectionalNumerator h x u v at hr
    rw [paper_numerator_eq_bisectionalForm h hs hk, hcξ, hcη] at hr
    linarith
  · intro hp x u v hu hv
    have hr := hp x (tangentCoordinates x u) (tangentCoordinates x v)
      ((tangentCoordinates_ne_zero_iff x u).mpr hu) ((tangentCoordinates_ne_zero_iff x v).mpr hv)
    change 0 < paperBisectionalNumerator h x u v
    rw [paper_numerator_eq_bisectionalForm h hs hk]
    exact mul_pos (by norm_num) hr

theorem paperBisectionalNormalization (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) : Blueprint.PaperBisectionalNormalization h := by
  refine ⟨?_, chernCalculatorCompatibility h hs, paper_hbc_eq_chern h hs hk,
    paper_numerator_eq_bisectionalForm h hs hk, paperPositive_iff_griffithsPositive h hs hk⟩
  intro hs' hk' x u v
  exact paperBisectionalNumerator_eq_four h hs' hk' x u v

/-- Complex dimension one reduces to the actual nondegenerate Gaussian plane (u,Ju). -/
theorem paperSurface_normalization {M : ComplexManifold 1}
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (x : M.Carrier) (u v : TangentVector M x) (hu : u ≠ 0) (hv : v ≠ 0) :
    paperHolomorphicBisectionalCurvature h x u v =
      paperRm h x u (Complex.I • u) (Complex.I • u) u / (2 * hermitianNormSq (h x) u) ^ 2 := by
  obtain ⟨c, hvc⟩ := exists_smul_eq_of_dim_one x u v hu
  have hc : c ≠ 0 := by
    intro hc
    apply hv
    rw [hvc, hc, zero_smul]
  have hq : Complex.normSq c ≠ 0 := (Complex.normSq_pos.mpr hc).ne'
  have hn : paperBisectionalNumerator h x u (c • u) =
      Complex.normSq c * paperBisectionalNumerator h x u u := by
    rw [paperBisectionalNumerator_eq_four h hs hk,
      paperBisectionalNumerator_eq_four h hs hk,
      bisectionalNumeratorOnTangent_re_smul_right]
    ring
  have hself : paperBisectionalNumerator h x u u =
      paperRm h x u (Complex.I • u) (Complex.I • u) u := by
    unfold paperBisectionalNumerator paperComplexStructure
    rw [paperRm_self_first, zero_add]
  rw [hvc]
  unfold paperHolomorphicBisectionalCurvature
  rw [hn, hself, hermitianNormSq_smul]
  rw [show (2 * hermitianNormSq (h x) u) *
      (2 * (Complex.normSq c * hermitianNormSq (h x) u)) =
        Complex.normSq c * (2 * hermitianNormSq (h x) u) ^ 2 by ring]
  exact mul_div_mul_left _ _ hq

end Yau.NodeProofs.G01Aux

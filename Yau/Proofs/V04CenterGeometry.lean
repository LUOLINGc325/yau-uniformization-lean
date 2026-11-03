import Yau.Proofs.V03LeviMatrix
import Yau.Proofs.V03CotangentSmooth

/-! The contact test is smooth in the actual chart centered at a disc's
center. A round trip is used only on a neighborhood in a valid overlap. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem contact_spatial_test_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    {y : CotangentPoint X.manifold} {s : ℝ}
    (hc : InCotangentTimeChart d.chart y s (centerCylinder d)) :
    ContDiffAt ℝ ∞ (fun z => d.test (cotangentChartInv y.1 z) s) (cotangentChart y.1 y) := by
  obtain ⟨V, hV, hCV, _, htest⟩ := hd.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  let z₀ := cotangentChart y.1 y
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source y.1
  have hz₀ : z₀ ∈ cotangentTarget y.1 := cotangentChart_mapsTo y.1 hself
  have hround : cotangentChartInv y.1 z₀ = y := cotangentChart_left_inv y.1 hself
  have hbase : chartInv y.1 z₀.1 = y.1 := congrArg Prod.fst hround
  have hother : chartInv y.1 z₀.1 ∈ (extChartAt (ComplexModel n) d.chart).source := by
    rw [hbase]
    exact hc.1
  have hchange : ContDiffAt ℝ ∞
      (fun z => cotangentChart d.chart (cotangentChartInv y.1 z)) z₀ :=
    (cotangentChartTransition_contDiffAt y.1 d.chart hz₀ hother).restrict_scalars ℝ
  have htestAt : ContDiffAt ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      d.test (cotangentChartInv d.chart p.1) p.2) (cotangentChart d.chart y, s) :=
    (htest _ (hCV hc.2)).contDiffAt (hV.mem_nhds (hCV hc.2))
  have htestAt' : ContDiffAt ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      d.test (cotangentChartInv d.chart p.1) p.2)
      (cotangentChart d.chart (cotangentChartInv y.1 z₀), s) := by
    simpa only [hround] using htestAt
  have hcomp := htestAt'.comp z₀ (hchange.prodMk (contDiffAt_const (c := s)))
  have hInvSmooth : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv y.1) z₀.1 :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) y.1).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) y.1).mem_nhds hz₀.1)
  have hInv : ContinuousAt (fun z : CotangentCoord n => chartInv y.1 z.1) z₀ :=
    hInvSmooth.continuousAt.comp continuousAt_fst
  have hsource : ∀ᶠ z in 𝓝 z₀, cotangentChartInv y.1 z ∈ cotangentSource d.chart :=
    hInv.eventually ((isOpen_extChartAt_source (I := ComplexModel n) d.chart).mem_nhds hother)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hsource] with z hz
  exact congrArg (fun y' => d.test y' s) (cotangentChart_left_inv d.chart hz).symm

theorem contact_spatialHessian_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    {y : CotangentPoint X.manifold} {s : ℝ}
    (hc : InCotangentTimeChart d.chart y s (centerCylinder d)) :
    (spatialHessian (fun y' => d.test y' s) y).IsHermitian :=
  leviMatrix_isHermitian ((contact_spatial_test_contDiffAt hd hc).of_le (by simp)) cotangentDir

theorem centerTestHessian_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    {F : VariationDisc X} (hc : InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d))
    (E : ℂ → CotangentMatrix n) : (centerTestHessian d F E).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul (E 0) (contact_spatialHessian_isHermitian hd hc)

theorem admissible_centerTestHessian_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) : (centerTestHessian d F E).IsHermitian :=
  centerTestHessian_isHermitian hd hF.2.2.2.2.2.1 E

end Yau.Blueprint.V04Proof

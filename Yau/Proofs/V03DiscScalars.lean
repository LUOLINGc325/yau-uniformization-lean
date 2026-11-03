import Yau.Proofs.V03DualTransport
import Yau.Proofs.V03MetricSmooth
import Yau.Proofs.V03DiscSmooth
import Yau.Proofs.V03Walls

/-! Smooth scalar pullbacks from the actual cotangent charts. This includes
the original static norm and the full product of cutoff walls. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem cotangentDisc_scalar_contDiffOn {f : ℂ → CotangentPoint M}
    (hf : CotangentDisc f) {b : CotangentPoint M → ℝ}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z))
      (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (fun ζ => b (f ζ)) (Metric.closedBall 0 1) := by
  intro ζ hζ
  obtain ⟨V, hV, hζV, hsource, hcoord⟩ := (cotangentDisc_holomorphicOn hf).2 ζ hζ
  have hmodel := (hb (f ζ).1).comp (hcoord.restrict_scalars ℝ)
    (fun η hη => cotangentChart_mapsTo (f ζ).1 (hsource η hη))
  apply (contDiffWithinAt_inter (hV.mem_nhds hζV)).mp
  apply (hmodel ζ ⟨hζ, hζV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hζ, hζV⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact congrArg b (cotangentChart_left_inv (f ζ).1 (hsource η hη)).symm

theorem cotangentDisc_dualNorm_contDiffOn (g : SmoothMetric M)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContDiffOn ℝ ∞ (fun ζ => dualNorm g.form (f ζ).1 (f ζ).2) (Metric.closedBall 0 1) := by
  apply cotangentDisc_scalar_contDiffOn hf (b := fun y => dualNorm g.form y.1 y.2)
  intro x
  exact (dualNormChart_contDiffOn g x).congr (fun z hz => dualNorm_cotangentChartInv g.form x hz)

theorem cotangentDisc_smoothFn_contDiffOn {u : M.Carrier → ℝ} (hu : SmoothFn u)
    {f : ℂ → CotangentPoint M} (hf : CotangentDisc f) :
    ContDiffOn ℝ ∞ (fun ζ => u (f ζ).1) (Metric.closedBall 0 1) := by
  apply cotangentDisc_scalar_contDiffOn hf (b := fun y => u y.1)
  intro x
  exact (hu x).comp contDiff_fst.contDiffOn (fun z hz => hz.1)

variable {q : ℕ} {X : KahlerManifold n}

theorem cotangentDisc_wallProduct_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f) :
    ContDiffOn ℝ ∞ (fun ζ => wallProduct d j (f ζ)) (Metric.closedBall 0 1) := by
  have hu : SmoothFn d.u := hd.2.2.2.1.1
  have h0 : d.h 0 = X.metric.form := hd.2.2.1.1.1.1
  have hN : ContDiffOn ℝ ∞ (fun ζ => dualNorm (d.h 0) (f ζ).1 (f ζ).2)
      (Metric.closedBall 0 1) := by
    rw [h0]
    exact cotangentDisc_dualNorm_contDiffOn X.metric hf
  have hp := setup_wallProfiles hd
  exact (hp.1.comp_contDiffOn ((cotangentDisc_smoothFn_contDiffOn hu hf).div_const (d.A j))).mul
    (hp.2.1.comp_contDiffOn (hN.div_const (d.B j ^ 2)))

theorem admissible_logWall_contDiffWithinAt {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) (θ : ℝ) :
    ContDiffWithinAt ℝ ∞ (fun ζ => Real.log (wallProduct d j (F.f ζ)))
      (Metric.closedBall 0 1) (circlePoint θ) :=
  ((cotangentDisc_wallProduct_contDiffOn hd j hF.1) _ (circlePoint_mem_closedBall θ)).log
    (admissible_wallProduct_bounds hd hF θ).1.ne'

end Yau.Blueprint.V03Proof

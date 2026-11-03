import Yau.Proofs.V03CotangentScalarMixed
import Yau.Proofs.V03FamilyLogTrace

/-! The pointwise actual logarithmic mixed variation depends only on
the prescribed first field in the original centered cotangent chart. -/

open scoped Manifold Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem wallProduct_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun z => wallProduct d j (cotangentChartInv x z)) (cotangentTarget x) :=
  (deltaBase_chart_contDiffOn hd j x).mul (deltaFiber_chart_contDiffOn hd j x)

theorem logWall_chart_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {y : CotangentPoint X.manifold} (hy : y ∈ cotangentSource x)
    (hp : wallProduct d j y ≠ 0) :
    ContDiffAt ℝ 2 (fun z => Real.log (wallProduct d j (cotangentChartInv x z)))
      (cotangentChart x y) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  apply (((wallProduct_chart_contDiffOn hd j x).contDiffAt
    (hopen.mem_nhds (cotangentChart_mapsTo x hy))).of_le (by simp)).log
  simpa only [cotangentChart_left_inv x hy] using hp

theorem realized_logTrace_mixed {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (θ : ℝ) :
    let ζ := circlePoint θ
    let y := F.f ζ
    let V := cotangentVectorOfCoords ((α ζ * h ζ) • (E ζ *ᵥ l ζ))
    mixedReal (fun z => logTrace d j (fz z) θ) =
      (wirt (fun u => wirtBar (fun u' =>
        (Real.log (wallProduct d j (cotangentChartInv y.1 u')) : ℂ)) u V)
        (cotangentChart y.1 y) V).re := by
  dsimp only
  have hζ := circlePoint_mem_closedBall θ
  have hs : CotangentHolomorphicOn (fun z => fz z (circlePoint θ)) (Metric.ball (0 : ℂ) R) :=
    hR.1.2.2.comp (contDiff_id.prodMk contDiff_const) (fun z hz => ⟨hz, hζ⟩)
  have hzero : fz 0 (circlePoint θ) = F.f (circlePoint θ) := congrFun hR.1.2.1 _
  have hp := (admissible_wallProduct_bounds hd hF θ).1.ne'
  have hb := logWall_chart_contDiffAt hd j (F.f (circlePoint θ)).1
    (mem_extChartAt_source (F.f (circlePoint θ)).1) hp
  have hb' : ContDiffAt ℝ 2
      (fun w => Real.log (wallProduct d j (cotangentChartInv (fz 0 (circlePoint θ)).1 w)))
      (cotangentChart (fz 0 (circlePoint θ)).1 (fz 0 (circlePoint θ))) := by
    simpa only [hzero] using hb
  have hm := cotangentHolomorphicOn_scalar_mixed (b := fun y => Real.log (wallProduct d j y))
    hs (Metric.ball_mem_nhds 0 hR.1.1) hb'
  rw [hzero, hR.2.2.1 _ hζ] at hm
  exact hm

end Yau.Blueprint.V03Proof

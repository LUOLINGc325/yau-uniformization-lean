import Yau.Proofs.V03CotangentScalarDerivative
import Yau.Proofs.V03ActualLogMixedJet
import Yau.Proofs.V03RealAngularTrace

/-! Each actual first real logarithmic boundary jet is the native chart
differential applied to the prescribed first field. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realized_logTrace_realParameterDerivative {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) (v : ℂ) (θ : ℝ) :
    let ζ := circlePoint θ
    let y := F.f ζ
    let V := cotangentVectorOfCoords ((α ζ * h ζ) • (E ζ *ᵥ l ζ))
    realParameterDerivative (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ)) v (0, θ) =
      (fderiv ℝ (fun w => Real.log (wallProduct d j (cotangentChartInv y.1 w)))
        (cotangentChart y.1 y) (v • V) : ℂ) := by
  dsimp only
  have hζ := circlePoint_mem_closedBall θ
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self hR.1.1
  have hs : CotangentHolomorphicOn (fun z => fz z (circlePoint θ)) (Metric.ball (0 : ℂ) R) :=
    hR.1.2.2.comp (contDiff_id.prodMk contDiff_const) (fun z hz => ⟨hz, hζ⟩)
  have hzero : fz 0 (circlePoint θ) = F.f (circlePoint θ) := congrFun hR.1.2.1 _
  have hp := (admissible_wallProduct_bounds hd hF θ).1.ne'
  have hb := logWall_chart_contDiffAt hd j (F.f (circlePoint θ)).1
    (mem_extChartAt_source (F.f (circlePoint θ)).1) hp
  have hb' : DifferentiableAt ℝ
      (fun w => Real.log (wallProduct d j (cotangentChartInv (fz 0 (circlePoint θ)).1 w)))
      (cotangentChart (fz 0 (circlePoint θ)).1 (fz 0 (circlePoint θ))) := by
    simpa only [hzero] using hb.differentiableAt (by norm_num)
  have hchain := cotangentHolomorphicOn_scalar_fderiv
    (b := fun y => Real.log (wallProduct d j y)) hs (Metric.ball_mem_nhds 0 hR.1.1) hb' v
  rw [hzero] at hchain
  have hparam : fderiv ℂ (fun z => cotangentChart (F.f (circlePoint θ)).1 (fz z (circlePoint θ))) 0 v =
      v • cotangentVectorOfCoords ((α (circlePoint θ) * h (circlePoint θ)) •
        (E (circlePoint θ) *ᵥ l (circlePoint θ))) := by
    rw [← hR.2.2.1 _ hζ]
    simpa only [smul_eq_mul, mul_one] using
      map_smul (fderiv ℂ (fun z => cotangentChart (F.f (circlePoint θ)).1
        (fz z (circlePoint θ))) 0) v (1 : ℂ)
  rw [hparam] at hchain
  have hg := family_logTrace_joint_contDiffOn hd j hR.1 hR.2.1
  have hgc : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => (logTrace d j (fz p.1) p.2 : ℂ))
      (Metric.ball (0 : ℂ) R ×ˢ Set.univ) := Complex.ofRealCLM.contDiff.comp_contDiffOn hg
  have hslice : ContDiffOn ℝ ∞ (fun z => logTrace d j (fz z) θ) (Metric.ball (0 : ℂ) R) :=
    hg.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun z hz => ⟨hz, Set.mem_univ θ⟩)
  rw [realParameterDerivative_eq_slice Metric.isOpen_ball hgc h0,
    fderiv_ofReal_apply ((hslice.contDiffAt (Metric.isOpen_ball.mem_nhds h0)).differentiableAt (by simp))]
  exact congrArg Complex.ofReal hchain

end Yau.Blueprint.V03Proof

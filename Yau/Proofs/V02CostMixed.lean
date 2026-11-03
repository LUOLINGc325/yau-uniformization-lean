import Yau.Proofs.V02CostMixedCircle
import Yau.Proofs.V02CostMixedScalar
import Yau.Proofs.V02CostMixedDensity
import Yau.Proofs.V03ActualEnergyMixedSplit
import Yau.Proofs.V03BoundaryHermitian
import Yau.Proofs.V03MixedRealLinear

/-! Exact mixed derivative of the complete original functional. Both cost
terms use the same first field, frame and fixed physical clock. -/

open scoped Topology ContDiff Matrix Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V02CostMixedProof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem realized_boundaryDensity_mixed {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) (θ : ℝ) :
    mixedReal (fun z => boundaryDensity d j {F with f := fz z} (circlePoint θ)) =
      ‖α (circlePoint θ)‖ ^ 2 *
        quadValue (boundarySymbol d j a F E (circlePoint θ)) (l (circlePoint θ)) := by
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  let b : CotangentPoint X.manifold → ℝ := fun y =>
    dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2 +
      wallCost d j y (discTime F (circlePoint θ)) F.s
  have hb : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv (F.f (circlePoint θ)).1 w))
      (cotangentChart (F.f (circlePoint θ)).1 (F.f (circlePoint θ))) :=
    (boundaryCost_chart_contDiffAt hd j (hF.2.2.2.2.2.2.2.1 θ)
      ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩ F.s).of_le (by simp)
  have hm := realized_scalar_mixed hR (circlePoint_mem_closedBall θ) b hb
  change mixedReal (fun z => b (fz z (circlePoint θ))) = _
  rw [hm]
  simp only [boundarySymbol, ← Complex.ofReal_pow, quadValue_real_smul, norm_mul, mul_pow,
    hR.2.2.2.2.2.2.2.1 θ]
  change (‖α (circlePoint θ)‖ ^ 2 * wallPower d j a (F.f (circlePoint θ)) ^ 2) *
    quadValue ((E (circlePoint θ))ᴴ * boundaryHessian d j F (circlePoint θ) * E (circlePoint θ))
      (l (circlePoint θ)) = _
  ring

theorem realized_boundaryCost_mixed {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    mixedReal (fun z => boundaryCost d j {F with f := fz z}) =
      circleAverage (fun θ => ‖α (circlePoint θ)‖ ^ 2 *
        quadValue (boundarySymbol d j a F E (circlePoint θ)) (l (circlePoint θ))) := by
  have hs := family_boundaryDensity_joint_contDiffOn hd j hF hR.1 hR.2.1
  have havg := mixedReal_circleAverage Metric.isOpen_ball
    (hs.mono (Set.prod_mono_right (Set.subset_univ _))) (Metric.mem_ball_self hR.1.1)
  change mixedReal (fun z => circleAverage (fun θ =>
    boundaryDensity d j {F with f := fz z} (circlePoint θ))) = _
  rw [havg]
  congr 1
  funext θ
  exact realized_boundaryDensity_mixed hd hF hR θ

theorem test_chart_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiffAt ℝ 2 (fun w => d.test (cotangentChartInv (F.f 0).1 w) F.s)
      (cotangentChart (F.f 0).1 (F.f 0)) := by
  have hc : StrictEnvelopeContact d := hd.2.2.2.2.2.2.2.1
  obtain ⟨V, hV, hCV, _, hs⟩ := hc.2.2.2.2.2.2
  have hcenter := hF.2.2.2.2.2.1
  have hb := (hs.contDiffAt (hV.mem_nhds (hCV hcenter.2))).comp
    (cotangentChart d.chart (F.f 0)) (contDiffAt_id.prodMk contDiffAt_const)
  exact scalar_chart_contDiffAt_centered (fun y => d.test y F.s) d.chart hcenter.1
    (hb.of_le (by simp))

theorem realized_test_mixed {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    mixedReal (fun z => d.test (fz z 0) F.s) =
      ‖α 0‖ ^ 2 * outerCenter d j a F ^ 2 * quadValue (centerTestHessian d F E) (l 0) := by
  have hm := realized_scalar_mixed hR (Metric.mem_closedBall_self zero_le_one)
    (fun y => d.test y F.s) (test_chart_contDiffAt hd hF)
  have hh : ‖h 0‖ ^ 2 = outerCenter d j a F ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      hR.2.2.2.2.2.1, hR.2.2.2.2.2.2.1]
    ring
  rw [hm, norm_mul, mul_pow, hh]
  rfl

theorem realized_energy_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X}
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    ContDiffAt ℝ 2 (fun z => (variationEnergy d j {F with f := fz z}).toReal) 0 := by
  have h0 : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 hR.1.1
  have hb := baseFamilyArea_contDiffOn X.metric (f := fun p : ℂ × ℂ => fz p.1 p.2)
    Metric.isOpen_ball hR.1.2.2
  have hg := gaussFamilyArea_contDiffOn hd.2.2.2.2.1 (f := fun p : ℂ × ℂ => fz p.1 p.2)
    Metric.isOpen_ball hR.1.2.2
  have hA := cotangentHolomorphicOn_ambient_contDiffOn hR.1.2.2 hd.2.2.2.2.1.1
  have he := euclideanFamilyArea_contDiffOn (H := fun p : ℂ × ℂ => d.G (fz p.1 p.2))
    Metric.isOpen_ball hA
  have hl := family_logEnergy_contDiffOn hd j hR.1 hR.2.1
  have hs : ContDiffAt ℝ 2 (fun z => spatialArea d (fz z) + (clockArea F).toReal +
      (scalarDSq (logTrace d j (fz z))).toReal) 0 :=
    (((((hb.contDiffAt h0).add (he.contDiffAt h0)).add (hg.contDiffAt h0)).add
      contDiffAt_const).add (hl.contDiffAt h0)).of_le (by simp)
  exact hs.congr_of_eventuallyEq (realized_energy_actual_local hd.2.2.2.2.1 hR)

theorem realized_test_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    {j a : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F)
    {E : ℂ → CotangentMatrix n} {l : ℂ → CotangentIndex n → ℂ}
    {h α : ℂ → ℂ} {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r) :
    ContDiffAt ℝ 2 (fun z => d.test (fz z 0) F.s) 0 := by
  have hζ : (0 : ℂ) ∈ Metric.closedBall 0 1 := Metric.mem_closedBall_self zero_le_one
  have hslice : CotangentHolomorphicOn (fun z => fz z 0) (Metric.ball (0 : ℂ) r) :=
    hR.1.2.2.comp (contDiff_id.prodMk contDiff_const) (fun z hz => ⟨hz, hζ⟩)
  obtain ⟨V, hV, h0V, hsrc, hcoord⟩ := hslice.2 0 (Metric.mem_ball_self hR.1.1)
  have hn : Metric.ball (0 : ℂ) r ∩ V ∈ 𝓝 (0 : ℂ) :=
    inter_mem (Metric.ball_mem_nhds 0 hR.1.1) (hV.mem_nhds h0V)
  have hzero : fz 0 0 = F.f 0 := congrFun hR.1.2.1 0
  have ht : ContDiffAt ℝ 2 (fun w => d.test (cotangentChartInv (fz 0 0).1 w) F.s)
      (cotangentChart (fz 0 0).1 (fz 0 0)) := by
    simpa only [hzero] using test_chart_contDiffAt hd hF
  apply (ht.comp 0 (((hcoord.contDiffAt hn).of_le (by simp)).restrict_scalars ℝ)).congr_of_eventuallyEq
  filter_upwards [hn] with z hz
  exact congrArg (fun y => d.test y F.s) (cotangentChart_left_inv (fz 0 0).1 (hsrc z hz)).symm

theorem costMixed_identity {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r ε : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz r) :
    mixedReal (fun z => penalizedFunctional d j ε {F with f := fz z}) =
      circleAverage (fun θ => ‖α (circlePoint θ)‖ ^ 2 *
        quadValue (boundarySymbol d j a F E (circlePoint θ)) (l (circlePoint θ))) -
      ‖α 0‖ ^ 2 * outerCenter d j a F ^ 2 * quadValue (centerTestHessian d F E) (l 0) +
      ε * mixedReal (fun z => (variationEnergy d j {F with f := fz z}).toReal) := by
  have hb : ContDiffAt ℝ 2 (fun z => boundaryCost d j {F with f := fz z}) 0 :=
    ((circleAverage_contDiffOn Metric.isOpen_ball
      ((family_boundaryDensity_joint_contDiffOn hd j hF hR.1 hR.2.1).mono
        (Set.prod_mono_right (Set.subset_univ _)))).contDiffAt
      (Metric.ball_mem_nhds 0 hR.1.1)).of_le (by simp)
  have he := realized_energy_contDiffAt hd hR
  have ht := realized_test_contDiffAt hd hF hR
  have hsum : ContDiffAt ℝ 2 (fun z => boundaryCost d j {F with f := fz z} +
      ε * (variationEnergy d j {F with f := fz z}).toReal) 0 :=
    hb.add (contDiffAt_const.mul he)
  have hconv {f : ℂ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
      ContDiffAt ℝ 2 (fun z => (f z : ℂ)) 0 :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hsplit : (fun z => penalizedFunctional d j ε {F with f := fz z}) =
      (fun z => (boundaryCost d j {F with f := fz z} +
        ε * (variationEnergy d j {F with f := fz z}).toReal) +
          (-1) * d.test (fz z 0) F.s) := by funext z; simp only [penalizedFunctional]; ring
  rw [hsplit, mixedReal_add (hconv hsum) (hconv (contDiffAt_const.mul ht)),
    mixedReal_add (hconv hb) (hconv (contDiffAt_const.mul he)),
    mixedReal_const_mul he, mixedReal_const_mul ht,
    realized_boundaryCost_mixed hd hF hR, realized_test_mixed hd hF hR]
  ring

end Yau.Blueprint.V02CostMixedProof

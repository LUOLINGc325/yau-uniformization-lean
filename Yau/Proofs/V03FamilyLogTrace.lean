import Yau.Proofs.V03DiscScalars
import Yau.Proofs.V03WallTensor
import Yau.Proofs.V03CirclePeriod

/-! The actual logarithmic wall trace of the original joint holomorphic
disc family is jointly real smooth in the parameter and boundary angle.
Only the original closed-disc regularity is used. -/

open scoped Topology ContDiff Manifold
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentHolomorphicOn_scalar_contDiffOn {n : ℕ} {M : ComplexManifold n}
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {S : Set P}
    {f : P → CotangentPoint M} (hf : CotangentHolomorphicOn f S)
    {b : CotangentPoint M → ℝ}
    (hb : ∀ x : M.Carrier, ContDiffOn ℝ ∞ (fun z => b (cotangentChartInv x z)) (cotangentTarget x)) :
    ContDiffOn ℝ ∞ (fun p => b (f p)) S := by
  intro p hp
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p hp
  have hmodel := (hb (f p).1).comp (hcoord.restrict_scalars ℝ)
    (fun y hy => cotangentChart_mapsTo (f p).1 (hsource y hy))
  apply (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp
  apply (hmodel p ⟨hp, hpV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hp, hpV⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact congrArg b (cotangentChart_left_inv (f p).1 (hsource y hy)).symm

theorem family_logTrace_joint_contDiffOn {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) {F : VariationDisc X}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => logTrace d j (fz p.1) p.2)
      (Metric.ball (0 : ℂ) R ×ˢ Set.univ) := by
  have hwall : ContDiffOn ℝ ∞ (fun p : ℂ × ℂ => wallProduct d j (fz p.1 p.2))
      (Metric.ball (0 : ℂ) R ×ˢ Metric.closedBall (0 : ℂ) 1) := by
    apply cotangentHolomorphicOn_scalar_contDiffOn hfamily.2.2
    intro x
    exact (deltaBase_chart_contDiffOn hd j x).mul (deltaFiber_chart_contDiffOn hd j x)
  have hc : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  have htrace : ContDiffOn ℝ ∞ (fun p : ℂ × ℝ => wallProduct d j (fz p.1 (circlePoint p.2)))
      (Metric.ball (0 : ℂ) R ×ˢ Set.univ) :=
    hwall.comp hc.contDiffOn (fun p hp => ⟨hp.1, circlePoint_mem_closedBall p.2⟩)
  exact htrace.log (fun p hp => (admissible_wallProduct_bounds hd (hadm p.1 hp.1) p.2).1.ne')

end Yau.Blueprint.V03Proof

import Yau.Proofs.V03LogTrace
import Yau.Proofs.V03BaseDensity
import Yau.Proofs.V03EuclideanRadial
import Yau.Proofs.V03ClockRadial

/-! A smooth closed cotangent disc with the original positive boundary walls
has finite actual energy. This proves admissibility without using energy
finiteness to establish logarithmic boundary regularity. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundary_logTrace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    (hboundary : ∀ θ, f (circlePoint θ) ∈ boundaryRegion d j) :
    ContDiff ℝ ∞ (logTrace d j f) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hpos := (wallProduct_pos_le_one (setup_wallProfiles hd)
    (setup_index_bounds hd j).1 (setup_index_bounds hd j).2 (hboundary θ)).1
  have hw := ((cotangentDisc_wallProduct_contDiffOn hd j hf) _
    (circlePoint_mem_closedBall θ)).log hpos.ne'
  have hc := hw.comp θ circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun η (_ : η ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall η)
  exact contDiffWithinAt_univ.mp hc

theorem boundary_logSeminorm_ne_top {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {f : ℂ → CotangentPoint X.manifold} (hf : CotangentDisc f)
    (hboundary : ∀ θ, f (circlePoint θ) ∈ boundaryRegion d j) :
    scalarDSq (logTrace d j f) ≠ ⊤ := by
  have hq := boundary_logTrace_contDiff hd hf hboundary
  have hU : ContDiff ℝ ∞ (fun θ => (logTrace d j f θ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq
  apply boundaryDSq_ne_top_of_periodic_C1
    (u' := deriv (fun θ => (logTrace d j f θ : ℂ)))
  · intro θ
    exact (hU.differentiable (by simp) θ).hasDerivAt
  · exact hU.continuous_deriv (by simp)
  · simp only [logTrace, circlePoint_two_pi, circlePoint_zero]

theorem variationEnergy_ne_top_of_boundary {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hf : CotangentDisc F.f)
    (hw : ContDiffOn ℂ ∞ F.w (closedBall 0 1))
    (hboundary : ∀ θ, F.f (circlePoint θ) ∈ boundaryRegion d j) :
    variationEnergy d j F ≠ ⊤ := by
  have hbase := discArea_ne_top_of_cotangentDisc X.metric hf
  have hamb := euclideanArea_ne_top_of_closedDisc
    (cotangentDisc_ambient_contDiffOn hf hd.2.2.2.2.1.1)
  have hclock := clockArea_ne_top_of_closedDisc (F := F) hw
  have hlog := boundary_logSeminorm_ne_top hd hf hboundary
  simp only [variationEnergy, ENNReal.add_ne_top]
  exact ⟨⟨⟨⟨hbase, hamb⟩, ENNReal.ofReal_ne_top⟩, hclock⟩, hlog⟩

theorem slice_admissible_of_center_boundary {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) {f : ℂ → CotangentPoint X.manifold}
    (hf : CotangentDisc f)
    (hcenter : InCotangentTimeChart d.chart (f 0) F.s (centerCylinder d))
    (hboundary : ∀ θ, f (circlePoint θ) ∈ boundaryRegion d j) :
    AdmissibleVariationDisc d j { F with f := f } := by
  refine ⟨hf, hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hcenter, ?_,
    hboundary, variationEnergy_ne_top_of_boundary hd hf hF.2.1 hboundary⟩
  exact hF.2.2.2.2.2.2.1

end Yau.Blueprint.V02Proof

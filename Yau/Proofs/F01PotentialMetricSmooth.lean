import Yau.Proofs.F01PotentialMetricAssembly
import Yau.Proofs.F01MetricSmoothComplexEntries
import Yau.Proofs.F01PotentialChartIdentity
import Yau.Proofs.F01ClosedWirtingerSmooth
import Yau.Proofs.F01FamilyChartGram
import Yau.Proofs.F01MetricFamilySlices
import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01OrdinaryPullback

/-! The intrinsic potential identity and actual joint potential
smoothness prove the original real metric-family smoothness. -/
noncomputable section
open Set
open scoped ContDiff Manifold Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem metricFamilySmooth_of_potential_identity
    (g : HermitianField M) (hg : MetricSmooth g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) {I : Set ℝ}
    (hI : UniqueDiffOn ℝ I) (hU : SmoothSpaceTime U I)
    (hpot : ∀ t ∈ I, ∀ x,
      gMat (h t) x = gMat g x - (t : ℂ) • ricci g x + levi (fun y => U y t) x) :
    MetricFamilySmooth h I := by
  apply metricFamilySmooth_of_complex_entries
  intro a i j
  let e := ordinaryChart a
  have he := (ordinaryChart_contMDiffOn a).mdifferentiableOn (by simp)
  have hei := (ordinaryChart_inverse_contMDiffOn a).mdifferentiableOn (by simp)
  let F : ComplexVector n × ℝ → ℝ := fun p =>
    U (e p.1) p.2 + p.2 * Real.log (pullbackMatrix g e p.1).det.re
  have hF : ContDiffOn ℝ ∞ F (e.source ×ˢ I) :=
    (smoothSpaceTime_holomorphic_chart hU e he).add (contDiffOn_snd.mul
      ((pullback_logdet_contDiffOn g hg e he hei).comp contDiffOn_fst (fun p hp => hp.1)))
  have hLevi := closed_slab_leviC_smooth e.open_source hI hF i j
  have hG := metricFamily_pullback_contDiffOn (fun _ => g) (metricFamilySmooth_const hg I) e he i j
  have hlocal : ContDiffOn ℝ ∞
      (fun p : ComplexVector n × ℝ => pullbackMatrix (h p.2) e p.1 i j) (e.source ×ˢ I) := by
    apply (hG.add hLevi).congr
    intro p hp
    have hm := metric_potential_identity_in_chart g (h p.2) hg (fun y => U y p.2)
      (smoothSpaceTime_slice hU hp.2) p.2 (hpot p.2 hp.2) e he hei hp.1
    have hm' := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) (sub_eq_iff_eq_add.mp hm)
    have heq : localFlowPotential g (fun y => U y p.2) p.2 e =
        (fun z => F (z, p.2)) := by rfl
    rw [heq] at hm'
    simpa only [Matrix.add_apply, add_comm] using hm'
  rw [ordinaryChart_source] at hlocal
  apply hlocal.congr
  intro p hp
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j)
    (ordinaryChart_pullbackMatrix (h p.2) a hp.1).symm

theorem assembledPotentialFlow_metricFamilySmooth
    (g : HermitianField M) (hg : MetricSmooth g) (U : M.Carrier → ℝ → ℝ)
    (I : Set ℝ) (hpos : ∀ t ∈ I, ∀ x, (nativePotentialMatrix g U t x).PosDef)
    (hI : UniqueDiffOn ℝ I) (hU : SmoothSpaceTime U I) :
    MetricFamilySmooth (assembledPotentialFlow g U I hpos) I :=
  metricFamilySmooth_of_potential_identity g hg (assembledPotentialFlow g U I hpos) U hI hU
    (fun t ht x => assembledPotentialFlow_native_matrix g U I hpos ht x)

end Yau.NodeProofs.F01Aux

import Yau.Proofs.E03JointCoordinates
import Yau.Proofs.V03MetricTime

/-! The original joint function is smooth on its actual base-chart domain. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
variable {n : ℕ} {X : KahlerManifold n}

def jointDomain (c : Pt X) : Set (JointSpace n) := {p | p.1 ∈ chartTarget c}
def jointNorm (h : Flow X) (c : Pt X) (p : JointSpace n) : ℝ :=
  dualNormChart (h (Real.exp (2 * p.2.2.re))) c p.1 p.2.1

theorem isOpen_jointDomain (c : Pt X) : IsOpen (jointDomain c) :=
  (isOpen_extChartAt_target (I := ComplexModel n) c).preimage continuous_fst

theorem jointNorm_contDiffOn (h : Flow X) (hh : MetricFamilySmooth h (Set.Ici 0))
    (c : Pt X) : ContDiffOn ℝ ∞ (jointNorm h c) (jointDomain c) := by
  have hr : ContDiff ℝ ∞ (fun p : JointSpace n => p.2.2.re) :=
    Complex.reCLM.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have ht : ContDiff ℝ ∞ (fun p : JointSpace n => Real.exp (2 * p.2.2.re)) :=
    (contDiff_const.mul hr).exp
  have hpair : ContDiff ℝ ∞
      (fun p : JointSpace n => ((p.1, p.2.1), Real.exp (2 * p.2.2.re))) :=
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk ht
  exact (metricFamily_dualNormChart_contDiffOn hh c).comp hpair.contDiffOn
    (fun p hp => ⟨⟨hp, Set.mem_univ _⟩, (Real.exp_pos _).le⟩)

end Yau.NodeProofs.E03Aux

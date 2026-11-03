import Yau.Blueprint.Nodes

open Set
open scoped Topology Manifold
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

variable {n : ℕ} (X : KahlerManifold n)

/-- The original one-chart, positive physical-time domain. -/
def envelopeDomain (T : ℝ) (x : Pt X) : Set (ComplexVector n × ComplexVector n × ℝ) :=
  {p | p.1 ∈ chartTarget x ∧ 0 < p.2.2 ∧ p.2.2 < T}

theorem isOpen_envelopeDomain (T : ℝ) (x : Pt X) : IsOpen (envelopeDomain X T x) := by
  have hz : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  exact (hz.preimage continuous_fst).inter
    (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd))

end Yau.NodeProofs.E02Aux

import Yau.Proofs.E01StrictNeighborhood
import Yau.Proofs.E01LogShrink
import Yau.Proofs.E01HomogeneousFeasible

/-! Lower semicontinuity of the actual log-determinant value from strict shrinks. -/

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

theorem lowerSemicontinuous_log_value_of_maximizers
    {n : ℕ} {P : Type*} [TopologicalSpace P]
    (v : P × ComplexVector n → EReal) (hv : LowerSemicontinuous v)
    (hzero : ∀ p, (0 : EReal) ≤ v (p, 0))
    (hhom : ∀ p (r : ℝ), 0 < r → ∀ η : ComplexVector n,
      v (p, (r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v (p, η))
    (L : P → ℝ)
    (hattain : ∀ p, ∃ B : Herm n, B.PosDef ∧
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v (p, η)) ∧
      L p = Real.log B.det.re)
    (hbound : ∀ p (B : Herm n), B.PosDef →
      (∀ η, (ellipsoidQuadratic B η : EReal) ≤ v (p, η)) →
      Real.log B.det.re ≤ L p) :
    LowerSemicontinuous L := by
  intro p a ha
  obtain ⟨B, hB, hBv, hLB⟩ := hattain p
  obtain ⟨r, hr0, hr1, har⟩ :=
    exists_positive_shrink_logdet_gt B hB a (by rwa [← hLB])
  obtain ⟨U, hU, hpU, hfeasible⟩ := strict_shrink_persists_on_sphere v hv p B hB hBv r hr1
  filter_upwards [hU.mem_nhds hpU] with q hq
  have hBr : ((r : ℂ) • B).PosDef := hB.smul (Complex.zero_lt_real.mpr hr0)
  have hBrv : ∀ η, (ellipsoidQuadratic ((r : ℂ) • B) η : EReal) ≤ v (q, η) :=
    homogeneous_minorant_of_sphere (fun η => v (q, η)) (hzero q) (hhom q) _
      (fun η hη => (hfeasible q hq η hη).le)
  exact har.trans_le (hbound q _ hBr hBrv)

end Yau.NodeProofs.E01Aux

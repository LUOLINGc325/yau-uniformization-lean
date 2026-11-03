import Yau.Proofs.F03DirichletEnergy
import Yau.Proofs.F03SupportedApproximation

/-! Density of the actual supported smooth core in the restricted scalar L² space. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Yau.Proofs.F03Aux
open Yau
open LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichletCoreL2_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) :
    DenseRange (fun f : dirichletCore g μ hμ O =>
      l2Restriction μ O (scalarEnergyDomainL2 g μ hμ f.val)) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨k, hks, hkc, hksupp, hknorm⟩ :=
    exists_supported_smooth_approx g μ hμ hO (Lp.memLp f) hε
  let v : dirichletCore g μ hμ O := ⟨⟨k, hks, hkc⟩, hksupp⟩
  let q := l2Restriction μ O (scalarEnergyDomainL2 g μ hμ v.val)
  refine ⟨q, ⟨v, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp q)).eLpNorm_ne_top hε.le]
  convert hknorm using 1
  apply eLpNorm_congr_ae
  filter_upwards [restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ v.val),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ v.val)] with x hr hk
  change f x - restrictL2 μ O (scalarEnergyDomainL2 g μ hμ v.val) x = f x - k x
  rw [hr, hk]

/-- The constructed inclusion has dense range in the actual restricted L²
space, with no trace-space or density premise. -/
theorem dirichletL2_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O) :
    DenseRange (dirichletL2 g μ hμ O) := by
  intro f
  apply closure_mono (s := Set.range (fun k : dirichletCore g μ hμ O =>
    l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val))) ?_
    (dirichletCoreL2_denseRange g μ hμ O hO f)
  rintro z ⟨v, rfl⟩
  exact ⟨dirichletCoreToEnergy g μ hμ O v, dirichletL2_core g μ hμ O v⟩

end Yau.Proofs.F03Aux

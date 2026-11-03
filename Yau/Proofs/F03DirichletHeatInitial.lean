import Yau.Proofs.F03L2FilterConvergence
import Yau.Proofs.F03ScalarL2Pairing
import Yau.Proofs.F03DirichletHeat

/-! Exact actual-prequotient initial L² convergence of supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {M : ComplexManifold n}

/-- The same actual supported heat converges to every actual initial
scalar in the registered ENNReal squared-distance topology. -/
theorem dirichletHeat_initial_scalarL2DistanceSq (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (f : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict O) f) :
    Tendsto (fun t : ℝ => scalarL2DistanceSq (μ.restrict O)
      (fun x => dirichletHeat g μ hμ O t (scalarToLp hf) x) f)
      (𝓝[>] 0) (𝓝 0) := by
  let S := fun t => dirichletHeat g μ hμ O t (scalarToLp hf)
  have hL (t : ℝ) : ScalarL2 (μ.restrict O) (fun x => S t x) :=
    (scalarL2_iff_memLp _ _).mpr (Lp.memLp (S t))
  apply (tendsto_scalarToLp_filter_iff (𝓝[>] (0 : ℝ)) (μ.restrict O)
    (fun t x => S t x) f hL hf).mp
  have heq (t : ℝ) : scalarToLp (hL t) = S t := by
    apply Lp.ext
    exact scalarToLp_coe (hL t)
  simp_rw [heq]
  exact (dirichletHeat_tendsto_zero g μ hμ O hO (scalarToLp hf)).mono_left
    (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)

end Yau.Proofs.F03Aux

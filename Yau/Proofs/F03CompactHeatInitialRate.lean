import Yau.Proofs.F03CompactHeatPowers
import Yau.Proofs.F03DirichletCoreDuhamel

/-! Genuine pointwise O(t) initial rates for every computed compact-source Laplacian power. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem dirichletClassicalHeat_compact_initial_bound
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : IsOpen O) (k : dirichletCore g μ hμ O)
    (K : ℝ) (hK0 : 0 < K) (hLap : ∀ x,|laplacian g.form k.val x| ≤ K)
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ O,|dirichletClassicalHeat g hK μ hμ O hO
      (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) x t-k.val x| ≤ t*K := by
  apply leOn_open_of_riemannian_ae_le g μ hμ O hO _ (fun _ => t*K)
    (((dirichletClassicalHeat_continuousOn g hK μ hμ O hO _ ht).sub
      (continuous_of_smoothFn k.val.2.1).continuousOn).abs) continuousOn_const
  filter_upwards [dirichletClassicalHeat_ae g hK μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) ht,
    dirichletHeat_compact_initial_ae g hK μ hμ O hO k hK0 ht hLap] with x hx hBound
  change |dirichletClassicalHeat g hK μ hμ O hO
    (l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k.val)) x t-k.val x| ≤ t*K
  rw [hx]
  exact hBound

theorem wholeCompactHeat_initial_rate (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) :
    ∃ K : ℝ,0 < K ∧ ∀ t,0 < t → ∀ x,
      |wholeCompactHeat g hK μ hμ k x t-k x| ≤ t*K := by
  obtain ⟨C,hC⟩ := (continuous_of_smoothFn (smoothFn_laplacian g k.2.1)).bounded_above_of_compact_support
    (laplacian_hasCompactSupport g.form k.2.1 k.2.2)
  let K := max 1 C
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hLap : ∀ x,|laplacian g.form k x| ≤ K := fun x =>
    (show |laplacian g.form k x| ≤ C by simpa only [Real.norm_eq_abs] using hC x).trans (le_max_right _ _)
  exact ⟨K,hK0,fun t ht x => dirichletClassicalHeat_compact_initial_bound
    g hK μ hμ univ isOpen_univ ⟨k,subset_univ _⟩ K hK0 hLap ht x (mem_univ x)⟩

theorem wholeCompactHeat_laplacian_power_initial_rate
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (m : ℕ) :
    ∃ K : ℝ,0 < K ∧ ∀ t,0 < t → ∀ x,
      |((laplacian g.form)^[m] (fun y => wholeCompactHeat g hK μ hμ k y t)) x-
        ((laplacian g.form)^[m] (fun y => k y)) x| ≤ t*K := by
  obtain ⟨K,hK0,hBound⟩ := wholeCompactHeat_initial_rate g hK μ hμ (compactLaplacianPower g μ hμ m k)
  refine ⟨K,hK0,fun t ht x => ?_⟩
  rw [wholeCompactHeat_laplacian_power g hK μ hμ k ht m,
    ← compactLaplacianPower_coe g μ hμ m k]
  exact hBound t ht x

end Yau.Proofs.F03Aux

import Yau.Proofs.F03CompactHeatGenerator
import Yau.Proofs.F03DirichletCompactInitial

/-! All computed Laplacian powers of true compact heat retain their genuine uniform initial trace. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

def compactLaplacianPower (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (m : ℕ) (k : ScalarEnergyDomain g μ hμ) :
    ScalarEnergyDomain g μ hμ := (scalarCompactLaplacian g μ hμ)^[m] k

def wholeCompactHeat (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) : M.Carrier → ℝ → ℝ :=
  dirichletClassicalHeat g hK μ hμ univ isOpen_univ
    (l2Restriction μ univ (scalarEnergyDomainL2 g μ hμ k))

theorem compactLaplacianPower_succ (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (m : ℕ) (k : ScalarEnergyDomain g μ hμ) :
    compactLaplacianPower g μ hμ (m+1) k=
      scalarCompactLaplacian g μ hμ (compactLaplacianPower g μ hμ m k) := by
  exact Function.iterate_succ_apply' (scalarCompactLaplacian g μ hμ) m k

theorem compactLaplacianPower_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (m : ℕ) (k : ScalarEnergyDomain g μ hμ) :
    (fun x => compactLaplacianPower g μ hμ m k x)=
      (laplacian g.form)^[m] (fun x => k x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',compactLaplacianPower_succ]
    change laplacian g.form (fun x => compactLaplacianPower g μ hμ m k x)=_
    rw [← ih]

theorem wholeCompactHeat_laplacian (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {t : ℝ} (ht : 0 < t) :
    laplacian g.form (fun y => wholeCompactHeat g hK μ hμ k y t)=
      (fun y => wholeCompactHeat g hK μ hμ (scalarCompactLaplacian g μ hμ k) y t) := by
  funext x
  exact dirichletClassicalHeat_compact_laplacian g hK μ hμ univ isOpen_univ
    ⟨k,subset_univ _⟩ ht x (mem_univ x)

theorem wholeCompactHeat_laplacian_power (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    (laplacian g.form)^[m] (fun y => wholeCompactHeat g hK μ hμ k y t)=
      (fun y => wholeCompactHeat g hK μ hμ (compactLaplacianPower g μ hμ m k) y t) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply',ih,
      wholeCompactHeat_laplacian g hK μ hμ (compactLaplacianPower g μ hμ m k) ht]
    rw [compactLaplacianPower_succ]

theorem scalarToLp_eq_restriction_compact (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (k : ScalarEnergyDomain g μ hμ)
    (hf : ScalarL2 (μ.restrict O) (fun x => k x)) :
    scalarToLp hf=l2Restriction μ O (scalarEnergyDomainL2 g μ hμ k) := by
  apply Lp.ext
  filter_upwards [scalarToLp_coe hf,restrictL2_coe μ O (scalarEnergyDomainL2 g μ hμ k),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ k)] with x hx hr hk
  exact hx.trans (hr.trans hk).symm

theorem wholeCompactHeat_uniform_initial (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ x,
      |wholeCompactHeat g hK μ hμ k x t-k x| < ε := by
  have hf := continuous_compact_scalarL2 g μ hμ univ (continuous_of_smoothFn k.2.1) k.2.2
  obtain ⟨δ,hδ,hClose⟩ := dirichletClassicalHeat_uniform_compact_initial g hK μ hμ univ
    isOpen_univ k (continuous_of_smoothFn k.2.1) k.2.2 (subset_univ _) hf ε hε
  rw [scalarToLp_eq_restriction_compact g μ hμ univ k hf] at hClose
  exact ⟨δ,hδ,fun t ht htd x => hClose t ht htd x (mem_univ x)⟩

theorem wholeCompactHeat_laplacian_power_initial
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : ScalarEnergyDomain g μ hμ) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ,0 < δ ∧ ∀ t,0 < t → t < δ → ∀ x,
      |((laplacian g.form)^[m] (fun y => wholeCompactHeat g hK μ hμ k y t)) x-
        ((laplacian g.form)^[m] (fun y => k y)) x| < ε := by
  obtain ⟨δ,hδ,hClose⟩ := wholeCompactHeat_uniform_initial g hK μ hμ
    (compactLaplacianPower g μ hμ m k) ε hε
  refine ⟨δ,hδ,fun t ht htd x => ?_⟩
  rw [wholeCompactHeat_laplacian_power g hK μ hμ k ht m,
    ← compactLaplacianPower_coe g μ hμ m k]
  exact hClose t ht htd x

end Yau.Proofs.F03Aux

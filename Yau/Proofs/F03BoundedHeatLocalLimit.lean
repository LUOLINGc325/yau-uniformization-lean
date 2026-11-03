import Yau.Proofs.F03BoundedSourceApproximation
import Yau.Proofs.F03BoundedCaloricLimit
import Yau.Proofs.F03DirichletChartEquation
import Yau.Proofs.F03ExhaustionKernelBuffers
import Yau.LeafProofs.L19HeatRegularityEllipticity

/-! The actual bounded-source integral is locally smooth and caloric at every positive time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

def dirichletMinimalBoundedHeatChart (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (a : M.Carrier) (p : Point n) : ℝ :=
  ∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO p.2 (chartInv a p.1) y*f y ∂μ

theorem dirichletMinimalBoundedHeatChart_smooth_caloric
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B)
    (a : M.Carrier) (V : Set (Space n)) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVt : closure V ⊆ chartTarget a)
    (l r : ℝ) (hl : 0 < l) :
    ContDiffOn ℝ ∞ (dirichletMinimalBoundedHeatChart g hK μ hμ O hO f a) (V ×ˢ Ioo l r) ∧
      ∀ p ∈ V ×ˢ Ioo l r,linearOp (V ×ˢ Ioo l r)
        (scalarHeatChartCoeff g a) (fun _ _ => 0)
        (dirichletMinimalBoundedHeatChart g hK μ hμ O hO f a) p=0 := by
  obtain ⟨J0,hJ0⟩ := smoothExhaustion_eventually_contains_chart_compacts O hO a a
    (closure V) (closure V) hVc hVc hVt hVt
  let fData : ∀ j,Lp ℝ 2 (μ.restrict (O (J0+j))) := fun j =>
    scalarToLp (bounded_source_precompact_scalarL2 g μ hμ (O (J0+j)) (hO.1 (J0+j)) f hf B hB.le hBound)
  let us : ℕ → Point n → ℝ := fun j =>
    dirichletClassicalChartHeat g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 a (fData j)
  let v := dirichletMinimalBoundedHeatChart g hK μ hμ O hO f a
  have hContain : ∀ j z,z ∈ V → z ∈ chartTarget a ∧ chartInv a z ∈ O (J0+j) := by
    intro j z hz
    exact ⟨hVt (subset_closure hz),(hJ0 (J0+j) (Nat.le_add_right _ _)).1 z (subset_closure hz)⟩
  have hI : Ioo l r ⊆ Ioi (0 : ℝ) := fun t ht => hl.trans ht.1
  have hSub (j : ℕ) : V ×ˢ Ioo l r ⊆
      {z | z ∈ chartTarget a ∧ chartInv a z ∈ O (J0+j)} ×ˢ Ioi (0 : ℝ) :=
    fun _ hp => ⟨hContain j _ hp.1,hI hp.2⟩
  have hs : ∀ j,ContDiffOn ℝ ∞ (us j) (V ×ˢ Ioo l r) := fun j =>
    (dirichletClassicalChartHeat_smooth g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 a (fData j)).mono (hSub j)
  have heq : ∀ j p,p ∈ V ×ˢ Ioo l r → linearOp (V ×ˢ Ioo l r)
      (scalarHeatChartCoeff g a) (fun _ _ => 0) (us j) p=0 := by
    intro j p hp
    have hOp := linearOp_congr_open_sets (hV.prod isOpen_Ioo)
      ((dirichletChartInterior_open (O (J0+j)) (hO.1 (J0+j)).1 a).prod isOpen_Ioi)
      (scalarHeatChartCoeff g a) (fun _ _ => 0) hp (hSub j hp)
      (Filter.EventuallyEq.refl (𝓝 p) (us j))
    exact hOp.trans (dirichletClassicalChartHeat_equation g hK μ hμ
      (O (J0+j)) (hO.1 (J0+j)).1 a (fData j) p (hSub j hp))
  have hb : ∀ j p,p ∈ V ×ˢ Ioo l r → |us j p| ≤ B := by
    intro j p hp
    have hData : ∀ᵐ y ∂μ.restrict (O (J0+j)),|fData j y| ≤ B := by
      filter_upwards [scalarToLp_coe (bounded_source_precompact_scalarL2 g μ hμ
        (O (J0+j)) (hO.1 (J0+j)) f hf B hB.le hBound)] with y hy
      rw [show fData j y=f y from hy]
      exact hBound y
    exact dirichletClassicalHeat_abs_bound g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 B hB
      (fData j) hData (hI hp.2) (chartInv a p.1) (hContain j p.1 hp.1).2
  have hTail : Tendsto (fun j : ℕ => J0+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat J0
  have hp : ∀ p ∈ V ×ˢ Ioo l r,Tendsto (fun j => us j p) atTop (𝓝 (v p)) := by
    intro p hp
    have hLimit := (dirichletExhaustionKernels_bounded_integral_tendsto g hK μ hμ O hO
      f hf B hB.le hBound (hI hp.2) (chartInv a p.1)).comp hTail
    have hSeq : (fun j => us j p)=(fun j => ∫ y,
        dirichletExhaustionKernels g hK μ hμ O hO (J0+j) p.2 (chartInv a p.1) y*f y ∂μ) := by
      funext j
      have hE := dirichletKernelCandidate_evolution_inside g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1
        (hI hp.2) (chartInv a p.1) (hContain j p.1 hp.1).2 f
        (bounded_source_precompact_scalarL2 g μ hμ (O (J0+j)) (hO.1 (J0+j)) f hf B hB.le hBound)
      rw [boundedKernelEvolution,if_neg (hI hp.2).ne'] at hE
      exact hE.symm
    rw [hSeq]
    exact hLimit
  have hAB := scalarHeatChartCoeff_smooth g a (subset_closure.trans hVt) (Ioo l r)
  obtain ⟨lam,upper,hEll⟩ := scalarHeatChartCoeff_elliptic g a hVc hVt (Ioo l r)
  have hEllV : Elliptic (V ×ˢ Ioo l r) (scalarHeatChartCoeff g a) lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p ⟨subset_closure hp.1,hp.2⟩⟩
  have hLimit := bounded_classical_caloric_limit (complexManifold_dimension_pos M)
    V l r lam upper hV hVc (scalarHeatChartCoeff g a) (fun _ _ => 0) hAB hEllV
    us v B hB.le hs heq hb hp
  exact ⟨hLimit.1,hLimit.2.1⟩

end Yau.Proofs.F03Aux

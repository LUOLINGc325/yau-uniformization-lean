import Yau.Proofs.F03BoundedCaloricLimit
import Yau.Proofs.F03KernelPackedEquation
import Yau.Proofs.F03KernelProductBuffers
import Yau.Proofs.F03ExhaustionKernelBuffers

/-! The actual exhaustion ciSup has a smooth packed representative equal at every point. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

def dirichletMinimalPackedKernel (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (x y : M.Carrier) (p : Point (n+n)) : ℝ :=
  dirichletMinimalKernelCandidate g hK μ hμ O hO p.2
    (chartInv x ((kernelPairPack n).symm p.1).1) (chartInv y ((kernelPairPack n).symm p.1).2)

theorem dirichletMinimalPackedKernel_limit
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (hx : IsOpen Ox) (hy : IsOpen Oy)
    (hxc : IsCompact (closure Ox)) (hyc : IsCompact (closure Oy))
    (hxt : closure Ox ⊆ chartTarget x) (hyt : closure Oy ⊆ chartTarget y)
    (l r : ℝ) (hl : 0 < l) :
    ∃ J0 : ℕ,
      ContDiffOn ℝ ∞ (dirichletMinimalPackedKernel g hK μ hμ O hO x y) (kernelProductSpace Ox Oy ×ˢ Ioo l r) ∧
      (∀ p ∈ kernelProductSpace Ox Oy ×ˢ Ioo l r,linearOp (kernelProductSpace Ox Oy ×ˢ Ioo l r)
        (kernelProductCoeff (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y)) (fun _ _ => 0)
        (dirichletMinimalPackedKernel g hK μ hμ O hO x y) p=0) ∧
      ∀ K : Set (Point (n+n)),IsCompact K → K ⊆ kernelProductSpace Ox Oy ×ˢ Ioo l r →
        ∀ (m : ℕ) (η : ℝ),0 < η → ∃ N : ℕ,∀ j,N ≤ j → ∀ p ∈ K,
          ‖iteratedFDeriv ℝ m (fun q =>
            dirichletPackedKernel g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 x y q-
              dirichletMinimalPackedKernel g hK μ hμ O hO x y q) p‖ < η := by
  obtain ⟨J0,hJ0⟩ := smoothExhaustion_eventually_contains_chart_compacts O hO x y
    (closure Ox) (closure Oy) hxc hyc hxt hyt
  obtain ⟨B,hB,hBound⟩ := dirichletExhaustionKernels_compact_uniform_bound g hK μ hμ O hO x y
    (closure Ox) (closure Oy) hxc hyc hxt hyt l r hl
  let Os := kernelProductSpace Ox Oy
  let A := kernelProductCoeff (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y)
  let us : ℕ → Point (n+n) → ℝ := fun j =>
    dirichletPackedKernel g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 x y
  let v := dirichletMinimalPackedKernel g hK μ hμ O hO x y
  have hContainX : ∀ j z,z ∈ Ox → z ∈ chartTarget x ∧ chartInv x z ∈ O (J0+j) := by
    intro j z hz
    exact ⟨hxt (subset_closure hz),(hJ0 (J0+j) (Nat.le_add_right _ _)).1 z (subset_closure hz)⟩
  have hContainY : ∀ j z,z ∈ Oy → z ∈ chartTarget y ∧ chartInv y z ∈ O (J0+j) := by
    intro j z hz
    exact ⟨hyt (subset_closure hz),(hJ0 (J0+j) (Nat.le_add_right _ _)).2 z (subset_closure hz)⟩
  have hI : Ioo l r ⊆ Ioi (0 : ℝ) := fun t ht => hl.trans ht.1
  have hAB := kernelHeatProductCoeff_smooth g x y Ox Oy (Ioo l r)
    (subset_closure.trans hxt) (subset_closure.trans hyt)
  obtain ⟨lam,upper,hEll⟩ := kernelHeatProductCoeff_elliptic g x y Ox Oy (Ioo l r) hxc hyc hxt hyt
  have hu : ∀ j,ContDiffOn ℝ ∞ (us j) (Os ×ˢ Ioo l r) := fun j =>
    dirichletPackedKernel_smooth g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 x y Ox Oy (Ioo l r)
      (hContainX j) (hContainY j) hI
  have hClass : ∀ j p,p ∈ Os ×ˢ Ioo l r → linearOp (Os ×ˢ Ioo l r) A (fun _ _ => 0) (us j) p=0 :=
    fun j p hp => dirichletPackedKernel_equation g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 x y
      Ox Oy (Ioo l r) hx hy isOpen_Ioo (hContainX j) (hContainY j) hI p hp
  have hUniform : ∀ j p,p ∈ Os ×ˢ Ioo l r → |us j p| ≤ B := by
    intro j p hp
    have hxy := kernelProductSpace_mem_iff.mp hp.1
    exact hBound (J0+j) _ (subset_closure hxy.1) _ (subset_closure hxy.2) p.2 ⟨hp.2.1.le,hp.2.2.le⟩
  have hTail : Tendsto (fun j : ℕ => J0+j) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat J0
  have hPoint : ∀ p ∈ Os ×ˢ Ioo l r,Tendsto (fun j => us j p) atTop (𝓝 (v p)) := by
    intro p hp
    exact (dirichletExhaustionKernels_tendsto g hK μ hμ O hO (hI hp.2)
      (chartInv x ((kernelPairPack n).symm p.1).1) (chartInv y ((kernelPairPack n).symm p.1).2)).comp hTail
  have hLimit := bounded_classical_caloric_limit (by have := complexManifold_dimension_pos M;omega)
    Os l r lam upper (kernelProductSpace_open hx hy) (kernelProductSpace_precompact Ox Oy hxc hyc)
    A (fun _ _ => 0) hAB hEll us v B hB.le hu hClass hUniform hPoint
  exact ⟨J0,hLimit.1,hLimit.2.1,hLimit.2.2.2⟩

end Yau.Proofs.F03Aux

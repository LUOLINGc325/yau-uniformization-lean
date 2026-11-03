import Yau.Proofs.F03KernelProductOperator
import Yau.Proofs.F03DirichletKernelSmooth

/-! Every actual Dirichlet kernel solves the same packed uniformly parabolic equation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings LeafProofs.L16Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

def dirichletPackedKernel (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x y : M.Carrier) (p : Point (n+n)) : ℝ :=
  dirichletKernelCandidate g hK μ hμ Ω hΩ p.2
    (chartInv x ((kernelPairPack n).symm p.1).1) (chartInv y ((kernelPairPack n).symm p.1).2)

theorem dirichletPackedKernel_smooth
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ)
    (hOx : ∀ z ∈ Ox,z ∈ chartTarget x ∧ chartInv x z ∈ Ω)
    (hOy : ∀ z ∈ Oy,z ∈ chartTarget y ∧ chartInv y z ∈ Ω) (hI : I ⊆ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (dirichletPackedKernel g hK μ hμ Ω hΩ x y) (kernelProductSpace Ox Oy ×ˢ I) := by
  apply (dirichletKernelCandidate_smooth g hK μ hμ Ω hΩ x y).comp
    (kernelPairTimePack n).symm.contDiff.contDiffOn
  intro p hp
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  exact ⟨⟨hOx _ hxy.1,hOy _ hxy.2⟩,hI hp.2⟩

theorem dirichletKernel_chart_pair_equations
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ) (hx : IsOpen Ox) (hy : IsOpen Oy) (hIopen : IsOpen I)
    (hOx : ∀ z ∈ Ox,z ∈ chartTarget x ∧ chartInv x z ∈ Ω)
    (hOy : ∀ z ∈ Oy,z ∈ chartTarget y ∧ chartInv y z ∈ Ω) (hI : I ⊆ Ioi (0 : ℝ))
    (p : Point (n+n)) (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I) :
    (linearOp (Ox ×ˢ I) (scalarHeatChartCoeff g x) (fun _ _ => 0)
      (fun q : Point n => dirichletKernelCandidate g hK μ hμ Ω hΩ q.2
        (chartInv x q.1) (chartInv y ((kernelPairPack n).symm p.1).2))
      (((kernelPairPack n).symm p.1).1,p.2)=0) ∧
    (linearOp (Oy ×ˢ I) (scalarHeatChartCoeff g y) (fun _ _ => 0)
      (fun q : Point n => dirichletKernelCandidate g hK μ hμ Ω hΩ q.2
        (chartInv x ((kernelPairPack n).symm p.1).1) (chartInv y q.1))
      (((kernelPairPack n).symm p.1).2,p.2)=0) := by
  let F : ((Space n × Space n) × ℝ) → ℝ := fun q =>
    dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv x q.1.1) (chartInv y q.1.2)
  let z := ((kernelPairPack n).symm p.1).1
  let w := ((kernelPairPack n).symm p.1).2
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  have hz := hOx z hxy.1
  have hw := hOy w hxy.2
  have ht : 0 < p.2 := hI hp.2
  have hLeft : linearOp (Ox ×ˢ I) (scalarHeatChartCoeff g x) (fun _ _ => 0)
      (fun q : Point n => F ((q.1,w),q.2)) (z,p.2)=0 := by
    exact (linearOp_congr_open_sets (p := (z,p.2)) (hx.prod hIopen) ((dirichletChartInterior_open Ω hΩ x).prod isOpen_Ioi)
      (scalarHeatChartCoeff g x) (fun _ _ => 0) ⟨hxy.1,hp.2⟩ ⟨hz,ht⟩ Filter.EventuallyEq.rfl).trans
      (dirichletKernelCandidate_chart_equation g hK μ hμ Ω hΩ x (chartInv y w) hw.2 (z,p.2) ⟨hz,ht⟩)
  have hRight : linearOp (Oy ×ˢ I) (scalarHeatChartCoeff g y) (fun _ _ => 0)
      (fun q : Point n => F ((z,q.1),q.2)) (w,p.2)=0 := by
    have hGerm : (fun q : Point n => F ((z,q.1),q.2)) =ᶠ[𝓝 (w,p.2)]
        (fun q : Point n => dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv y q.1) (chartInv x z)) := by
      filter_upwards [(continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds ht))] with q hq
      exact dirichletKernelCandidate_symm g hK μ hμ Ω hΩ hq _ _
    exact (linearOp_congr_open_sets (p := (w,p.2)) (hy.prod hIopen) ((dirichletChartInterior_open Ω hΩ y).prod isOpen_Ioi)
      (scalarHeatChartCoeff g y) (fun _ _ => 0) ⟨hxy.2,hp.2⟩ ⟨hw,ht⟩ hGerm).trans
      (dirichletKernelCandidate_chart_equation g hK μ hμ Ω hΩ y (chartInv x z) hz.2 (w,p.2) ⟨hw,ht⟩)
  exact ⟨hLeft,hRight⟩

theorem dirichletPackedKernel_equation
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ) (hx : IsOpen Ox) (hy : IsOpen Oy) (hIopen : IsOpen I)
    (hOx : ∀ z ∈ Ox,z ∈ chartTarget x ∧ chartInv x z ∈ Ω)
    (hOy : ∀ z ∈ Oy,z ∈ chartTarget y ∧ chartInv y z ∈ Ω) (hI : I ⊆ Ioi (0 : ℝ))
    (p : Point (n+n)) (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I) :
    linearOp (kernelProductSpace Ox Oy ×ˢ I)
      (kernelProductCoeff (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y)) (fun _ _ => 0)
      (dirichletPackedKernel g hK μ hμ Ω hΩ x y) p=0 := by
  let F : ((Space n × Space n) × ℝ) → ℝ := fun q =>
    dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv x q.1.1) (chartInv y q.1.2)
  let z := ((kernelPairPack n).symm p.1).1
  let w := ((kernelPairPack n).symm p.1).2
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  have hz := hOx z hxy.1
  have hw := hOy w hxy.2
  have ht : 0 < p.2 := hI hp.2
  have hF : ContDiffAt ℝ 2 F ((kernelPairTimePack n).symm p) :=
    ((dirichletKernelCandidate_smooth g hK μ hμ Ω hΩ x y).contDiffAt
      ((((dirichletChartInterior_open Ω hΩ x).prod (dirichletChartInterior_open Ω hΩ y)).prod isOpen_Ioi).mem_nhds
        (show (kernelPairTimePack n).symm p ∈ _ from ⟨⟨hz,hw⟩,ht⟩))).of_le (by simp)
  obtain ⟨hLeft,hRight⟩ := dirichletKernel_chart_pair_equations g hK μ hμ Ω hΩ x y
    Ox Oy I hx hy hIopen hOx hOy hI p hp
  change linearOp _ _ _ (fun q => F ((kernelPairTimePack n).symm q)) p=0
  rw [kernelProduct_linearOp Ox Oy I hx hy hIopen (scalarHeatChartCoeff g x) (scalarHeatChartCoeff g y) F p hp hF]
  change (1/2 : ℝ)*(_+_)=0
  rw [hLeft,hRight,add_zero,mul_zero]

theorem dirichletPackedKernel_partial_equations
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x y : M.Carrier)
    (Ox Oy : Set (Space n)) (I : Set ℝ) (hx : IsOpen Ox) (hy : IsOpen Oy) (hIopen : IsOpen I)
    (hOx : ∀ z ∈ Ox,z ∈ chartTarget x ∧ chartInv x z ∈ Ω)
    (hOy : ∀ z ∈ Oy,z ∈ chartTarget y ∧ chartInv y z ∈ Ω) (hI : I ⊆ Ioi (0 : ℝ))
    (p : Point (n+n)) (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I) :
    (timeD (kernelProductSpace Ox Oy ×ˢ I) (dirichletPackedKernel g hK μ hμ Ω hΩ x y) p-
      (∑ i,∑ j,scalarHeatChartCoeff g x (((kernelPairPack n).symm p.1).1,p.2) i j*
        spatialDD (dirichletPackedKernel g hK μ hμ Ω hΩ x y) p
          (realVec (kernelRealIndexLeft n i)) (realVec (kernelRealIndexLeft n j)))=0) ∧
    (timeD (kernelProductSpace Ox Oy ×ˢ I) (dirichletPackedKernel g hK μ hμ Ω hΩ x y) p-
      (∑ i,∑ j,scalarHeatChartCoeff g y (((kernelPairPack n).symm p.1).2,p.2) i j*
        spatialDD (dirichletPackedKernel g hK μ hμ Ω hΩ x y) p
          (realVec (kernelRealIndexRight n i)) (realVec (kernelRealIndexRight n j)))=0) := by
  let F : ((Space n × Space n) × ℝ) → ℝ := fun q =>
    dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv x q.1.1) (chartInv y q.1.2)
  let z := ((kernelPairPack n).symm p.1).1
  let w := ((kernelPairPack n).symm p.1).2
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  have hz := hOx z hxy.1
  have hw := hOy w hxy.2
  have ht : 0 < p.2 := hI hp.2
  have hF : ContDiffAt ℝ 2 F ((kernelPairTimePack n).symm p) :=
    ((dirichletKernelCandidate_smooth g hK μ hμ Ω hΩ x y).contDiffAt
      ((((dirichletChartInterior_open Ω hΩ x).prod (dirichletChartInterior_open Ω hΩ y)).prod isOpen_Ioi).mem_nhds
        (show (kernelPairTimePack n).symm p ∈ _ from ⟨⟨hz,hw⟩,ht⟩))).of_le (by simp)
  obtain ⟨hLeft,hRight⟩ := dirichletKernel_chart_pair_equations g hK μ hμ Ω hΩ x y
    Ox Oy I hx hy hIopen hOx hOy hI p hp
  constructor
  · have h := kernelProduct_left_linearOp Ox Oy I hx hy hIopen (scalarHeatChartCoeff g x) F p hp hF
    rw [hLeft] at h
    exact h.symm
  · have h := kernelProduct_right_linearOp Ox Oy I hx hy hIopen (scalarHeatChartCoeff g y) F p hp hF
    rw [hRight] at h
    exact h.symm

end Yau.Proofs.F03Aux

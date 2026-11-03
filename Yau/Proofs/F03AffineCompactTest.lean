import Yau.Proofs.F03DirichletMixedGreen

/-! Constant plus genuine compact smooth functions as coercive boundary tests. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem scalarExterior_const (c : ℝ) :
    scalarExterior (M := M) (fun _ => c) = 0 := by
  apply realForm_eq_of_center_components
  intro x I
  rw [scalarExterior_components (M := M) (smoothFn_const c) x
    (z := chartPt x x) (mem_extChartAt_target x) I]
  simp only [rDeriv]
  change (fderiv ℝ (inChart x (fun _ : M.Carrier => c)) (chartPt x x)) (realVec (I 0))=0
  change (fderiv ℝ (fun _ : ComplexVector n => c) (chartPt x x)) (realVec (I 0))=0
  simp

theorem scalarExterior_add_const {k : M.Carrier → ℝ} (hk : SmoothFn k) (c : ℝ) :
    scalarExterior (fun x => k x+c) = scalarExterior k := by
  change scalarExterior (k+(fun _ => c))=scalarExterior k
  rw [scalarExterior_add hk (smoothFn_const c),scalarExterior_const,add_zero]

theorem affineCompact_scalarL2 (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hfin : μ Ω < ⊤)
    (k : ScalarEnergyDomain g μ hμ) (c : ℝ) :
    ScalarL2 (μ.restrict Ω) (fun x => k x+c) := by
  letI : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
  exact (scalarL2_iff_memLp _ _).mpr
    (((scalarEnergyDomain_memLp g μ hμ k).restrict Ω).add (memLp_const c))

theorem affineCompact_toLp (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (k : ScalarEnergyDomain g μ hμ) (c : ℝ)
    (hc : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => c))
    (hk : ScalarL2 (μ.restrict Ω) (fun x => k x+c)) :
    scalarToLp hk = l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k)+scalarToLp hc := by
  apply Lp.ext
  filter_upwards [scalarToLp_coe hk,scalarToLp_coe hc,
    restrictL2_coe μ Ω (scalarEnergyDomainL2 g μ hμ k),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ k),
    Lp.coeFn_add (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k)) (scalarToLp hc)]
    with x hsum hconst hres hkx hadd
  rw [hsum,hadd,Pi.add_apply,hconst]
  exact congrArg (fun z => z+c) (hres.trans hkx).symm

theorem dirichlet_affine_compact_green (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (k : ScalarEnergyDomain g μ hμ) (c : ℝ)
    (hc : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => c))
    (hk : ScalarL2 (μ.restrict Ω) (fun x => k x+c))
    (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (scalarToLp hk) (dirichletL2 g μ hμ Ω v)+
      (1/2 : ℝ)*inner ℝ (scalarEnergyDomainD g μ hμ Ω k) (dirichletD g μ hμ Ω v) =
      inner ℝ (l2Restriction μ Ω
        (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))+scalarToLp hc)
        (dirichletL2 g μ hμ Ω v) := by
  rw [affineCompact_toLp g μ hμ Ω k c hc hk,inner_add_left,inner_add_left]
  linarith only [dirichlet_compact_green g hK μ hμ Ω hΩ k v]

end Yau.Proofs.F03Aux

import Yau.Proofs.F03AffineCompactSource
import Yau.Proofs.F03CoerciveComparison
import Yau.Proofs.F03DirichletCoerciveSource
import Yau.Proofs.F03DirichletKernelMass
import Yau.Proofs.F03L2Parts
import Yau.Proofs.F04ShiftPositivePairing

/-! Coercive comparison against a genuine nonnegative affine compact barrier. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau F04Proof HeatConcreteBindings LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem dirichletHeat_le_affine_barrier (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω)
    (f : Lp ℝ 2 (μ.restrict Ω)) {t : ℝ} (ht : 0 < t)
    (k : ScalarEnergyDomain g μ hμ) (c : ℝ) (hr0 : ∀ x ∈ Ω, 0 ≤ k x+c)
    (hsource : ∀ᵐ x ∂μ.restrict Ω,
      k x+c < dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t →
        dirichletHeatInverse g μ hμ Ω t f x ≤ k x+c-laplacian g.form (fun y => k y+c) x) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t ≤ k x+c := by
  let r : M.Carrier → ℝ := fun x => k x+c
  have hr : SmoothFn r := fun a => (k.2.1 a).add contDiffOn_const
  have hfin := smoothPrecompactDomain_volume_lt_top g μ hμ Ω hΩ
  letI : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
  have hc : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => c) :=
    (scalarL2_iff_memLp _ _).mpr (memLp_const c)
  have hr2 : ScalarL2 (μ.restrict Ω) r := affineCompact_scalarL2 g μ hμ Ω hfin k c
  have hd : L2RealForm g.form (μ.restrict Ω) (scalarExterior r) := by
    simpa only [r,scalarExterior_add_const k.2.1 c] using
      scalarExterior_l2_restrict g μ hμ Ω k.2.1 k.2.2
  let u := dirichletHeatEnergy g μ hμ Ω t f
  let w := dirichletShiftPosPart g μ hμ Ω hΩ.1 r hr hr0 hr2 hd u
  let G := l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))+
    scalarToLp hc
  have hpair := dirichletShiftPosPart_pairings g μ hμ Ω hΩ.1 r hr hr0 hr2 hd u
  have hs := dirichletShiftPosPart_spec g μ hμ Ω hΩ.1 r hr hr0 hr2 hd u
  have hUae : (dirichletL2 g μ hμ Ω u : M.Carrier → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t) := by
    change (dirichletL2 g μ hμ Ω (dirichletHeatEnergy g μ hμ Ω t f) : M.Carrier → ℝ) =ᵐ[μ.restrict Ω] _
    rw [dirichletHeatEnergy_L2 g μ hμ Ω ht f]
    exact (dirichletClassicalHeat_ae g hK μ hμ Ω hΩ.1 f ht).symm
  have hWae : (dirichletL2 g μ hμ Ω w : M.Carrier → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => max (dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t-r x) 0) := by
    rw [hs.1]
    filter_upwards [Lp.coeFn_posPart (dirichletL2 g μ hμ Ω u-scalarToLp hr2),
      Lp.coeFn_sub (dirichletL2 g μ hμ Ω u) (scalarToLp hr2),scalarToLp_coe hr2,hUae]
      with x hp hsub hR hU
    rw [hp,hsub,Pi.sub_apply,hR,hU]
  have hnorm : ‖w‖^2=inner ℝ (dirichletHeatInverse g μ hμ Ω t f-G) (dirichletL2 g μ hμ Ω w) :=
    dirichlet_coercive_difference_norm g μ hμ Ω u w (scalarToLp hr2)
      (dirichletHeatInverse g μ hμ Ω t f) G
      (realizeL2Form g (μ.restrict Ω) (L2FormSpace.ofSection (scalarExterior r) hd))
      (dirichletHeatEnergy_coercive_source g μ hμ Ω t f w)
      (dirichlet_affine_compact_coerciveGreen g hK μ hμ Ω hΩ.1.measurableSet k c hc hr2 hd w)
      hpair.1 hpair.2
  have hw : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ dirichletL2 g μ hμ Ω w x := by
    filter_upwards [hWae] with x hx
    rw [hx]
    exact le_max_right _ _
  have hFG : ∀ᵐ x ∂μ.restrict Ω, 0 < dirichletL2 g μ hμ Ω w x →
      dirichletHeatInverse g μ hμ Ω t f x ≤ G x := by
    filter_upwards [hWae,hsource,affineCompact_source_ae g μ hμ Ω k c hc] with x hW hS hG
    intro hx
    rw [hW] at hx
    have hactive : r x < dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t :=
      sub_pos.mp ((lt_max_iff.mp hx).resolve_right (lt_irrefl 0))
    exact (hS hactive).trans_eq hG.symm
  have hwzero := dirichlet_coercive_test_zero g μ hμ Ω w (dirichletHeatInverse g μ hμ Ω t f) G hnorm hw hFG
  have hzero : dirichletL2 g μ hμ Ω w=0 := by rw [hwzero,map_zero]
  apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ.1 _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ.1 f ht)
    (continuous_of_smoothFn hr).continuousOn
  have hzeroae := Lp.ext_iff.mp hzero
  filter_upwards [hWae,hzeroae,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict Ω)] with x hW hzero hz
  have hm : max (dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t-r x) 0=0 :=
    hW.symm.trans (hzero.trans hz)
  have hle := le_max_left (dirichletClassicalHeat g hK μ hμ Ω hΩ.1 f x t-r x) 0
  rw [hm] at hle
  exact sub_nonpos.mp hle

end Yau.Proofs.F03Aux

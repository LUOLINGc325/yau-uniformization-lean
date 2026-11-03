import Yau.Proofs.F03AffineCompactTest

/-! The affine compact Green source is the actual scalar q-L_g q. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem affineCompact_source_ae (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (k : ScalarEnergyDomain g μ hμ) (c : ℝ)
    (hc : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => c)) :
    ((l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))+
      scalarToLp hc : Lp ℝ 2 (μ.restrict Ω)) : M.Carrier → ℝ) =ᵐ[μ.restrict Ω]
      (fun x => k x+c-laplacian g.form (fun y => k y+c) x) := by
  filter_upwards [Lp.coeFn_add
      (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)))
      (scalarToLp hc),
    restrictL2_coe μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)),
    ae_restrict_of_ae (scalarEnergyDomainL2_coe g μ hμ (scalarEnergyGreenTest g μ hμ k)),
    scalarToLp_coe hc] with x hadd hres hkx hcx
  have hG : (l2Restriction μ Ω
      (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))) x=
      (scalarEnergyGreenTest g μ hμ k) x := hres.trans hkx
  rw [hadd,Pi.add_apply,hG,hcx,laplacian_add_const g.form k.2.1 c]
  change k x-laplacian g.form k x+c=k x+c-laplacian g.form k x
  ring

theorem affineCompact_form_realize (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (k : ScalarEnergyDomain g μ hμ) (c : ℝ)
    (hd : L2RealForm g.form (μ.restrict Ω) (scalarExterior (fun y => k y+c))) :
    realizeL2Form g (μ.restrict Ω)
      (L2FormSpace.ofSection (scalarExterior (fun y => k y+c)) hd) =
      scalarEnergyDomainD g μ hμ Ω k := by
  simp only [scalarExterior_add_const k.2.1 c]
  rfl

theorem dirichlet_affine_compact_coerciveGreen (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (k : ScalarEnergyDomain g μ hμ) (c : ℝ)
    (hc : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => c))
    (hk : ScalarL2 (μ.restrict Ω) (fun y => k y+c))
    (hd : L2RealForm g.form (μ.restrict Ω) (scalarExterior (fun y => k y+c)))
    (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (scalarToLp hk) (dirichletL2 g μ hμ Ω v)+
      (1/2 : ℝ)*inner ℝ
        (realizeL2Form g (μ.restrict Ω)
          (L2FormSpace.ofSection (scalarExterior (fun y => k y+c)) hd))
        (dirichletD g μ hμ Ω v) =
      inner ℝ (l2Restriction μ Ω
        (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k))+scalarToLp hc)
        (dirichletL2 g μ hμ Ω v) := by
  rw [affineCompact_form_realize g μ hμ Ω k c hd]
  exact dirichlet_affine_compact_green g hK μ hμ Ω hΩ k c hc hk v

end Yau.Proofs.F03Aux

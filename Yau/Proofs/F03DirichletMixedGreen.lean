import Yau.Proofs.F03DirichletCoreApprox
import Yau.Proofs.F03DirichletEnergyIdentity
import Yau.Proofs.F03L2RestrictionPairing

/-! Genuine compact ambient Green identities tested against the full supported completion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem scalarEnergyDomain_mixed_core_inner (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier)
    (k : ScalarEnergyDomain g μ hμ) (w : dirichletCore g μ hμ Ω) :
    inner ℝ k w.val =
      inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k))
        (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ w.val)) +
      (1/2 : ℝ)*inner ℝ (scalarEnergyDomainD g μ hμ Ω k) (scalarEnergyDomainD g μ hμ Ω w.val) := by
  rw [scalarEnergyDomainRestrictedL2_inner,scalarEnergyDomainD_inner,scalarEnergyDomain_inner]
  have hscalar : (∫ x in Ω, k x*w.val x ∂μ)=∫ x, k x*w.val x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (w.property hs)),mul_zero]
  have hgradient : (∫ x in Ω, scalarGradientPair g.form k w.val x ∂μ)=
      ∫ x, scalarGradientPair g.form k w.val x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [scalarGradientPair_symm g.form k w.val x]
    exact scalarGradientPair_zero_of_notMem_tsupport g.form w.val k (fun hs => hx (w.property hs))
  rw [hscalar,hgradient]
  rfl

theorem dirichlet_compact_green_core (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (k : ScalarEnergyDomain g μ hμ) (w : dirichletCore g μ hμ Ω) :
    inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k))
        (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω w)) +
      (1/2 : ℝ)*inner ℝ (scalarEnergyDomainD g μ hμ Ω k)
        (dirichletD g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω w)) =
      inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)))
        (dirichletL2 g μ hμ Ω (dirichletCoreToEnergy g μ hμ Ω w)) := by
  let v := dirichletCoreToEnergy g μ hμ Ω w
  let G := scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)
  have hZ := dirichletL2_zeroExtension g μ hμ Ω hΩ v
  change l2ZeroExtension μ Ω hΩ (dirichletL2 g μ hμ Ω v) =
    scalarEnergyL2 g μ hμ (w.val : ScalarEnergySpace g μ hμ) at hZ
  rw [scalarEnergyL2_coe] at hZ
  have hPair := l2ZeroExtension_inner_left μ Ω hΩ (dirichletL2 g μ hμ Ω v) G
  rw [hZ] at hPair
  rw [dirichletL2_core,dirichletD_core]
  calc
    _ = inner ℝ k w.val := (scalarEnergyDomain_mixed_core_inner g μ hμ Ω k w).symm
    _ = inner ℝ (k : ScalarEnergySpace g μ hμ) (w.val : ScalarEnergySpace g μ hμ) :=
      (UniformSpace.Completion.inner_coe k w.val).symm
    _ = inner ℝ (w.val : ScalarEnergySpace g μ hμ) (k : ScalarEnergySpace g μ hμ) :=
      real_inner_comm _ _
    _ = inner ℝ (scalarEnergyDomainL2 g μ hμ w.val) G := by
      rw [scalarEnergyL2_green g hK μ hμ,scalarEnergyL2_coe]
    _ = inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ w.val)) (l2Restriction μ Ω G) := by
      simpa only [v,dirichletL2_core] using hPair
    _ = _ := real_inner_comm _ _

/-- The test is any element of the actual supported closure. The compact
scalar k can cross the domain boundary; no trace-space identification is used. -/
theorem dirichlet_compact_green (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    (k : ScalarEnergyDomain g μ hμ) (v : DirichletEnergy g μ hμ Ω) :
    inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k)) (dirichletL2 g μ hμ Ω v) +
      (1/2 : ℝ)*inner ℝ (scalarEnergyDomainD g μ hμ Ω k) (dirichletD g μ hμ Ω v) =
      inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)))
        (dirichletL2 g μ hμ Ω v) := by
  let L : DirichletEnergy g μ hμ Ω → ℝ := fun w =>
    inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ k)) (dirichletL2 g μ hμ Ω w) +
      (1/2 : ℝ)*inner ℝ (scalarEnergyDomainD g μ hμ Ω k) (dirichletD g μ hμ Ω w)
  let R : DirichletEnergy g μ hμ Ω → ℝ := fun w =>
    inner ℝ (l2Restriction μ Ω (scalarEnergyDomainL2 g μ hμ (scalarEnergyGreenTest g μ hμ k)))
      (dirichletL2 g μ hμ Ω w)
  have hLC : Continuous L := (continuous_const.inner (dirichletL2 g μ hμ Ω).continuous).add
    (continuous_const.mul (continuous_const.inner (dirichletD g μ hμ Ω).continuous))
  have hRC : Continuous R := continuous_const.inner (dirichletL2 g μ hμ Ω).continuous
  obtain ⟨fs,hfs⟩ := exists_dirichletCore_tendsto g μ hμ Ω v
  have hL : Tendsto (fun j => L (dirichletCoreToEnergy g μ hμ Ω (fs j))) atTop (𝓝 (L v)) :=
    (hLC.tendsto v).comp hfs
  have hR : Tendsto (fun j => R (dirichletCoreToEnergy g μ hμ Ω (fs j))) atTop (𝓝 (R v)) :=
    (hRC.tendsto v).comp hfs
  have hEq : (fun j => L (dirichletCoreToEnergy g μ hμ Ω (fs j))) =
      (fun j => R (dirichletCoreToEnergy g μ hμ Ω (fs j))) :=
    funext (fun j => dirichlet_compact_green_core g hK μ hμ Ω hΩ k (fs j))
  rw [hEq] at hL
  exact tendsto_nhds_unique hL hR

end Yau.Proofs.F03Aux

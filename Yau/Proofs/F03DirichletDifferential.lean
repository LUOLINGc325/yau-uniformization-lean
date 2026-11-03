import Yau.Proofs.F03DirichletDensity
import Yau.Proofs.F03ScalarForms

/-! The continuous actual scalar exterior derivative on the supported energy space. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def scalarEnergyDomainD (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : ScalarEnergyDomain g μ hμ) : L2FormHilbert g (μ.restrict O) 1 :=
  realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior f)
    (scalarExterior_l2_restrict g μ hμ O f.2.1 f.2.2))

theorem scalarEnergyDomainD_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : ScalarEnergyDomain g μ hμ) : ‖scalarEnergyDomainD g μ hμ O f‖ ≤ 2 * ‖f‖ := by
  have hnorm : ‖scalarEnergyDomainD g μ hμ O f‖ ^ 2 =
      ∫ x in O, scalarGradientPair g.form f f x ∂μ := by
    rw [scalarEnergyDomainD, realizeL2Form_norm_sq]
    apply integral_congr_ae
    exact ae_of_all _ (scalarExterior_inner g.form f.2.1 f.2.1)
  have hmono : (∫ x in O, scalarGradientPair g.form f f x ∂μ) ≤
      ∫ x, scalarGradientPair g.form f f x ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (scalarGradientPair_self_nonneg g.form f))
      (scalarGradientPair_integrable g μ hμ f.2.1 f.2.1 f.2.2)
  have henergy := real_inner_self_eq_norm_sq f
  rw [scalarEnergyDomain_inner] at henergy
  unfold scalarSobolevPair scalarEnergyPair at henergy
  have hscalar : 0 ≤ ∫ x, f x * f x ∂μ := integral_nonneg (fun x => mul_self_nonneg _)
  nlinarith [norm_nonneg (scalarEnergyDomainD g μ hμ O f), norm_nonneg f]

def scalarEnergyDomainDLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    ScalarEnergyDomain g μ hμ →ₗ[ℝ] L2FormHilbert g (μ.restrict O) 1 where
  toFun := scalarEnergyDomainD g μ hμ O
  map_add' f k := by
    simp only [scalarEnergyDomainD, realizeL2Form]
    rw [← UniformSpace.Completion.coe_add]
    congr 1
    apply L2FormSpace.toSection_injective g (μ.restrict O) 1
    exact scalarExterior_add f.2.1 k.2.1
  map_smul' c f := by
    simp only [RingHom.id_apply, scalarEnergyDomainD, realizeL2Form]
    rw [← UniformSpace.Completion.coe_smul]
    congr 1
    apply L2FormSpace.toSection_injective g (μ.restrict O) 1
    exact scalarExterior_smul c f.2.1

def scalarEnergyDomainDCLM (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    ScalarEnergyDomain g μ hμ →L[ℝ] L2FormHilbert g (μ.restrict O) 1 :=
  (scalarEnergyDomainDLinear g μ hμ O).mkContinuous 2
    (scalarEnergyDomainD_norm_le g μ hμ O)

def scalarEnergyD (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    ScalarEnergySpace g μ hμ →L[ℝ] L2FormHilbert g (μ.restrict O) 1 :=
  (scalarEnergyDomainDCLM g μ hμ O).extend UniformSpace.Completion.toComplL

theorem scalarEnergyD_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : ScalarEnergyDomain g μ hμ) :
    scalarEnergyD g μ hμ O (f : ScalarEnergySpace g μ hμ) =
      scalarEnergyDomainD g μ hμ O f := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) f

/-- The derivative is constructed from actual scalar exterior derivatives. -/
def dirichletD (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) :
    DirichletEnergy g μ hμ O →L[ℝ] L2FormHilbert g (μ.restrict O) 1 :=
  (scalarEnergyD g μ hμ O).comp (dirichletEnergySubmodule g μ hμ O).subtypeL

theorem dirichletD_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : dirichletCore g μ hμ O) :
    dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O f) =
      scalarEnergyDomainD g μ hμ O f.val :=
  scalarEnergyD_coe g μ hμ O f.val

end Yau.Proofs.F03Aux

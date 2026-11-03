import Yau.Proofs.F04EnergyRepresentatives
import Yau.Proofs.F03ScalarL2Pairing

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.HeatConcreteBindings Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem energyRepresentative_coe (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (f : M.Carrier → ℝ) (df : RealForm M 1) (hf : ScalarEnergyClosure g.form μ O f df) :
    (dirichletL2 g μ hμ O (energyRepresentative g μ hμ O f df) : M.Carrier → ℝ)
      =ᵐ[μ.restrict O] f := by
  rw [(energyRepresentative_spec g μ hμ O f df hf).1]
  exact scalarToLp_coe hf.1

theorem energyRepresentative_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    {f v : M.Carrier → ℝ} {df dv : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (hv : ScalarEnergyClosure g.form μ O v dv) :
    Integrable (fun x => f x * v x) (μ.restrict O) ∧
      Integrable (formInner g.form df dv) (μ.restrict O) ∧
      inner ℝ (energyRepresentative g μ hμ O f df) (energyRepresentative g μ hμ O v dv) =
        (∫ x in O, f x * v x ∂μ) + (∫ x in O, formInner g.form df dv x ∂μ) / 2 := by
  have hfs := energyRepresentative_spec g μ hμ O f df hf
  have hvs := energyRepresentative_spec g μ hμ O v dv hv
  have hi := dirichletEnergy_inner g μ hμ O
    (energyRepresentative g μ hμ O f df) (energyRepresentative g μ hμ O v dv)
  rw [hfs.1, hvs.1, hfs.2, hvs.2, scalarToLp_inner hf.1 hv.1, realizeL2Form_inner] at hi
  simp only [L2FormSpace.toSection_ofSection] at hi
  refine ⟨scalarL2_product_integrable hf.1 hv.1,
    formInner_integrable g (μ.restrict O) df dv hf.2.1 hv.2.1, ?_⟩
  calc
    _ = (∫ x in O, f x * v x ∂μ) + (1 / 2 : ℝ) * ∫ x in O, formInner g.form df dv x ∂μ := hi
    _ = _ := by ring

theorem energyRepresentative_eq_iff (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O)
    {f v : M.Carrier → ℝ} {df dv : RealForm M 1}
    (hf : ScalarEnergyClosure g.form μ O f df) (hv : ScalarEnergyClosure g.form μ O v dv) :
    energyRepresentative g μ hμ O f df = energyRepresentative g μ hμ O v dv ↔
      f =ᵐ[μ.restrict O] v ∧ ∀ᵐ x ∂μ.restrict O, df x = dv x := by
  have hfs := energyRepresentative_spec g μ hμ O f df hf
  have hvs := energyRepresentative_spec g μ hμ O v dv hv
  constructor
  · intro he
    have hJ := congrArg (dirichletL2 g μ hμ O) he
    have hD := congrArg (dirichletD g μ hμ O) he
    rw [hfs.1, hvs.1] at hJ
    rw [hfs.2, hvs.2] at hD
    constructor
    · filter_upwards [scalarToLp_coe hf.1, scalarToLp_coe hv.1] with x hx hy
      exact hx.symm.trans ((congrArg (fun w : Lp ℝ 2 (μ.restrict O) => w x) hJ).trans hy)
    · exact (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mp hD
  · intro he
    apply dirichletL2_injective g hK μ hμ O hO
    rw [hfs.1, hvs.1]
    apply Lp.ext
    filter_upwards [scalarToLp_coe hf.1, scalarToLp_coe hv.1, he.1] with x hx hy heq
    exact hx.trans (heq.trans hy.symm)

end Yau.F04Proof

import Yau.Proofs.F04ShiftSmoothingCore
import Yau.Proofs.F04PositiveSmoothing
import Yau.Proofs.F04GraphDifferentialLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.HeatConcreteBindings

variable {n : ℕ} {M : ComplexManifold n}

theorem shiftSmoothingCore_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (δ : ℝ) (r : M.Carrier → ℝ) (hr2 : ScalarL2 (μ.restrict O) r)
    (f q : dirichletCore g μ hμ O)
    (hq : EqOn (q.val : M.Carrier → ℝ) (fun x => smoothPositive δ (f.val x - r x)) O) :
    dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O q) =
      smoothPositiveL2 (μ.restrict O) δ
        (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) - scalarToLp hr2) := by
  apply Lp.ext
  filter_upwards [dirichletCoreL2_ae g μ hμ O q,
    smoothPositiveL2_coe (μ.restrict O) δ
      (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) - scalarToLp hr2),
    Lp.coeFn_sub (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)) (scalarToLp hr2),
    dirichletCoreL2_ae g μ hμ O f, scalarToLp_coe hr2, ae_restrict_mem hO]
      with x hJq hβ hsub hJf hr hx
  calc
    _ = q.val x := hJq
    _ = smoothPositive δ (f.val x - r x) := hq hx
    _ = _ := by
      simpa only [hsub, Pi.sub_apply, hJf, hr] using hβ.symm

theorem shiftSmoothingCore_D (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : MeasurableSet O)
    (δ : ℝ) (r : M.Carrier → ℝ) (hr2 : ScalarL2 (μ.restrict O) r)
    (hdr2 : L2RealForm g.form (μ.restrict O) (scalarExterior r))
    (f q : dirichletCore g μ hμ O)
    (hq : ∀ x ∈ O, scalarExterior q.val x =
      multiplyRealForm (fun y => deriv (smoothPositive δ) (f.val y - r y))
        (scalarExterior f.val - scalarExterior r) x) :
    dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O q) =
      continuousFormMultiplier g (μ.restrict O) (deriv (smoothPositive δ))
        (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff δ)).2.continuous
        1 zero_le_one (smoothPositive_deriv_abs_le δ)
        (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) - scalarToLp hr2)
        (dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O f) -
          realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2)) := by
  have hdf := scalarExterior_l2_restrict g μ hμ O f.val.2.1 f.val.2.2
  have hsub : L2RealForm g.form (μ.restrict O) (scalarExterior f.val - scalarExterior r) :=
    (l2FormSubmodule g (μ.restrict O) 1).sub_mem hdf hdr2
  have he : dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O f) -
      realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (scalarExterior r) hdr2) =
      realizeL2Form g (μ.restrict O)
        (L2FormSpace.ofSection (scalarExterior f.val - scalarExterior r) hsub) := by
    rw [realize_section_sub g (μ.restrict O) _ _ hdf hdr2 hsub, dirichletD_core]
    rfl
  rw [he, continuousFormMultiplier, multiplyL2FormHilbert_realize, dirichletD_core, scalarEnergyDomainD]
  apply (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mpr
  filter_upwards [Lp.coeFn_sub (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f))
      (scalarToLp hr2), dirichletCoreL2_ae g μ hμ O f, scalarToLp_coe hr2, ae_restrict_mem hO]
      with x hc hf hr hx
  change scalarExterior q.val x =
    deriv (smoothPositive δ)
      ((dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) - scalarToLp hr2) x) •
        (scalarExterior f.val x - scalarExterior r x)
  rw [hq x hx]
  simp only [multiplyRealForm, Pi.sub_apply, hc, hf, hr]

end Yau.F04Proof

import Yau.Proofs.F04ScalarExteriorChain
import Yau.Proofs.F04ContinuousFormMultiplier

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L19Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem smoothScalar_lipschitz (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C) :
    LipschitzWith ⟨C, hC⟩ β := by
  apply lipschitzWith_of_nnnorm_deriv_le (hβ.differentiable (by simp))
  intro s
  exact_mod_cast hβC s

def scalarSmoothCompL2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (smoothScalar_lipschitz β hβ C hC hβC).compLp hβ0 f

def smoothCompositionCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (f : dirichletCore g μ hμ O) : dirichletCore g μ hμ O :=
  ⟨⟨fun x => β (f.val x), (fun c => hβ.comp_contDiffOn (f.val.2.1 c)),
    f.val.2.2.comp_left hβ0⟩, (tsupport_comp_subset hβ0 (f.val : M.Carrier → ℝ)).trans f.property⟩

theorem dirichletCoreL2_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (f : dirichletCore g μ hμ O) :
    (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) : M.Carrier → ℝ)
      =ᵐ[μ.restrict O] f.val := by
  rw [dirichletL2_core_eq_scalarToLp g μ hμ O f (dirichletCore_scalarL2 g μ hμ O f)]
  exact scalarToLp_coe _

theorem smoothCompositionCore_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (f : dirichletCore g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O
      (smoothCompositionCore g μ hμ O β hβ hβ0 f)) =
      scalarSmoothCompL2 (μ.restrict O) β hβ hβ0 C hC hβC
        (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)) := by
  apply Lp.ext
  filter_upwards [dirichletCoreL2_ae g μ hμ O (smoothCompositionCore g μ hμ O β hβ hβ0 f),
    (smoothScalar_lipschitz β hβ C hC hβC).coeFn_compLp hβ0
      (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f)),
    dirichletCoreL2_ae g μ hμ O f] with x hl hr hf
  apply hl.trans
  change β (f.val x) = ((smoothScalar_lipschitz β hβ C hC hβC).compLp hβ0
    (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f))) x
  simpa only [Function.comp_def, hf] using hr.symm

theorem smoothCompositionCore_D (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hβC : ∀ s, |deriv β s| ≤ C)
    (f : dirichletCore g μ hμ O) :
    dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O
      (smoothCompositionCore g μ hμ O β hβ hβ0 f)) =
      continuousFormMultiplier g (μ.restrict O) (deriv β)
        (contDiff_infty_iff_deriv.mp hβ).2.continuous C hC hβC
        (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f))
        (dirichletD g μ hμ O (dirichletCoreToEnergy g μ hμ O f)) := by
  rw [dirichletD_core, dirichletD_core]
  unfold continuousFormMultiplier scalarEnergyDomainD
  rw [multiplyL2FormHilbert_realize]
  apply (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mpr
  filter_upwards [dirichletCoreL2_ae g μ hμ O f] with x hx
  change scalarExterior (fun y => β (f.val y)) x =
    multiplyRealForm (fun y => deriv β
      (dirichletL2 g μ hμ O (dirichletCoreToEnergy g μ hμ O f) y)) (scalarExterior f.val) x
  rw [scalarExterior_scalar_comp f.val.2.1 β hβ]
  simp only [multiplyRealForm, hx]

end Yau.F04Proof

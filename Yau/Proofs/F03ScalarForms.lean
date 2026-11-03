import Yau.Proofs.F03ScalarZeroForm
import Yau.Proofs.F03FormRestriction
import Yau.LeafProofs.L03CompletionRepresentatives
import Yau.LeafProofs.L19ScalarEnergyCompletion

/-! Scalar differentials as actual degree-one alternating forms. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
open LeafProofs.L03 LeafProofs.L18Aux LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def scalarExterior (f : M.Carrier → ℝ) : RealForm M 1 :=
  exteriorRealForm (scalarZeroForm f)

theorem scalarExterior_represents {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    RepresentsExterior (scalarZeroForm f) (scalarExterior f) :=
  exteriorRealForm_represents _ (scalarZeroForm_smooth hf)

theorem scalarExterior_smooth {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    SmoothRealForm (scalarExterior f) :=
  exteriorRealForm_smooth _ (scalarZeroForm_smooth hf)

theorem scalarExterior_support_subset {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    closure {x | scalarExterior f x ≠ 0} ⊆ tsupport f := by
  simpa only [scalarZeroForm_tsupport] using
    representsExterior_support_subset (scalarExterior_represents hf)

theorem scalarExterior_compactlySupported {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (hc : HasCompactSupport f) :
    CompactlySupportedRealForm (scalarExterior f) :=
  hc.of_isClosed_subset isClosed_closure (scalarExterior_support_subset hf)

theorem scalarExterior_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (hc : HasCompactSupport f) :
    L2RealForm g.form μ (scalarExterior f) :=
  smooth_compactlySupported_l2RealForm g μ hμ _
    (scalarExterior_smooth hf) (scalarExterior_compactlySupported hf hc)

theorem scalarExterior_l2_restrict (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (hc : HasCompactSupport f) :
    L2RealForm g.form (μ.restrict O) (scalarExterior f) :=
  l2RealForm_restrict g.form μ O (scalarExterior_l2 g μ hμ hf hc)

theorem scalarExterior_components {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (I : Fin 1 → RIdx n) :
    formComponents (scalarExterior f) x z I = rDeriv (inChart x f) z (I 0) := by
  rw [scalarExterior_represents hf x z hz I]
  simp [exteriorComponents, scalarZeroForm_components]

theorem scalarExterior_inner (g : HermitianField M)
    {f k : M.Carrier → ℝ} (hf : SmoothFn f) (hk : SmoothFn k) (x : M.Carrier) :
    formInner g (scalarExterior f) (scalarExterior k) x = scalarGradientPair g f k x := by
  classical
  have hfc : formComponents (scalarExterior f) x (chartPt x x) =
      fun I => rDeriv (inChart x f) (chartPt x x) (I 0) :=
    funext (scalarExterior_components hf x (mem_extChartAt_target x))
  have hkc : formComponents (scalarExterior k) x (chartPt x x) =
      fun I => rDeriv (inChart x k) (chartPt x x) (I 0) :=
    funext (scalarExterior_components hk x (mem_extChartAt_target x))
  rw [formInner, hfc, hkc]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, Fin.prod_univ_one]
  rw [scalarGradientPair, chartGradientPair_eq_sum]
  trans ∑ a : RIdx n, ∑ b : RIdx n,
    rDeriv (inChart x f) (chartPt x x) a * rDeriv (inChart x k) (chartPt x x) b *
      (realMetricFn g x (chartPt x x))⁻¹ a b
  · refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (RIdx n)) _ _ ?_
    intro I
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (RIdx n)) _ _ ?_
    intro J
    rfl
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem scalarExterior_add {f k : M.Carrier → ℝ} (hf : SmoothFn f) (hk : SmoothFn k) :
    scalarExterior (f + k) = scalarExterior f + scalarExterior k := by
  unfold scalarExterior
  rw [scalarZeroForm_add]
  exact exteriorRealForm_add _ _ (scalarZeroForm_smooth hf) (scalarZeroForm_smooth hk)

theorem scalarExterior_smul (c : ℝ) {f : M.Carrier → ℝ} (hf : SmoothFn f) :
    scalarExterior (c • f) = c • scalarExterior f := by
  unfold scalarExterior
  rw [scalarZeroForm_smul]
  exact exteriorRealForm_smul _ _ (scalarZeroForm_smooth hf)

theorem scalarExterior_unique {f : M.Carrier → ℝ} (hf : SmoothFn f)
    {A : RealForm M 1} (hA : RepresentsExterior (scalarZeroForm f) A) :
    A = scalarExterior f := by
  apply realForm_eq_of_center_components
  intro x I
  rw [hA x (chartPt x x) (mem_extChartAt_target x) I,
    scalarExterior_represents hf x (chartPt x x) (mem_extChartAt_target x) I]

end Yau.Proofs.F03Aux

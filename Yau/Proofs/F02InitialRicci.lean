import Yau.Proofs.F02Elementary
import Yau.LeafProofs.L12Complete

/-! The initial Ricci sign needed for volume comparison follows directly
from the given flow's metric inequality and its derivative at zero. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ}

theorem initialRicci_posSemidef (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) (x : Pt X) :
    (ricci X.metric.form x).PosSemidef := by
  let D : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => t⁻¹ • (gMat X.metric.form x - gMat (h t) x)
  have hlim : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 (ricci X.metric.form x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hd := (hf.1.2.2.2 x 0 le_rfl i j).mono
      (Set.Ioi_subset_Ici_self : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0)
    have hs := ((hasDerivWithinAt_iff_tendsto_slope'
      (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hd).neg
    have heq : (fun t => -slope (fun t => gMat (h t) x i j) 0 t) =
        fun t => t⁻¹ • (gMat X.metric.form x i j - gMat (h t) x i j) := by
      funext t
      rw [slope_def_module]
      simp only [sub_zero, hf.1.1, ← smul_neg, neg_sub]
    rw [heq] at hs
    simpa only [D, Pi.smul_apply, Matrix.smul_apply, Matrix.sub_apply, hf.1.1, neg_neg] using hs
  apply Matrix.posSemidef_is_closed.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hf.2.2.2.2.1 t ht.le x).smul (inv_nonneg.mpr ht.le)

/-- The already-proved exact Bishop--Gromov leaf now applies to precisely
the initial metric and every genuine volume witness of the original flow. -/
theorem flow_initial_volume_comparison (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    μ (distBall X.metric.form o R) ≤
      ENNReal.ofReal ((R / r) ^ (2 * n)) * μ (distBall X.metric.form o r) := by
  exact LeafProofs.L12 n X.manifold X.metric X.complete_metric X.kahler_metric
    (initialRicci_posSemidef X o h U P ρ hf) μ hμ o r R hr hrR

end Yau.Proofs.F02Aux

import Yau.Proofs.V03FourierEnergy
import Yau.Proofs.V03Energy

/-! Constant competitors for the original admissible class have exactly
zero computed energy, including Gauss and logarithmic Fourier terms. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def constantVariationDisc (y : CotangentPoint X.manifold) (s : ℝ) : VariationDisc X :=
  { f := fun _ => y, w := fun _ => 0, s := s }

theorem cotangentDisc_const {m : ℕ} {M : ComplexManifold m} (y : CotangentPoint M) :
    CotangentDisc (fun _ : ℂ => y) :=
  ⟨contMDiffOn_const, fun _ _ => contDiffWithinAt_const⟩

theorem scalarDSq_const (c : ℝ) : scalarDSq (fun _ => c) = 0 := by
  have hb := boundaryDSq_le_angularDerivative (u := fun _ => (c : ℂ)) (u' := fun _ => 0)
    (fun θ _ => hasDerivAt_const θ (c : ℂ)) intervalIntegrable_const rfl (by simp)
  apply le_antisymm ?_ bot_le
  simpa only [scalarDSq, bot_eq_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    intervalIntegral.integral_zero, mul_zero, ENNReal.ofReal_zero] using hb

theorem constantVariationEnergy_zero (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (s : ℝ) :
    variationEnergy d j (constantVariationDisc y s) = 0 := by
  have hn : hermitianNormSq (X.metric.form y.1) 0 = 0 :=
    ((X.metric.form y.1).positive_definite 0).2.mpr rfl
  have hbase : discArea X.metric.form (fun _ : ℂ => y.1) = 0 := by
    simp [discArea, hn]
  have hamb : euclideanArea (fun _ : ℂ => d.G y) = 0 := by
    simp [euclideanArea]
  have hgauss : gaussArea d.G (fun _ : ℂ => y) = 0 := by
    simp [gaussArea, wirt, wirtBar]
  simp only [variationEnergy, constantVariationDisc, hbase, hamb, hgauss,
    ENNReal.ofReal_zero, zero_add, deriv_const, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, MeasureTheory.lintegral_zero,
    scalarDSq_const, add_zero]

theorem constantVariation_admissible (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (s : ℝ) (hs : 0 < s) (hsT : s < d.T)
    (hc : InCotangentTimeChart d.chart y s (centerCylinder d))
    (hy : y ∈ boundaryRegion d j) : AdmissibleVariationDisc d j (constantVariationDisc y s) := by
  refine ⟨cotangentDisc_const y, contDiffOn_const, rfl, hs, hsT, hc, ?_, fun _ => hy, ?_⟩
  · intro ζ _
    simpa [discTime, constantVariationDisc] using hsT
  · rw [constantVariationEnergy_zero]
    exact ENNReal.zero_ne_top

end Yau.Blueprint.V03Proof

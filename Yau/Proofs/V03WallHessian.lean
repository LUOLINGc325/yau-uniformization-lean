import Yau.Proofs.V03ClearedWallMatrix
import Yau.Proofs.V03LeviLinear
import Yau.Proofs.V03DiscScalars

/-! The two actual cutoff profiles have smooth native chart expressions.
The reciprocal-wall Hessian admits a polynomial extension through both
cutoff zero sets. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem leviMatrix_add_const (f : E → ℝ) (c : ℝ) (z : E) (dir : ι → E) :
    leviMatrix (fun y => f y + c) z dir = leviMatrix f z dir := by
  ext a b
  simp only [leviMatrix, Complex.ofReal_add, wirtBar, fderiv_add_const]

def clearedWallHessian (f g : E → ℝ) (m : ℕ) (dir : ι → E) (z : E) : Matrix ι ι ℂ :=
  ((g z : ℂ) ^ m) • clearedReciprocalMatrix f m dir z +
    ((f z : ℂ) ^ m) • clearedReciprocalMatrix g m dir z

theorem clearedWallHessian_eq {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hfn : f z ≠ 0) (hgn : g z ≠ 0) (dir : ι → E) {m : ℕ} (hm : 3 ≤ m) :
    clearedWallHessian f g m dir z =
      (((f z * g z) ^ m : ℝ) : ℂ) •
        leviMatrix (fun y => ((f y)⁻¹ - 1) + ((g y)⁻¹ - 1)) z dir := by
  have hfun : (fun y => ((f y)⁻¹ - 1) + ((g y)⁻¹ - 1)) =
      (fun y => ((f y)⁻¹ + (g y)⁻¹) + (-2)) := by funext y; ring
  have hfi : ContDiffAt ℝ 2 (fun y => (f y)⁻¹) z := hf.inv hfn
  have hgi : ContDiffAt ℝ 2 (fun y => (g y)⁻¹) z := hg.inv hgn
  rw [hfun, leviMatrix_add_const, leviMatrix_add (f := fun y => (f y)⁻¹)
    (g := fun y => (g y)⁻¹) hfi hgi dir]
  unfold clearedWallHessian
  rw [clearedReciprocalMatrix_eq hf hfn dir hm, clearedReciprocalMatrix_eq hg hgn dir hm]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_pow,
    Complex.ofReal_mul, mul_pow]
  ring

theorem clearedWallHessian_entry_contDiffOn {U : Set E} (hU : IsOpen U) {f g : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (m : ℕ) (dir : ι → E) (a b : ι) :
    ContDiffOn ℝ ∞ (fun z => clearedWallHessian f g m dir z a b) U := by
  exact (((Complex.ofRealCLM.contDiff.comp_contDiffOn hg).pow m).mul
    (clearedReciprocalMatrix_entry_contDiffOn hU hf m dir a b)).add
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn hf).pow m).mul
      (clearedReciprocalMatrix_entry_contDiffOn hU hg m dir a b))

theorem clearedWallHessian_isHermitian {f g : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (dir : ι → E) {m : ℕ} (hm : 4 ≤ m) :
    (clearedWallHessian f g m dir z).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply (clearedReciprocalMatrix_isHermitian hf dir hm).smul
    simp [IsSelfAdjoint]
  · apply (clearedReciprocalMatrix_isHermitian hg dir hm).smul
    simp [IsSelfAdjoint]

variable {n q : ℕ} {X : KahlerManifold n}

theorem deltaBase_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun z => deltaBase d j (cotangentChartInv x z).1) (cotangentTarget x) := by
  have hu : ContDiffOn ℝ ∞ (fun z : CotangentCoord n => d.u (chartInv x z.1))
      (cotangentTarget x) :=
    (hd.2.2.2.1.1 x).comp contDiff_fst.contDiffOn (fun z hz => hz.1)
  exact (setup_wallProfiles hd).1.comp_contDiffOn (hu.div_const (d.A j))

theorem deltaFiber_chart_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) :
    ContDiffOn ℝ ∞ (fun z => deltaFiber d j (cotangentChartInv x z)) (cotangentTarget x) := by
  have hnorm : ContDiffOn ℝ ∞
      (fun z => dualNorm (d.h 0) (cotangentChartInv x z).1 (cotangentChartInv x z).2)
      (cotangentTarget x) := by
    rw [hd.2.2.1.1.1.1]
    exact (dualNormChart_contDiffOn X.metric x).congr
      (fun z hz => dualNorm_cotangentChartInv X.metric.form x hz)
  exact (setup_wallProfiles hd).2.1.comp_contDiffOn (hnorm.div_const (d.B j ^ 2))

end Yau.Blueprint.V03Proof

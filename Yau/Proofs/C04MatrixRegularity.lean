import Yau.Proofs.C04ClockBasic
import Yau.Proofs.Y03MetricSmooth
import Yau.Proofs.Y03QuadraticForm

/-! Regularity and inverse differentiation of the actual physical-time metric matrices. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem gMat_time_contDiffAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun s => gMat (h s) x i j) t := by
  have hnhds : chartTarget x ×ˢ Set.Ici 0 ∈ 𝓝 (chartPt x x, t) :=
    prod_mem_nhds ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)) (Ici_mem_nhds ht)
  exact ((Blueprint.Alignment.Y03Proof.metricFamily_hMat_contDiffOn hf.1.2.1 x i j).contDiffAt hnhds).comp
    t (contDiffAt_const.prodMk contDiffAt_id)

theorem gMat_inverse_time_contDiffAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun s => (gMat (h s) x)⁻¹ i j) t := by
  have hnhds : chartTarget x ×ˢ Set.Ici 0 ∈ 𝓝 (chartPt x x, t) :=
    prod_mem_nhds ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)) (Ici_mem_nhds ht)
  exact ((Blueprint.Alignment.Y03Proof.metricFamily_hMat_inv_contDiffOn hf.1.2.1 x i j).contDiffAt hnhds).comp
    t (contDiffAt_const.prodMk contDiffAt_id)

theorem gMat_inverse_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    ∀ i j, HasDerivAt (fun s => (gMat (h s) x)⁻¹ i j)
      (((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) i j) t := by
  have hentry : ∀ i j, HasDerivAt (fun s => gMat (h s) x i j) (-ricci (h t) x i j) t :=
    fun i j => (hf.1.2.2.2 x t ht.le i j).hasDerivAt (Ici_mem_nhds ht)
  have hInv : ∀ i j, DifferentiableAt ℝ (fun s => (gMat (h s) x)⁻¹ i j) t :=
    fun i j => (gMat_inverse_time_contDiffAt X o h U P ρ hf x ht i j).differentiableAt (by simp)
  have hdet : ∀ᶠ s in 𝓝 t, IsUnit (gMat (h s) x).det := by
    exact Eventually.of_forall fun s =>
      (LeafProofs.L18Aux.hMat_posDef (h s) x (chartPt x x) (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom
  have hh := Blueprint.Alignment.Y03Proof.matrix_inverse_entry_hasDerivAt
    (fun s => gMat (h s) x) (-ricci (h t) x) hentry hInv hdet
  intro i j
  simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, neg_neg] using hh i j

theorem ricci_time_contDiffAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun s => ricci (h s) x i j) t := by
  have hc := (gMat_time_contDiffAt X o h U P ρ hf x ht i j).derivWithin (m := ∞) (by simp)
  have heq : (fun s => ricci (h s) x i j) =ᶠ[𝓝 t]
      fun s => -deriv (fun v => gMat (h v) x i j) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hd := (hf.1.2.2.2 x s hs.le i j).hasDerivAt (Ici_mem_nhds hs)
    rw [hd.deriv, neg_neg]
  exact hc.neg.congr_of_eventuallyEq heq

theorem inverse_form_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) (v : Fin n → ℂ) :
    HasDerivAt (fun s => Blueprint.Alignment.Y03Proof.matrixForm (gMat (h s) x)⁻¹ v)
      (Blueprint.Alignment.Y03Proof.matrixForm
        ((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) v) t :=
  Blueprint.Alignment.Y03Proof.matrixForm_hasDerivAt _ _ (gMat_inverse_hasDerivAt X o h U P ρ hf x ht) v

end Yau.Proofs.C04Aux

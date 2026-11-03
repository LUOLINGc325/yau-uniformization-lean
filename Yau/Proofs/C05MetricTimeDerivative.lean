import Yau.Proofs.C05ComplexMatrixDerivative
import Yau.Proofs.C05FlowRegularity

/-! The actual inverse-metric evolution follows entrywise from the original
Kähler–Ricci equation and genuine matrix inversion. -/

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint Set C04Aux
variable {n : ℕ} {X : KahlerManifold n}

set_option backward.isDefEq.respectTransparency false in
theorem gMat_time_contDiffOn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => gMat (h t) x i j) (Ioi 0) := by
  have hh := metricFamily_hMat_contDiffOn h hf.1.2.1 x i j
  have hmap : ContDiffOn ℝ ∞ (fun t : ℝ => (chartPt x x, t)) (Ioi 0) :=
    contDiffOn_const.prodMk contDiffOn_id
  have hm : MapsTo (fun t : ℝ => (chartPt x x, t)) (Ioi 0) (chartTarget x ×ˢ Ici 0) := by
    intro t ht
    change (0 : ℝ) < t at ht
    refine ⟨mem_extChartAt_target x, ?_⟩
    change (0 : ℝ) ≤ t
    exact ht.le
  have hc := hh.comp hmap hm
  exact hc

theorem gMat_time_det_ne_zero (h : Flow X) (x : Pt X) (t : ℝ) :
    (gMat (h t) x).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Yau.LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x)
      (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom)

theorem gMat_inverse_time_contDiffOn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => (gMat (h t) x)⁻¹ i j) (Ioi 0) :=
  Yau.LeafProofs.L18Aux.contDiffOn_matrix_inv (gMat_time_contDiffOn o h U P ρ hf x)
    (fun t _ => gMat_time_det_ne_zero h x t) i j

theorem gMat_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    HasDerivAt (fun s => gMat (h s) x i j) (-(ricci (h t) x i j)) t :=
  (hf.1.2.2.2 x t ht.le i j).hasDerivAt (Ici_mem_nhds ht)

theorem gMat_inverse_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (i j : Fin n) :
    HasDerivAt (fun s => (gMat (h s) x)⁻¹ i j)
      (((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) i j) t := by
  have hi := fderiv_complex_matrix_inv_entry isOpen_Ioi
    (gMat_time_contDiffOn o h U P ρ hf x)
    (fun s _ => gMat_time_det_ne_zero h x s) ht (1 : ℝ) i j
  have hDA : Matrix.of (fun p q => fderiv ℝ (fun s => gMat (h s) x p q) t 1) =
      -ricci (h t) x := by
    ext p q
    simpa only [Matrix.of_apply, fderiv_apply_one_eq_deriv, Matrix.neg_apply] using
      (gMat_hasDerivAt o h U P ρ hf x ht p q).deriv
  rw [hDA, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply, neg_neg] at hi
  have hd := ((gMat_inverse_time_contDiffOn o h U P ρ hf x i j).contDiffAt
    (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)
  have he : deriv (fun s => (gMat (h s) x)⁻¹ i j) t =
      ((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) i j := by
    simpa only [fderiv_apply_one_eq_deriv] using hi
  simpa only [he] using hd.hasDerivAt

end Yau.Proofs.C05Aux

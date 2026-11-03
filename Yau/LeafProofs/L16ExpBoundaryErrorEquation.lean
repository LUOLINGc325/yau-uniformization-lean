import Yau.LeafProofs.L16ExpBoundaryJointJets
import Yau.LeafProofs.L16ExpBoundaryTransfer
import Yau.LeafProofs.L16ExpBoundaryOpenTop

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- The fixed transformed datum is differentiated only in the open cylinder. -/
theorem log_error_interior_regularity {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {T m : ℝ} (hm : 0 < m) {q P : Point n → ℝ}
    (hq : C2 (cylinder (closure O) 0 T) q)
    (hP : ContDiffOn ℝ ∞ P (cylinder (closure O) 0 T))
    (hbound : ∀ z ∈ cylinder (closure O) 0 T, m ≤ q z) :
    (∀ z ∈ O ×ˢ Ioo 0 T,
      ContDiffAt ℝ 2 (fun x => Real.log (q (x,z.2))-P (x,z.2)) z.1) ∧
    ∀ z ∈ O ×ˢ Ioo 0 T,
      DifferentiableAt ℝ (fun t => Real.log (q (z.1,t))-P (z.1,t)) z.2 := by
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro z hz
    exact ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  have hPAt (z : Point n) (hz : z ∈ O ×ˢ Ioo 0 T) : ContDiffAt ℝ 2 P z :=
    (((hP.mono hUK).contDiffAt ((hO.prod isOpen_Ioo).mem_nhds hz)).of_le (by simp))
  constructor
  · intro z hz
    exact ((hq.2.2.2.2.1 z (hUK hz)).log
      (hm.trans_le (hbound z (hUK hz))).ne').sub
        ((hPAt z hz).comp z.1 (contDiffAt_id.prodMk contDiffAt_const))
  · intro z hz
    have hfiber : {t | (z.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
      ext t
      simp [cylinder,(hUK hz).1]
    have hqt := hq.2.2.2.2.2 z (hUK hz)
    rw [hfiber] at hqt
    have hqt' := hqt.differentiableAt (Icc_mem_nhds hz.2.1 hz.2.2)
    exact (hqt'.log (hm.trans_le (hbound z (hUK hz))).ne').sub
      (((hPAt z hz).differentiableAt (by norm_num)).comp z.2
        (differentiableAt_const z.1 |>.prodMk differentiableAt_id))

/-- Subtracting the fixed smooth datum gives the exact bounded-source
nondivergence equation, without ambient boundary differentiability of P. -/
theorem log_error_equation {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {T m : ℝ} (hT : 0 < T) (hm : 0 < m)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {R q P : Point n → ℝ}
    (ha : ContDiffOn ℝ ∞ a (cylinder (closure O) 0 T))
    (hq : C2 (cylinder (closure O) 0 T) q)
    (hP : ContDiffOn ℝ ∞ P (cylinder (closure O) 0 T))
    (hbound : ∀ z ∈ cylinder (closure O) 0 T, m ≤ q z)
    (heq : ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q) :
    ∀ z ∈ O ×ˢ Ioo 0 T,
      linearOp (cylinder (closure O) 0 T) (fun z => (q z)⁻¹ • a z)
        (fun z j => b z j/q z) (fun z => Real.log (q z)-P z) z =
      (1-1/q z)*R z-timeD (cylinder (closure O) 0 T) P z +
        (∑ i, ∑ j, (a z i j/q z)*spatialDD P z (Yau.realVec i) (Yau.realVec j)) +
        ∑ i, (b z i/q z)*spatialD P z (Yau.realVec i) := by
  intro z hz
  have hzQ : z ∈ cylinder (closure O) 0 T :=
    ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro w hw
    exact ⟨subset_closure hw.1,Ioo_subset_Icc_self hw.2⟩
  have hPAt : ContDiffAt ℝ 2 P z :=
    ((hP.mono hUK).contDiffAt ((hO.prod isOpen_Ioo).mem_nhds hz)).of_le (by simp)
  have hPs := hPAt.comp z.1 (contDiffAt_id.prodMk contDiffAt_const)
  have hPt : DifferentiableAt ℝ (fun t => P (z.1,t)) z.2 :=
    (hPAt.differentiableAt (by norm_num)).comp z.2
    ((differentiableAt_const z.1).prodMk differentiableAt_id)
  rw [linearOp_sub_at ((hq.2.2.2.2.1 z hzQ).log
      (hm.trans_le (hbound z hzQ)).ne') hPs
      ((hq.2.2.2.2.2 z hzQ).log (hm.trans_le (hbound z hzQ)).ne')
      hPt.differentiableWithinAt,
    expDivergence_log_equation hO hT hm ha hq hbound heq z ⟨hz.1,hz.2.1,hz.2.2.le⟩]
  simp only [linearOp,Matrix.smul_apply,smul_eq_mul]
  have hA : (∑ i, ∑ j, (q z)⁻¹*a z i j*spatialDD P z (Yau.realVec i) (Yau.realVec j)) =
      ∑ i, ∑ j, (a z i j/q z)*spatialDD P z (Yau.realVec i) (Yau.realVec j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hA]
  ring

end Yau.LeafProofs.L16ExpBoundaryAux

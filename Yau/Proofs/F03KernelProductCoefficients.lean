import Yau.Proofs.F03KernelProductMatrix

/-! Smooth uniformly elliptic coefficients in the actual packed product chart. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem kernelProductMatrix_contraction {n : ℕ} (A B : Mat n) (H : RIdx (n+n) → RIdx (n+n) → ℝ) :
    (∑ i,∑ j,kernelProductMatrix A B i j*H i j)=
      (1/2 : ℝ)*((∑ i,∑ j,A i j*H (kernelRealIndexLeft n i) (kernelRealIndexLeft n j))+
        (∑ i,∑ j,B i j*H (kernelRealIndexRight n i) (kernelRealIndexRight n j))) := by
  simp_rw [sum_kernel_real_index n]
  simp only [kernelProductMatrix_left_left,kernelProductMatrix_left_right,
    kernelProductMatrix_right_left,kernelProductMatrix_right_right,zero_mul,
    Finset.sum_const_zero,add_zero,zero_add]
  rw [mul_add]
  congr 1 <;> simp only [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

def kernelProductSpace {n : ℕ} (Ox Oy : Set (Space n)) : Set (Space (n+n)) :=
  kernelPairPack n '' (Ox ×ˢ Oy)

def kernelProductCoeff {n : ℕ} (a b : Point n → Mat n) (p : Point (n+n)) : Mat (n+n) :=
  kernelProductMatrix (a (((kernelPairPack n).symm p.1).1,p.2))
    (b (((kernelPairPack n).symm p.1).2,p.2))

theorem kernelProductSpace_open {n : ℕ} {Ox Oy : Set (Space n)} (hx : IsOpen Ox) (hy : IsOpen Oy) :
    IsOpen (kernelProductSpace Ox Oy) := (kernelPairPack n).toHomeomorph.isOpenMap _ (hx.prod hy)

theorem kernelProductSpace_mem_iff {n : ℕ} {Ox Oy : Set (Space n)} {z : Space (n+n)} :
    z ∈ kernelProductSpace Ox Oy ↔ ((kernelPairPack n).symm z).1 ∈ Ox ∧
      ((kernelPairPack n).symm z).2 ∈ Oy := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      (show p.1 ∈ Ox ∧ p.2 ∈ Oy from ⟨hp.1,hp.2⟩)
  · intro hz
    exact ⟨(kernelPairPack n).symm z,hz,(kernelPairPack n).apply_symm_apply z⟩

theorem kernelProductCoeff_elliptic {n : ℕ} (Ox Oy : Set (Space n)) (I : Set ℝ)
    (a b : Point n → Mat n) (la ua lb ub : ℝ)
    (ha : Elliptic (Ox ×ˢ I) a la ua) (hb : Elliptic (Oy ×ˢ I) b lb ub) :
    Elliptic (kernelProductSpace Ox Oy ×ˢ I) (kernelProductCoeff a b) (min la lb/2) (max ua ub/2) := by
  refine ⟨div_pos (lt_min ha.1 hb.1) (by norm_num),?_,?_⟩
  · exact div_le_div_of_nonneg_right ((min_le_left la lb).trans (ha.2.1.trans (le_max_left ua ub))) (by norm_num)
  intro p hp
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  have hA := ha.2.2 (((kernelPairPack n).symm p.1).1,p.2) ⟨hxy.1,hp.2⟩
  have hB := hb.2.2 (((kernelPairPack n).symm p.1).2,p.2) ⟨hxy.2,hp.2⟩
  exact ⟨kernelProductMatrix_symm _ _ hA.1 hB.1,
    kernelProductMatrix_quadratic_bounds _ _ la ua lb ub hA.2 hB.2⟩

theorem kernelProductCoeff_smooth {n : ℕ} (Ox Oy : Set (Space n)) (I : Set ℝ)
    (a b : Point n → Mat n)
    (ha : SmoothCoefficients (Ox ×ˢ I) a (fun _ _ => 0))
    (hb : SmoothCoefficients (Oy ×ˢ I) b (fun _ _ => 0)) :
    SmoothCoefficients (kernelProductSpace Ox Oy ×ˢ I) (kernelProductCoeff a b) (fun _ _ => 0) := by
  refine ⟨?_,fun _ => contDiffOn_const⟩
  let Lx : Point (n+n) →L[ℝ] Point n :=
    (((ContinuousLinearMap.fst ℝ (Space n) (Space n)).comp (kernelPairPack n).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.fst ℝ (Space (n+n)) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Space (n+n)) ℝ)
  let Ly : Point (n+n) →L[ℝ] Point n :=
    (((ContinuousLinearMap.snd ℝ (Space n) (Space n)).comp (kernelPairPack n).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.fst ℝ (Space (n+n)) ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Space (n+n)) ℝ)
  have hAx : ContDiffOn ℝ ∞ (fun p => a (Lx p)) (kernelProductSpace Ox Oy ×ˢ I) :=
    ha.1.comp Lx.contDiff.contDiffOn (fun p hp => ⟨(kernelProductSpace_mem_iff.mp hp.1).1,hp.2⟩)
  have hBy : ContDiffOn ℝ ∞ (fun p => b (Ly p)) (kernelProductSpace Ox Oy ×ˢ I) :=
    hb.1.comp Ly.contDiff.contDiffOn (fun p hp => ⟨(kernelProductSpace_mem_iff.mp hp.1).2,hp.2⟩)
  have hEntry (i j : RIdx (n+n)) : ContDiffOn ℝ ∞
      (fun p => kernelProductCoeff a b p i j) (kernelProductSpace Ox Oy ×ˢ I) := by
    unfold kernelProductCoeff kernelProductMatrix
    rcases hi : (kernelRealIndexSumEquiv n).symm i with i|i <;>
      rcases hj : (kernelRealIndexSumEquiv n).symm j with j|j
    · exact contDiffOn_const.mul ((matrixEntryCLM i j).contDiff.comp_contDiffOn hAx)
    · exact contDiffOn_const
    · exact contDiffOn_const
    · exact contDiffOn_const.mul ((matrixEntryCLM i j).contDiff.comp_contDiffOn hBy)
  have hs := ContDiffOn.sum (s := Finset.univ) (fun i _ =>
    ContDiffOn.sum (s := Finset.univ) (fun j _ =>
      (hEntry i j).smul (contDiffOn_const (c := (Matrix.single i j (1 : ℝ) : Mat (n+n))))))
  convert hs using 1
  funext p
  ext i j
  simp only [Matrix.sum_apply]
  change kernelProductCoeff a b p i j=
    ∑ x,∑ y,kernelProductCoeff a b p x y*Matrix.single x y (1 : ℝ) i j
  simp only [Matrix.single_apply,ite_and]
  simp

end Yau.Proofs.F03Aux

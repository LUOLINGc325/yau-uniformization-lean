import Yau.Proofs.F03KernelProductHessian
import Yau.Proofs.F03KernelProductCoefficients

/-! The packed operator is exactly one half of each actual spatial heat operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem kernelProduct_left_linearOp {n : ℕ} (Ox Oy : Set (Space n)) (I : Set ℝ)
    (hx : IsOpen Ox) (hy : IsOpen Oy) (hI : IsOpen I)
    (a : Point n → Mat n) (f : ((Space n × Space n) × ℝ) → ℝ) (p : Point (n+n))
    (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I)
    (hf : ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)) :
    linearOp (Ox ×ˢ I) a (fun _ _ => 0)
        (fun q : Point n => f ((q.1,((kernelPairPack n).symm p.1).2),q.2))
        (((kernelPairPack n).symm p.1).1,p.2)=
      timeD (kernelProductSpace Ox Oy ×ˢ I) (fun q => f ((kernelPairTimePack n).symm q)) p-
        (∑ i,∑ j,a (((kernelPairPack n).symm p.1).1,p.2) i j*
          spatialDD (fun q => f ((kernelPairTimePack n).symm q)) p
            (realVec (kernelRealIndexLeft n i)) (realVec (kernelRealIndexLeft n j))) := by
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen (hx.prod hI) ⟨hxy.1,hp.2⟩,
    timeD_eq_deriv_of_isOpen ((kernelProductSpace_open hx hy).prod hI) hp]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  simp_rw [kernelProductHessian_left f p hf]
  rfl

theorem kernelProduct_right_linearOp {n : ℕ} (Ox Oy : Set (Space n)) (I : Set ℝ)
    (hx : IsOpen Ox) (hy : IsOpen Oy) (hI : IsOpen I)
    (b : Point n → Mat n) (f : ((Space n × Space n) × ℝ) → ℝ) (p : Point (n+n))
    (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I)
    (hf : ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)) :
    linearOp (Oy ×ˢ I) b (fun _ _ => 0)
        (fun q : Point n => f ((((kernelPairPack n).symm p.1).1,q.1),q.2))
        (((kernelPairPack n).symm p.1).2,p.2)=
      timeD (kernelProductSpace Ox Oy ×ˢ I) (fun q => f ((kernelPairTimePack n).symm q)) p-
        (∑ i,∑ j,b (((kernelPairPack n).symm p.1).2,p.2) i j*
          spatialDD (fun q => f ((kernelPairTimePack n).symm q)) p
            (realVec (kernelRealIndexRight n i)) (realVec (kernelRealIndexRight n j))) := by
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen (hy.prod hI) ⟨hxy.2,hp.2⟩,
    timeD_eq_deriv_of_isOpen ((kernelProductSpace_open hx hy).prod hI) hp]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  simp_rw [kernelProductHessian_right f p hf]
  rfl

theorem kernelProduct_linearOp {n : ℕ} (Ox Oy : Set (Space n)) (I : Set ℝ)
    (hx : IsOpen Ox) (hy : IsOpen Oy) (hI : IsOpen I)
    (a b : Point n → Mat n) (f : ((Space n × Space n) × ℝ) → ℝ) (p : Point (n+n))
    (hp : p ∈ kernelProductSpace Ox Oy ×ˢ I)
    (hf : ContDiffAt ℝ 2 f ((kernelPairTimePack n).symm p)) :
    linearOp (kernelProductSpace Ox Oy ×ˢ I) (kernelProductCoeff a b) (fun _ _ => 0)
        (fun q => f ((kernelPairTimePack n).symm q)) p=
      (1/2 : ℝ)*(linearOp (Ox ×ˢ I) a (fun _ _ => 0)
          (fun q : Point n => f ((q.1,((kernelPairPack n).symm p.1).2),q.2))
          (((kernelPairPack n).symm p.1).1,p.2)+
        linearOp (Oy ×ˢ I) b (fun _ _ => 0)
          (fun q : Point n => f ((((kernelPairPack n).symm p.1).1,q.1),q.2))
          (((kernelPairPack n).symm p.1).2,p.2)) := by
  have hxy := kernelProductSpace_mem_iff.mp hp.1
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen ((kernelProductSpace_open hx hy).prod hI) hp,
    timeD_eq_deriv_of_isOpen (hx.prod hI) ⟨hxy.1,hp.2⟩,
    timeD_eq_deriv_of_isOpen (hy.prod hI) ⟨hxy.2,hp.2⟩]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  change deriv (fun t => f (((kernelPairPack n).symm p.1),t)) p.2-
    (∑ i,∑ j,kernelProductMatrix (a (((kernelPairPack n).symm p.1).1,p.2))
      (b (((kernelPairPack n).symm p.1).2,p.2)) i j*
      spatialDD (fun q => f ((kernelPairTimePack n).symm q)) p (realVec i) (realVec j))=_
  rw [kernelProductMatrix_contraction]
  simp_rw [kernelProductHessian_left f p hf,kernelProductHessian_right f p hf]
  ring

end Yau.Proofs.F03Aux

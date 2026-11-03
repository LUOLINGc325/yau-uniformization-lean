import Yau.Proofs.F03KernelProductCoordinates

/-! The actual left/right partition of all real directions in product coordinates. -/
noncomputable section
open MeasureTheory Filter Set
namespace Yau.Proofs.F03Aux
open Yau Parabolic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

def kernelRealIndexSumEquiv (n : ℕ) : (RIdx n ⊕ RIdx n) ≃ RIdx (n+n) :=
  (Equiv.sumProdDistrib (Fin n) (Fin n) (Fin 2)).symm.trans
    ((finSumFinEquiv : (Fin n ⊕ Fin n) ≃ Fin (n+n)).prodCongr (Equiv.refl (Fin 2)))

theorem kernelRealIndexSumEquiv_inl (n : ℕ) (i : RIdx n) :
    kernelRealIndexSumEquiv n (Sum.inl i)=kernelRealIndexLeft n i := by
  rcases i with ⟨i,k⟩
  rfl

theorem kernelRealIndexSumEquiv_inr (n : ℕ) (i : RIdx n) :
    kernelRealIndexSumEquiv n (Sum.inr i)=kernelRealIndexRight n i := by
  rcases i with ⟨i,k⟩
  rfl

theorem sum_kernel_real_index (n : ℕ) (f : RIdx (n+n) → ℝ) :
    (∑ i,f i)=(∑ i,f (kernelRealIndexLeft n i))+(∑ i,f (kernelRealIndexRight n i)) := by
  rw [← (kernelRealIndexSumEquiv n).sum_comp f]
  simp only [Fintype.sum_sum_type,kernelRealIndexSumEquiv_inl,kernelRealIndexSumEquiv_inr]

theorem kernelRealIndexSumEquiv_symm_left (n : ℕ) (i : RIdx n) :
    (kernelRealIndexSumEquiv n).symm (kernelRealIndexLeft n i)=Sum.inl i := by
  rw [← kernelRealIndexSumEquiv_inl]
  exact (kernelRealIndexSumEquiv n).symm_apply_apply (Sum.inl i)

theorem kernelRealIndexSumEquiv_symm_right (n : ℕ) (i : RIdx n) :
    (kernelRealIndexSumEquiv n).symm (kernelRealIndexRight n i)=Sum.inr i := by
  rw [← kernelRealIndexSumEquiv_inr]
  exact (kernelRealIndexSumEquiv n).symm_apply_apply (Sum.inr i)

end Yau.Proofs.F03Aux

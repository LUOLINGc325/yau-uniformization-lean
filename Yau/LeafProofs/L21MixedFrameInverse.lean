import Yau.LeafProofs.L21MatrixBounds
import Mathlib.Analysis.Normed.Operator.Prod

open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.LeafProofs.L21Aux

abbrev MixedFrameVector (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)

/-- A single actual off-diagonal entry of the mixed coefficient frame. -/
def mixedFrameSlot0 {n : ℕ} (i k : Fin n) : MixedFrameVector n →L[ℝ] MixedFrameVector n :=
  ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).comp
    ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Fin n → ℂ) (Fin n → ℂ)))).prod 0

def mixedFrameSlot1 {n : ℕ} (i k : Fin n) : MixedFrameVector n →L[ℝ] MixedFrameVector n :=
  (0 : MixedFrameVector n →L[ℝ] (Fin n → ℂ)).prod
    ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).comp
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin n → ℂ) (Fin n → ℂ))))

theorem mixedFrameSlot0_norm {n : ℕ} (i k : Fin n) : ‖mixedFrameSlot0 i k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  change max ‖(ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k) (w.2 i)‖ ‖(0 : Fin n → ℂ)‖ ≤ 1*‖w‖
  simp only [norm_zero,max_eq_left (norm_nonneg _),one_mul]
  exact ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_single_le_one ℝ (fun _ : Fin n => ℂ) k)
      (norm_nonneg _)).trans ((by simpa only [one_mul] using
        (norm_le_pi_norm w.2 i).trans (show ‖w.2‖ ≤ ‖w‖ from le_max_right _ _))))

theorem mixedFrameSlot1_norm {n : ℕ} (i k : Fin n) : ‖mixedFrameSlot1 i k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  change max ‖(0 : Fin n → ℂ)‖ ‖(ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k) (w.1 i)‖ ≤ 1*‖w‖
  simp only [norm_zero,max_eq_right (norm_nonneg _),one_mul]
  exact ((ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) k).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_single_le_one ℝ (fun _ : Fin n => ℂ) k)
      (norm_nonneg _)).trans ((by simpa only [one_mul] using
        (norm_le_pi_norm w.1 i).trans (show ‖w.1‖ ≤ ‖w‖ from le_max_left _ _))))

def mixedFramePerturbation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MixedFrameVector n →L[ℝ] MixedFrameVector n :=
  ∑ i, ∑ k, (star (A i k) • mixedFrameSlot0 i k + A i k • mixedFrameSlot1 i k)

def mixedFrameOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    MixedFrameVector n →L[ℝ] MixedFrameVector n :=
  ContinuousLinearMap.id ℝ _ + mixedFramePerturbation A

/-- Anti-holomorphic and holomorphic coefficient blocks of the actual frame. -/
theorem mixedFrameOperator_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : MixedFrameVector n) :
    mixedFrameOperator A w =
      (fun k => w.1 k+∑ i, w.2 i*star (A i k), fun k => w.2 k+∑ i, w.1 i*A i k) := by
  classical
  ext k <;>
    simp [mixedFrameOperator,mixedFramePerturbation,mixedFrameSlot0,mixedFrameSlot1,
      sum_apply,Finset.sum_add_distrib,
      Pi.single_apply,mul_ite,ite_mul,mul_comm,Prod.fst_sum,Prod.snd_sum]

theorem mixedFramePerturbation_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖mixedFramePerturbation A‖ ≤ 2*(∑ i, ∑ k, ‖A i k‖) := by
  calc
    _ ≤ ∑ i, ‖∑ k, (star (A i k) • mixedFrameSlot0 i k+A i k • mixedFrameSlot1 i k)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ k, (‖star (A i k) • mixedFrameSlot0 i k‖+‖A i k • mixedFrameSlot1 i k‖) := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_add_le _ _))
    _ ≤ ∑ i, ∑ k, (‖A i k‖+‖A i k‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_smul,norm_star]
      exact add_le_add
        ((mul_le_mul_of_nonneg_left (mixedFrameSlot0_norm i k) (norm_nonneg _)).trans_eq (mul_one _))
        ((mul_le_mul_of_nonneg_left (mixedFrameSlot1_norm i k) (norm_nonneg _)).trans_eq (mul_one _))
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

def mixedFrameEpsilon (n : ℕ) : ℝ := 1/(4*((n : ℝ)^2+1))

theorem mixedFrameEpsilon_pos (n : ℕ) : 0 < mixedFrameEpsilon n := by unfold mixedFrameEpsilon; positivity

theorem mixedFramePerturbation_small {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i k, ‖A i k‖ ≤ mixedFrameEpsilon n) : ‖mixedFramePerturbation A‖ ≤ 1/2 := by
  have hSum : (∑ i, ∑ k, ‖A i k‖) ≤ (n : ℝ)^2*mixedFrameEpsilon n := by
    calc
      _ ≤ ∑ _i : Fin n, ∑ _k : Fin n, mixedFrameEpsilon n := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hA i k))
      _ = _ := by simp; ring
  calc
    _ ≤ 2*(∑ i, ∑ k, ‖A i k‖) := mixedFramePerturbation_norm A
    _ ≤ 2*((n : ℝ)^2*mixedFrameEpsilon n) := mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ ≤ 1/2 := by
      dsimp only [mixedFrameEpsilon]
      calc
        _ = (2*(n : ℝ)^2)/(4*((n : ℝ)^2+1)) := by ring
        _ ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 4*((n : ℝ)^2+1))).mpr (by nlinarith only [sq_nonneg (n : ℝ)])

/-- The real paired coefficient frame has a genuine uniform lower bound. -/
theorem mixedFrameOperator_lower {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i k, ‖A i k‖ ≤ mixedFrameEpsilon n) (w : MixedFrameVector n) :
    ‖w‖ ≤ 2*‖mixedFrameOperator A w‖ := by
  have h := (norm_sub_le (mixedFrameOperator A w) (mixedFramePerturbation A w))
  have hEval : mixedFrameOperator A w-mixedFramePerturbation A w = w := by
    simp only [mixedFrameOperator,add_apply,ContinuousLinearMap.id_apply,add_sub_cancel_right]
  rw [hEval] at h
  have hT : ‖mixedFramePerturbation A w‖ ≤ (1/2:ℝ)*‖w‖ :=
    ((mixedFramePerturbation A).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (mixedFramePerturbation_small hA) (norm_nonneg _))
  linarith only [h,hT]

theorem mixedFrameOperator_invertible {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i k, ‖A i k‖ ≤ mixedFrameEpsilon n) : (mixedFrameOperator A).IsInvertible := by
  have hinj : Function.Injective (mixedFrameOperator A) := by
    intro u v huv
    have hZero : mixedFrameOperator A (u-v) = 0 := by rw [map_sub,huv,sub_self]
    have h := mixedFrameOperator_lower hA (u-v)
    rw [hZero,norm_zero,mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let e := (LinearEquiv.ofInjectiveEndo (mixedFrameOperator A).toLinearMap hinj).toContinuousLinearEquiv
  exact ⟨e,by apply ContinuousLinearMap.ext; intro w; rfl⟩

theorem mixedFrameOperator_inverse_norm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i k, ‖A i k‖ ≤ mixedFrameEpsilon n) : ‖(mixedFrameOperator A).inverse‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  have h := mixedFrameOperator_lower hA ((mixedFrameOperator A).inverse w)
  rwa [(mixedFrameOperator_invertible hA).self_apply_inverse] at h

theorem mixedFrameOperator_smooth {n : ℕ} {O : Set (X n)}
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O) :
    ContDiffOn ℝ ∞ (fun x => mixedFrameOperator (A x)) O := by
  apply contDiffOn_const.add
  change ContDiffOn ℝ ∞ (fun x => ∑ i, ∑ k, (star (A x i k) • mixedFrameSlot0 i k+A x i k • mixedFrameSlot1 i k)) O
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro k _
  exact (((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn (hA i k)).smul contDiffOn_const).add ((hA i k).smul contDiffOn_const)

theorem mixedFrameOperator_inverse_smooth {n : ℕ} {O : Set (X n)} (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hSmall : JetBound 0 (mixedFrameEpsilon n) A O) :
    ContDiffOn ℝ ∞ (fun x => (mixedFrameOperator (A x)).inverse) O := by
  intro x hx
  have hEntry (i k : Fin n) : ‖A x i k‖ ≤ mixedFrameEpsilon n := by
    simpa only [norm_iteratedFDeriv_zero] using hSmall 0 le_rfl x hx i k
  exact ((mixedFrameOperator_invertible hEntry).contDiffAt_map_inverse.comp x
    ((mixedFrameOperator_smooth hA).contDiffAt (hO.mem_nhds hx))).contDiffWithinAt

end Yau.LeafProofs.L21Aux

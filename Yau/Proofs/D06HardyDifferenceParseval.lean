import Yau.Proofs.D06BoundaryDifferences

/-! Translation difference energy equals the exact Hardy coefficient norm
for the original circle traces, supplying the finite-Fourier W¹ argument. -/

open scoped lp
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyTrace_difference_rotation_ae (a : HardySeq r) (i : Fin r) (θ : HardyCircle) :
    (fun t => hardyTraceLp (hardyDilate (fourier 1 θ)
      (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a - a) i t) =ᵐ[hardyCircleMeasure]
      fun t => hardyTraceLp a i (t + θ) - hardyTraceLp a i t := by
  let R : HardySeq r := hardyDilate (fourier 1 θ)
    (by simp only [fourier_apply, Circle.norm_coe, le_refl]) a
  have hs : hardyTraceLp (R - a) i = hardyTraceLp R i - hardyTraceLp a i :=
    map_sub (hardyTraceLpCLM i) R a
  have h := Lp.coeFn_sub (hardyTraceLp R i) (hardyTraceLp a i)
  rw [← hs] at h
  filter_upwards [h, hardyTrace_rotation_ae a i θ] with t ht hr
  exact ht.trans (by rw [Pi.sub_apply, hr])

theorem hardyMatrixTrace_difference_parseval (a : Fin r → HardySeq r) (θ : HardyCircle) :
    circleDifference (hardyMatrixTrace a) θ =
      ∑ j : Fin r, ‖hardyDilate (fourier 1 θ)
        (by simp only [fourier_apply, Circle.norm_coe, le_refl]) (a j) - a j‖ ^ 2 := by
  let R : HardySeq r → HardySeq r := hardyDilate (fourier 1 θ)
    (by simp only [fourier_apply, Circle.norm_coe, le_refl])
  have hentry (i j : Fin r) : Integrable
      (fun t => ‖hardyTraceLp (a j) i (t + θ) - hardyTraceLp (a j) i t‖ ^ 2)
      hardyCircleMeasure := by
    have hr := hardyTrace_difference_rotation_ae (a j) i θ
    exact ((Lp.memLp (hardyTraceLp (R (a j) - a j) i)).integrable_norm_pow
      (by decide : 2 ≠ 0)).congr (hr.mono fun t ht => congrArg (fun c : ℂ => ‖c‖ ^ 2) ht)
  unfold circleDifference
  change (∫ t, ∑ i : Fin r, ∑ j : Fin r,
    ‖hardyTraceLp (a j) i (t + θ) - hardyTraceLp (a j) i t‖ ^ 2 ∂hardyCircleMeasure) = _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hentry i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hentry _ j)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hardyTrace_norm_sq (R (a j) - a j)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hardyTrace_difference_rotation_ae (a j) i θ] with t ht
  exact congrArg (fun c : ℂ => ‖c‖ ^ 2) ht.symm

end Yau.NodeProofs.D06Aux

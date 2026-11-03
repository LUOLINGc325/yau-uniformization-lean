import Yau.Proofs.C02DirectionalWords

/-! The finite directional estimates give the literal operator norm of
each actual Fréchet derivative, including dimension zero and order zero. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem directionalWord_ofFn_eq (b : ι → E) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (a : Fin m → ι) (x : E) :
    directionalWord b f (List.ofFn a) x = iteratedFDeriv ℝ m f x (fun j => b (a j)) := by
  induction m generalizing x with
  | zero => simp only [List.ofFn_zero, directionalWord, iteratedFDeriv_zero_apply]
  | succ m ih =>
    rw [List.ofFn_succ, directionalWord]
    have hFun : directionalWord b f (List.ofFn (fun j => a j.succ)) =
        fun y => iteratedFDeriv ℝ m f y (fun j => b (a j.succ)) :=
      funext (fun y => ih (fun j => a j.succ) y)
    rw [hFun]
    have hJet : DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x :=
      (hf.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
    exact (hJet.iteratedFDeriv_succ_apply_left' (m := fun j => b (a j))).symm

theorem norm_iteratedFDeriv_le_directional_bound
    (b : OrthonormalBasis ι ℝ E) (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (x : E) (B : ℝ) (hB : 0 ≤ B)
    (hWords : ∀ w : List ι, w.length = m → ‖directionalWord b f w x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ (Fintype.card ι : ℝ) ^ m * B := by
  apply norm_multilinear_le_card_pow_basis_bound b m _ B hB
  intro a
  rw [← directionalWord_ofFn_eq (b : ι → E) f hf m a x]
  exact hWords (List.ofFn a) (by simp)

end Yau.Blueprint.C02Proof

import Yau.Proofs.D06HardyRadialTrace
import Yau.Proofs.D06FiniteLpLimit

/-! Common radial subsequences for the actual Hardy matrix boundary traces. -/

open scoped Topology
open Filter MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyRadius (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + 1)

theorem hardyRadius_nonneg (n : ℕ) : 0 ≤ hardyRadius n := by
  unfold hardyRadius
  positivity

theorem hardyRadius_lt_one (n : ℕ) : hardyRadius n < 1 := by
  unfold hardyRadius
  apply (div_lt_one (by positivity : 0 < (n : ℝ) + 1)).mpr
  linarith

theorem hardyRadius_norm (n : ℕ) : ‖(hardyRadius n : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hardyRadius_nonneg n)]
  exact hardyRadius_lt_one n

theorem hardyRadius_tendsto : Tendsto (fun n => (hardyRadius n : ℂ)) atTop (𝓝 1) := by
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_natCast_div_add_atTop (𝕜 := ℝ) 1)
  exact h

def hardyMatrixInterior (a : Fin r → HardySeq r) (z : ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => hardyEvalEntry (a j) i z

def hardyMatrixTrace (a : Fin r → HardySeq r) (t : HardyCircle) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => hardyTraceLp (a j) i t

theorem hardyMatrix_radial_subsequence {κ : Type*} [Fintype κ]
    (a : κ → Fin r → HardySeq r) : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ t ∂hardyCircleMeasure,
      ∀ k, Tendsto (fun n => hardyMatrixInterior (a k)
          ((hardyRadius (ns n) : ℂ) * fourier 1 t)) atTop (𝓝 (hardyMatrixTrace (a k) t)) := by
  let f : ℕ → κ × Fin r × Fin r → Lp ℂ 2 hardyCircleMeasure := fun n q =>
    hardyTraceLp (hardyDilate (hardyRadius n : ℂ) (hardyRadius_norm n).le (a q.1 q.2.2)) q.2.1
  let g : κ × Fin r × Fin r → Lp ℂ 2 hardyCircleMeasure := fun q => hardyTraceLp (a q.1 q.2.2) q.2.1
  have hlim (q : κ × Fin r × Fin r) : Tendsto (fun n => f n q) atTop (𝓝 (g q)) :=
    hardyTraceLp_radial_tendsto _ (fun n => (hardyRadius_norm n).le) hardyRadius_tendsto _ _
  obtain ⟨ns, hns, hnlim⟩ := finiteLp_ae_subsequence hardyCircleMeasure f g hlim
  have heq (n : ℕ) (q : κ × Fin r × Fin r) : (fun t => f n q t) =ᵐ[hardyCircleMeasure]
      fun t => hardyMatrixInterior (a q.1) ((hardyRadius n : ℂ) * fourier 1 t) q.2.1 q.2.2 :=
    hardyTraceLp_radial_ae _ (hardyRadius_norm n) _ _
  have hall : ∀ᵐ t ∂hardyCircleMeasure, ∀ n q, f n q t =
      hardyMatrixInterior (a q.1) ((hardyRadius n : ℂ) * fourier 1 t) q.2.1 q.2.2 :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (heq n))
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hnlim, hall] with t ht he
  intro k
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := ht (k, i, j)
  exact h.congr' (Eventually.of_forall fun n => he (ns n) (k, i, j))

end Yau.NodeProofs.D06Aux

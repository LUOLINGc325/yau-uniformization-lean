import Yau.Proofs.D06CircleProductCoefficients

/-! The canonical boundary sum of each original Hardy power series equals
its fixed Fourier trace almost everywhere once the first Sobolev order holds. -/

open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

theorem hardyEvalEntry_circle_eq_representative (a : HardySeq r) (i : Fin r)
    (h1 : CircleSobolev 1 (hardyTraceLp a i)) (t : HardyCircle) :
    hardyEvalEntry a i (fourier 1 t) = circleFourierRepresentative (hardyTraceLp a i) t := by
  let F : ℤ → ℂ := fun n => circleCoeff (hardyTraceLp a i) n * fourier n t
  have hsum : HasSum F (circleFourierRepresentative (hardyTraceLp a i) t) :=
    circleFourierRepresentative_hasSum h1 t
  have hp : Summable (fun n : ℕ => F (n : ℤ)) := hsum.summable.comp_injective Int.ofNat_injective
  have hneg : (fun n : ℕ => F (-(n + 1) : ℤ)) = fun _ : ℕ => (0 : ℂ) := by
    funext n
    change circleCoeff (hardyTraceLp a i) (-(n + 1) : ℤ) * fourier (-(n + 1)) t = 0
    rw [circleCoeff_eq_fourierCoeff, hardyTrace_fourierCoeff, ite_eq_right (by omega), zero_mul]
  have hm : Summable (fun n : ℕ => F (-(n + 1) : ℤ)) := by rw [hneg]; exact summable_zero
  have hs := tsum_of_nat_of_neg_add_one (f := F) hp hm
  have hnat : (∑' n : ℤ, F n) = ∑' n : ℕ, F (n : ℤ) := by
    simpa only [hneg, tsum_zero, add_zero] using hs
  symm
  calc
    _ = ∑' n : ℤ, F n := hsum.tsum_eq.symm
    _ = ∑' n : ℕ, F (n : ℤ) := hnat
    _ = hardyEvalEntry a i (fourier 1 t) := by
      rw [hardyEvalEntry_eq_tsum]
      apply tsum_congr
      intro n
      change circleCoeff (hardyTraceLp a i) (n : ℤ) * fourier (n : ℤ) t = _
      rw [circleCoeff_eq_fourierCoeff, hardyTrace_fourierCoeff,
        ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast, hardy_fourier_nat]
      ring

theorem hardyEvalEntry_circle_ae (a : HardySeq r) (i : Fin r)
    (h1 : CircleSobolev 1 (hardyTraceLp a i)) :
    (fun t => hardyEvalEntry a i (fourier 1 t)) =ᵐ[hardyCircleMeasure] hardyTraceLp a i := by
  filter_upwards [circleFourierRepresentative_ae h1] with t ht
  rw [hardyEvalEntry_circle_eq_representative a i h1]
  exact ht

theorem hardyMatrixInterior_circle_ae (a : Fin r → HardySeq r)
    (h1 : ∀ i j, CircleSobolev 1 (hardyTraceLp (a j) i)) :
    (fun t => hardyMatrixInterior a (fourier 1 t)) =ᵐ[hardyCircleMeasure] hardyMatrixTrace a := by
  have hall : ∀ᵐ t ∂hardyCircleMeasure, ∀ i j,
      hardyEvalEntry (a j) i (fourier 1 t) = hardyTraceLp (a j) i t :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hardyEvalEntry_circle_ae (a j) i (h1 i j)))
  filter_upwards [hall] with t ht
  ext i j
  exact ht i j

end Yau.NodeProofs.D06Aux

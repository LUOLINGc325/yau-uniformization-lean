import Yau.Proofs.V04DiscMatrixMaximum

/-! Any two given closed-disc factors of the same boundary matrix differ
by a constant unitary left factor. In particular the caller's inverse is
transported explicitly, rather than replaced by an existential witness. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem closedDisc_factor_unitary_unique
    (H Hinv K Kinv : ℂ → CotangentMatrix n)
    (hH : ∀ i j, ContDiffOn ℂ ∞ (fun z => H z i j) (Metric.closedBall (0 : ℂ) 1) ∧
      ContDiffOn ℂ ∞ (fun z => Hinv z i j) (Metric.closedBall (0 : ℂ) 1))
    (hK : ∀ i j, ContDiffOn ℂ ∞ (fun z => K z i j) (Metric.closedBall (0 : ℂ) 1) ∧
      ContDiffOn ℂ ∞ (fun z => Kinv z i j) (Metric.closedBall (0 : ℂ) 1))
    (hHi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, H z * Hinv z = 1 ∧ Hinv z * H z = 1)
    (hKi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, K z * Kinv z = 1 ∧ Kinv z * K z = 1)
    (hboundary : ∀ θ, (H (circlePoint θ))ᴴ * H (circlePoint θ) =
      (K (circlePoint θ))ᴴ * K (circlePoint θ)) :
    ∃ U : CotangentMatrix n, Uᴴ * U = 1 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H z = U * K z ∧ Hinv z = Kinv z * Uᴴ := by
  let Q : ℂ → CotangentMatrix n := fun z => H z * Kinv z
  let R : ℂ → CotangentMatrix n := fun z => K z * Hinv z
  have hQ : ∀ i j, ContDiffOn ℂ ∞ (fun z => Q z i j) (Metric.closedBall (0 : ℂ) 1) := by
    intro i j
    change ContDiffOn ℂ ∞ (fun z => ∑ k, H z i k * Kinv z k j) (Metric.closedBall (0 : ℂ) 1)
    exact ContDiffOn.sum fun k _ => (hH i k).1.mul (hK k j).2
  have hR : ∀ i j, ContDiffOn ℂ ∞ (fun z => R z i j) (Metric.closedBall (0 : ℂ) 1) := by
    intro i j
    change ContDiffOn ℂ ∞ (fun z => ∑ k, K z i k * Hinv z k j) (Metric.closedBall (0 : ℂ) 1)
    exact ContDiffOn.sum fun k _ => (hK i k).1.mul (hH k j).2
  have hRQ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, R z * Q z = 1 := by
    intro z hz
    calc
      R z * Q z = K z * (Hinv z * H z) * Kinv z := by dsimp [R, Q]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hHi z hz).2, Matrix.mul_one, (hKi z hz).1]
  have hcircle (θ : ℝ) : circlePoint θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, circlePoint, Complex.norm_exp]
  have hQboundary : ∀ θ, (Q (circlePoint θ))ᴴ * Q (circlePoint θ) = 1 := by
    intro θ
    let z := circlePoint θ
    calc
      (Q z)ᴴ * Q z = (Kinv z)ᴴ * ((H z)ᴴ * H z) * Kinv z := by
        dsimp [Q]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Kinv z)ᴴ * ((K z)ᴴ * K z) * Kinv z := by rw [hboundary θ]
      _ = (K z * Kinv z)ᴴ * (K z * Kinv z) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [(hKi z (hcircle θ)).1]; simp
  have hRboundary : ∀ θ, (R (circlePoint θ))ᴴ * R (circlePoint θ) = 1 := by
    intro θ
    let z := circlePoint θ
    calc
      (R z)ᴴ * R z = (Hinv z)ᴴ * ((K z)ᴴ * K z) * Hinv z := by
        dsimp [R]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Hinv z)ᴴ * ((H z)ᴴ * H z) * Hinv z := by rw [← hboundary θ]
      _ = (H z * Hinv z)ᴴ * (H z * Hinv z) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [(hHi z (hcircle θ)).1]; simp
  obtain ⟨hU, hconst⟩ := closedDisc_matrix_inverse_unitary_constant Q R hQ hR hRQ
    hQboundary hRboundary
  refine ⟨Q 0, hU, fun z hz => ?_⟩
  have hHfactor : H z = Q 0 * K z := by
    calc
      H z = H z * (Kinv z * K z) := by rw [(hKi z hz).2, Matrix.mul_one]
      _ = Q z * K z := by dsimp [Q]; simp only [Matrix.mul_assoc]
      _ = Q 0 * K z := by rw [hconst z hz]
  refine ⟨hHfactor, ?_⟩
  have hleft : (Kinv z * (Q 0)ᴴ) * H z = 1 := by
    rw [hHfactor]
    calc
      _ = Kinv z * ((Q 0)ᴴ * Q 0) * K z := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, (hKi z hz).2]
  calc
    Hinv z = 1 * Hinv z := (Matrix.one_mul _).symm
    _ = ((Kinv z * (Q 0)ᴴ) * H z) * Hinv z := by rw [hleft]
    _ = Kinv z * (Q 0)ᴴ := by rw [Matrix.mul_assoc, (hHi z hz).1, Matrix.mul_one]

theorem spectralFactorFor_unitary_unique {d : VariationData X q} {j a : ℕ} {δ : ℝ}
    {F : VariationDisc X} {E H Hinv K Kinv : ℂ → CotangentMatrix n}
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hK : SpectralFactorFor d j a δ F E K Kinv) :
    ∃ U : CotangentMatrix n, Uᴴ * U = 1 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        H z = U * K z ∧ Hinv z = Kinv z * Uᴴ :=
  closedDisc_factor_unitary_unique H Hinv K Kinv hH.1 hK.1 hH.2.1 hK.2.1
    (fun θ => (hH.2.2 θ).trans (hK.2.2 θ).symm)

theorem spectralFactorFor_gram_eq {d : VariationData X q} {j a : ℕ} {δ : ℝ}
    {F : VariationDisc X} {E H Hinv K Kinv : ℂ → CotangentMatrix n}
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hK : SpectralFactorFor d j a δ F E K Kinv)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    (H z)ᴴ * H z = (K z)ᴴ * K z := by
  obtain ⟨U, hU, h⟩ := spectralFactorFor_unitary_unique hH hK
  rw [(h z hz).1]
  calc
    _ = (K z)ᴴ * (Uᴴ * U) * K z := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

end Yau.Blueprint.V04Proof

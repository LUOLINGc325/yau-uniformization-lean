import Yau.Proofs.C04MatrixRegularity

/-! Product differentiation for the genuine inverse-metric Ricci quadratic form. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem matrix_mul_entry_hasDerivAt (A B : ℝ → Herm n) (A' B' : Herm n) {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) :
    ∀ i j, HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  intro i j
  have hh := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hA i k).mul (hB k j))
  convert hh using 1
  · funext s
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]
  · simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

theorem inverse_ricci_inverse_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    let K := (gMat (h t) x)⁻¹
    let R := ricci (h t) x
    let R' := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
    ∀ i j, HasDerivAt (fun s => ((gMat (h s) x)⁻¹ * ricci (h s) x * (gMat (h s) x)⁻¹) i j)
      ((K * R' * K + K * R * K * R * K + K * R * K * R * K) i j) t := by
  dsimp only
  let Km := fun s => (gMat (h s) x)⁻¹
  let Rm := fun s => ricci (h s) x
  let R' : Herm n := Matrix.of (fun i j => deriv (fun s => ricci (h s) x i j) t)
  have hK := gMat_inverse_hasDerivAt X o h U P ρ hf x ht
  have hR : ∀ i j, HasDerivAt (fun s => Rm s i j) (R' i j) t :=
    fun i j => (ricci_time_contDiffAt X o h U P ρ hf x ht i j).differentiableAt (by simp) |>.hasDerivAt
  have hKR := matrix_mul_entry_hasDerivAt Km Rm (Km t * Rm t * Km t) R' hK hR
  have hKRK := matrix_mul_entry_hasDerivAt (fun s => Km s * Rm s) Km
    ((Km t * Rm t * Km t) * Rm t + Km t * R') (Km t * Rm t * Km t) hKR hK
  intro i j
  have heq : ((Km t * Rm t * Km t) * Rm t + Km t * R') * Km t +
      (Km t * Rm t) * (Km t * Rm t * Km t) =
      Km t * R' * Km t + Km t * Rm t * Km t * Rm t * Km t +
        Km t * Rm t * Km t * Rm t * Km t := by noncomm_ring
  simpa only [heq] using hKRK i j

end Yau.Proofs.C04Aux

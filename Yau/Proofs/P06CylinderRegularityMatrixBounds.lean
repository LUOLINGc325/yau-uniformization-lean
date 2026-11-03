import Yau.Proofs.P06CylinderRegularityCutoffs

/-! Finite coupled lower-order terms are bounded by values alone. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

theorem matrix_row_square_bound {α : Type*} [Fintype α]
    (a v : α → ℝ) {B : ℝ} (hB : 0 ≤ B) (ha : ∀ c, |a c| ≤ B) :
    (∑ c, a c * v c)^2 ≤ (Fintype.card α : ℝ) * B^2 * ∑ c, (v c)^2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a v
  have hs : (∑ c, (a c)^2) ≤ (Fintype.card α : ℝ) * B^2 := by
    calc
      _ ≤ ∑ _c : α, B^2 := Finset.sum_le_sum (fun c _ => by
        nlinarith [ha c, abs_nonneg (a c), sq_abs (a c)])
      _ = _ := by simp
  exact hCS.trans (by gcongr)

def valueSquare {α : Type*} [Fintype α] {E : Type*} (U : E → α → ℝ) (p : E) : ℝ :=
  ∑ c, (U p c)^2

def valueFlux {n : ℕ} {α : Type*} [Fintype α]
    (d : α → α → Yau.RIdx n → Point n → ℝ) (U : Point n → α → ℝ)
    (r : α) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  ∑ c, d r c i p * U p c

def valueSource {n : ℕ} {α : Type*} [Fintype α]
    (e : α → α → Point n → ℝ) (U : Point n → α → ℝ)
    (r : α) (p : Point n) : ℝ := ∑ c, e r c p * U p c

theorem valueSquare_nonneg {α E : Type*} [Fintype α] (U : E → α → ℝ) (p : E) :
    0 ≤ valueSquare U p := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem component_square_le_valueSquare {α E : Type*} [Fintype α]
    (U : E → α → ℝ) (p : E) (r : α) : (U p r)^2 ≤ valueSquare U p := by
  classical
  exact Finset.single_le_sum (fun c _ => sq_nonneg (U p c)) (Finset.mem_univ r)

theorem valueFlux_square_bound {n : ℕ} {α : Type*} [Fintype α]
    (d : α → α → Yau.RIdx n → Point n → ℝ) (U : Point n → α → ℝ)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ r c i p, |d r c i p| ≤ D) (r : α) (p : Point n) :
    (∑ i, (valueFlux d U r p i)^2) ≤
      (Fintype.card (Yau.RIdx n) : ℝ) * (Fintype.card α : ℝ) * D^2 * valueSquare U p := by
  calc
    _ ≤ ∑ _i : Yau.RIdx n, (Fintype.card α : ℝ) * D^2 * valueSquare U p :=
      Finset.sum_le_sum fun i _ => matrix_row_square_bound _ _ hD (fun c => hd r c i p)
    _ = _ := by simp; ring

theorem valueSource_square_bound {n : ℕ} {α : Type*} [Fintype α]
    (e : α → α → Point n → ℝ) (U : Point n → α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (he : ∀ r c p, |e r c p| ≤ B) (r : α) (p : Point n) :
    (valueSource e U r p)^2 ≤ (Fintype.card α : ℝ) * B^2 * valueSquare U p :=
  matrix_row_square_bound _ _ hB (fun c => he r c p)

theorem value_forcing_bound {n : ℕ} {α : Type*} [Fintype α]
    (d : α → α → Yau.RIdx n → Point n → ℝ) (e : α → α → Point n → ℝ)
    (U : Point n → α → ℝ) {D B : ℝ} (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hd : ∀ r c i p, |d r c i p| ≤ D) (he : ∀ r c p, |e r c p| ≤ B)
    (r : α) (p : Point n) :
    (U p r)^2 + (∑ i, (valueFlux d U r p i)^2) + (valueSource e U r p)^2 ≤
      (1 + (Fintype.card α : ℝ) *
        ((Fintype.card (Yau.RIdx n) : ℝ) * D^2 + B^2)) * valueSquare U p := by
  have h1 := component_square_le_valueSquare U p r
  have h2 := valueFlux_square_bound d U hD hd r p
  have h3 := valueSource_square_bound e U hB he r p
  nlinarith

end Yau.NodeProofs.P06Aux.CylinderReg

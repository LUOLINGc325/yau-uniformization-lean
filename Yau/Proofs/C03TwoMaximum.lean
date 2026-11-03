import Yau.Proofs.C03SmoothMaximum

/-! A two-function smooth maximum with exact separated branches. -/

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def twoMaximum (δ : ℝ) (f g : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  regularizedMaxCoords (fun _ : Bool => δ) (fun i => if i then g z else f z)

theorem twoMaximum_contDiff (δ : ℝ) (f g : ComplexVector n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (twoMaximum δ f g) := by
  apply (regularizedMaxCoords_smooth (fun _ : Bool => δ)).comp
  exact contDiff_pi.mpr (fun i => by cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption)

theorem twoMaximum_eq_left (δ : ℝ) (hδ : 0 < δ) (f g : ComplexVector n → ℝ)
    (z : ComplexVector n) (hgap : g z + 2 * δ ≤ f z) : twoMaximum δ f g z = f z := by
  apply regularizedMax_eq_separated_coordinate (fun _ : Bool => δ)
    (fun i => if i then g z else f z) false (fun _ => hδ)
  intro i hi
  cases i
  · exact False.elim (hi rfl)
  · change g z + δ ≤ f z - δ
    linarith

theorem twoMaximum_eq_right (δ : ℝ) (hδ : 0 < δ) (f g : ComplexVector n → ℝ)
    (z : ComplexVector n) (hgap : f z + 2 * δ ≤ g z) : twoMaximum δ f g z = g z := by
  apply regularizedMax_eq_separated_coordinate (fun _ : Bool => δ)
    (fun i => if i then g z else f z) true (fun _ => hδ)
  intro i hi
  cases i
  · change f z + δ ≤ g z - δ
    linarith
  · exact False.elim (hi rfl)

theorem twoMaximum_leviC_posSemidef (δ : ℝ) (f g : ComplexVector n → ℝ)
    (z : ComplexVector n) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hfp : (leviC f z).PosSemidef) (hgp : (leviC g z).PosSemidef) :
    (leviC (twoMaximum δ f g) z).PosSemidef := by
  apply regularizedMax_leviC_posSemidef (fun _ : Bool => δ)
  · intro i
    cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption
  · intro i
    cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> assumption

end Yau.Proofs.C03Aux

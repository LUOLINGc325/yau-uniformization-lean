import Yau.Proofs.E03GapChartChange
import Yau.Proofs.F04ChartContinuity

/-! The actual centered gap, extended by zero outside its original positive-time horizon. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

def scalarGap (X : KahlerManifold n) (h : Flow X) (T : ℝ) : STF X :=
  fun y t => if 0 < t ∧ t < T then volumeGap X h T y (chartPt y y) t else 0

theorem scalarGap_positive (h : Flow X) (T : ℝ) (y : Pt X) (t : ℝ)
    (ht : t ∈ Ioo 0 T) :
    scalarGap X h T y t = volumeGap X h T y (chartPt y y) t := by
  unfold scalarGap
  exact ite_eq_left ⟨ht.1, ht.2⟩

theorem scalarGap_zero (h : Flow X) (T : ℝ) (y : Pt X) :
    scalarGap X h T y 0 = 0 := by
  simp [scalarGap]

theorem scalarGap_fixed_chart (h : Flow X) (ρ : STF X)
    (hopt : OptimizerContacts X h ρ) (T : ℝ) (hT : 0 < T)
    (c : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget c) (ht : t ∈ Ioo 0 T) :
    scalarGap X h T (chartInv c z) t = volumeGap X h T c z t := by
  have hy : chartInv c z ∈ (extChartAt (ComplexModel n) c).source :=
    (extChartAt (ComplexModel n) c).map_target hz
  have he := volumeGap_eq_centered h ρ hopt T hT c (chartInv c z) hy t ht
  have hc : chartPt c (chartInv c z) = z :=
    (extChartAt (ComplexModel n) c).right_inv hz
  rw [hc] at he
  rw [scalarGap_positive h T (chartInv c z) t ht]
  exact he.symm

theorem scalarGap_bounds (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (T : ℝ) (hT : 0 < T) (S : ℝ) (hST : S < T)
    (y : Pt X) (t : ℝ) (ht : t ∈ Icc 0 S) :
    0 ≤ scalarGap X h T y t ∧ scalarGap X h T y t ≤ ρ y t := by
  by_cases ht0 : t = 0
  · subst t
    rw [scalarGap_zero]
    exact ⟨le_rfl, Yau.F04Proof.rho_nonneg o h U P ρ hloc y 0 le_rfl⟩
  · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have htime : t ∈ Ioo 0 T := ⟨hpos, ht.2.trans_lt hST⟩
    have hy : chartPt y y ∈ chartTarget y :=
      mem_extChartAt_target (I := ComplexModel n) y
    have hh := (hopt T hT y).2 (chartPt y y) t hy htime
    have hlo := hh.2.1
    have hup := hh.2.2.1
    have hr : chartInv y (chartPt y y) = y :=
      (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source (I := ComplexModel n) y)
    rw [hr] at hup
    rw [scalarGap_positive h T y t htime]
    exact ⟨hlo, hup⟩

end Yau.NodeProofs.E03Aux

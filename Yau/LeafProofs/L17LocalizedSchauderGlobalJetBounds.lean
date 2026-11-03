import Yau.LeafProofs.L17LocalizedSchauderGlobalJets

open Set Metric
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux Yau.LeafProofs.L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem globalUnitValue_jet_bounds (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (v : P.centers → ComplexVector n × Time T → ℝ)
    (D : P.centers → ComplexVector n × Time T → D1 n)
    (H : P.centers → ComplexVector n × Time T → D2 n)
    (b : P.centers → ComplexVector n × Time T → ℝ)
    (hTrue : LocalTrueJets P T hT v D H b) {gamma B : ℝ} (hB : 0 ≤ B)
    (hEach : ∀ (p : P.centers) (q : M.Carrier) (t s : Time T) (z w : ComplexVector n),
      z ∈ ball 0 1 → w ∈ ball 0 1 → ∀ j, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z-
        iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) s) w‖ ≤
          B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma)
    (q : M.Carrier) (t s : Time T) {z w : ComplexVector n}
    (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1) (j : ℕ) (hj : j ≤ 2) :
    ‖iteratedFDeriv ℝ j (globalUnitValue P T v q t) z‖ ≤ (P.overlapBudget : ℝ)*B ∧
    ‖iteratedFDeriv ℝ j (globalUnitValue P T v q t) z-
      iteratedFDeriv ℝ j (globalUnitValue P T v q s) w‖ ≤
      (2*(P.overlapBudget : ℝ))*B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  classical
  rw [globalUnitValue_iteratedFDeriv_eq_finsum P T hT v D H b hTrue q t hz j hj,
    globalUnitValue_iteratedFDeriv_eq_finsum P T hT v D H b hTrue q s hw j hj]
  obtain ⟨I,hI,hActiveI⟩ := exists_active_finset P (P.charts.chart q (P.radius • z))
  obtain ⟨J,hJ,hActiveJ⟩ := exists_active_finset P (P.charts.chart q (P.radius • w))
  have hIZero (p : P.centers) (hp : p ∉ I) :
      iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) t) z = 0 :=
    unitLocalizedTerm_iteratedFDeriv_zero P T p q (v p) t hz (hActiveI p hp) j
  have hJZero (p : P.centers) (hp : p ∉ J) :
      iteratedFDeriv ℝ j (unitLocalizedTerm P T p q (v p) s) w = 0 :=
    unitLocalizedTerm_iteratedFDeriv_zero P T p q (v p) s hw (hActiveJ p hp) j
  constructor
  · exact (norm_finsum_le _ I B hIZero (fun p _ => (hEach p q t s z w hz hw j hj).1)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hB)
  · have hh := norm_finsum_sub_le_two_overlap _ _ I J P.overlapBudget
      (B*(unitParabolicDistance P.radius (z,t) (w,s))^gamma)
      (mul_nonneg hB (Real.rpow_nonneg (unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)) _))
      hI hJ hIZero hJZero (fun p _ => (hEach p q t s z w hz hw j hj).2)
    exact hh.trans_eq (by ring)

end Yau.LeafProofs.L17LocalizedSchauderAux

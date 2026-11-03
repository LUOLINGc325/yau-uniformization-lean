import Yau.LeafProofs.L23LocalDistanceSupportMinimizingGeodesic

/-! Complete original metrics supply the actual compactly confined
near-minimizers used by the static L23 geodesic construction. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_complete_minimizing_fieldGeodesic (g : SmoothMetric M) (o q : M.Carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
      γ 0 = o ∧ γ 1 = q ∧ FieldGeodesicOn g.form γ (Set.Ioo (-δ) (1+δ)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq g.form γ u = inducedDistance g.form o q ^ 2 := by
  have hh := metricSmooth_of_smoothMetric g
  let S : Set M.Carrier := {x | inducedDistance g.form o x ≤ inducedDistance g.form o q + 1}
  have hS : IsCompact S := isCompact_inducedDistance_sublevel g o _
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ β : IntegrableCurve g.form o q,
      curveLength g.form β.1 < inducedDistance g.form o q + ε ∧
        Set.MapsTo β.1 (Set.Icc (0 : ℝ) 1) S := by
    intro ε hε
    obtain ⟨β,hβ⟩ := L12Aux.exists_nearMinimizingCurve g o q
      (lt_min hε (show (0 : ℝ) < 1 by norm_num))
    refine ⟨β,hβ.trans_le (add_le_add le_rfl (min_le_left ε 1)),?_⟩
    intro u hu
    have H := (inducedDistance_le_fieldPathELength_piecewise g.form hh β.1 hu).trans
      (fieldPathELength_mono g.form β.1 le_rfl hu.2)
    rw [fieldPathELength_of_integrableCurve g.form β] at H
    have Hreal := (ENNReal.ofReal_le_ofReal_iff (curveLength_nonneg g.form β.1)).mp H
    change inducedDistance g.form o (β.1 u) ≤ inducedDistance g.form o q + 1
    exact Hreal.trans (hβ.le.trans (add_le_add le_rfl (min_le_right ε 1)))
  obtain ⟨δ,hδ,γ,hγ0,hγ1,hγ,_,hspeed⟩ :=
    compactMinimizingGeodesic n M g.form hh Set.univ S isOpen_univ hS
      (Set.subset_univ S) o q hnear
  exact ⟨δ,hδ,γ,hγ0,hγ1,hγ,hspeed⟩

end Yau.NodeProofs.P07DistanceLevi

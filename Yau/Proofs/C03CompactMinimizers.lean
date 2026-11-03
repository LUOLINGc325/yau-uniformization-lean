import Yau.LeafProofs.L23LocalDistanceSupportMinimizingGeodesic

/-! Compact distance sublevels give genuine minimizing geodesics for a smooth
Hermitian field; no global Kähler or completeness structure is assumed. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem minimizing_geodesic_of_compact_sublevels
    (h : HermitianField M) (hh : MetricSmooth h)
    (hcompact : ∀ p R, IsCompact {x | inducedDistance h p x ≤ R}) (o q : M.Carrier) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ : ℝ → M.Carrier,
      γ 0 = o ∧ γ 1 = q ∧ FieldGeodesicOn h γ (Set.Ioo (-δ) (1 + δ)) ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq h γ u = inducedDistance h o q ^ 2 := by
  let S : Set M.Carrier := {x | inducedDistance h o x ≤ inducedDistance h o q + 1}
  have hS : IsCompact S := hcompact o _
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ β : IntegrableCurve h o q,
      curveLength h β.1 < inducedDistance h o q + ε ∧
        Set.MapsTo β.1 (Set.Icc (0 : ℝ) 1) S := by
    intro ε hε
    obtain ⟨β, hβ⟩ := L23Aux.exists_nearMinimizingCurve h hh o q
      (lt_min hε (show (0 : ℝ) < 1 by norm_num))
    refine ⟨β, hβ.trans_le (add_le_add le_rfl (min_le_left ε 1)), ?_⟩
    intro u hu
    have H := (inducedDistance_le_fieldPathELength_piecewise h hh β.1 hu).trans
      (fieldPathELength_mono h β.1 le_rfl hu.2)
    rw [fieldPathELength_of_integrableCurve h β] at H
    have Hreal := (ENNReal.ofReal_le_ofReal_iff (curveLength_nonneg h β.1)).mp H
    change inducedDistance h o (β.1 u) ≤ inducedDistance h o q + 1
    exact Hreal.trans (hβ.le.trans (add_le_add le_rfl (min_le_right ε 1)))
  obtain ⟨δ, hδ, γ, hγ0, hγ1, hγ, _, hspeed⟩ :=
    compactMinimizingGeodesic n M h hh Set.univ S isOpen_univ hS
      (Set.subset_univ S) o q hnear
  exact ⟨δ, hδ, γ, hγ0, hγ1, hγ, hspeed⟩

end Yau.Proofs.C03Aux

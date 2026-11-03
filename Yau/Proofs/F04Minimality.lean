import Yau.Proofs.F04SmoothSubcaloric

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ}

theorem nonpos_of_smoothPositive_zero (s : ℝ)
    (hs : ∀ δ : ℝ, 0 < δ → smoothPositive δ s = 0) : s ≤ 0 := by
  by_contra h
  have hp : 0 < s := lt_of_not_ge h
  have hδ : 0 < s / 2 := by positivity
  have he := smoothPositive_error_le hδ s
  rw [hs (s / 2) hδ, max_eq_left hp.le, zero_sub, abs_neg, abs_of_pos hp] at he
  linarith

/-- The original rho is minimal among the original smooth nonnegative
 source solutions. Finite cutoff Gronwall precedes the cutoff limit. -/
theorem rho_minimal_from_dependencies (hP07 : P07) (hF03 : F03) (hG02 : G02)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (ρ' : STF X) (hρ' : SmoothSpaceTime ρ' (Icc 0 T))
    (hρ'pos : ∀ x t, t ∈ Icc 0 T → 0 ≤ ρ' x t)
    (_hρ'zero : ∀ x, ρ' x 0 = 0)
    (hρ'eq : ∀ x t, t ∈ Icc 0 T →
      heatOp h (Icc 0 T) ρ' x t = traceWith (gMat (h t) x) (ricci X.metric.form x)) :
    ∀ x t, t ∈ Icc 0 T → ρ x t ≤ ρ' x t := by
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  let w := fun x t => ρ x t - ρ' x t
  have hw : SmoothSpaceTime w (Icc 0 T) := fun c => (hρ c).sub (hρ' c)
  have hcal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) w x t ≤ 0 := by
    intro x t ht
    calc
      heatOp h (Icc 0 T) w x t =
          heatOp h (Icc 0 T) ρ x t - heatOp h (Icc 0 T) ρ' x t :=
        heatOp_sub_smooth h hT hρ hρ' x ht
      _ = 0 := by
        rw [rho_source_equation o h U P ρ hloc T hT x t ht, hρ'eq x t ht]
        simp only [source, sub_self]
      _ ≤ 0 := le_rfl
  have hz (δ : ℝ) (hδ : 0 < δ) :
      ∀ x t, t ∈ Icc 0 T → smoothPositive δ (w x t) = 0 := by
    apply dominated_subcaloric_uniqueness_from_dependencies hP07 hF03 hG02 X o h U P ρ hloc hT
      (z := fun x t => smoothPositive δ (w x t))
    · exact fun c => (smoothPositive_contDiff δ).comp_contDiffOn (hw c)
    · intro x t ht
      have hb := smoothPositive_bounds hδ (w x t)
      refine ⟨hb.1, hb.2.trans ?_⟩
      exact max_le (sub_le_self _ (hρ'pos x t ht)) (rho_nonneg o h U P ρ hloc x t ht.1)
    · exact smoothPositive_subcaloric h hT hw hδ hcal
  intro x t ht
  have hnonpos := nonpos_of_smoothPositive_zero (w x t) (fun δ hδ => hz δ hδ x t ht)
  exact sub_nonpos.mp hnonpos

end Yau.F04Proof

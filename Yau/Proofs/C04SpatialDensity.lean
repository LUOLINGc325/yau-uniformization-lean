import Yau.Proofs.C04HarnackComparison
import Yau.Proofs.C04ShiftedPrimitives
import Yau.Proofs.C04Clock

/-! The original volume density divided by the same basepoint clock tends uniformly to one. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem compact_rho_ratio (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    ∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      |ρ x t / ρ o t - 1| ≤ ε := by
  intro K hK ε hε
  let η := ε / 2
  have hη : 0 < η := half_pos hε
  have hk : 0 < 1 + η := by linarith
  obtain ⟨T₁, hT₁, hcompare⟩ := compact_scalar_harnack_comparison X o h U P ρ hf hH K hK η hη
  obtain ⟨T₂, hT₂⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH)) 1
  let A := max T₁ T₂
  have hA1 : 1 ≤ A := hT₁.trans (le_max_left _ _)
  have hA : 0 < A := zero_lt_one.trans_le hA1
  obtain ⟨C₀, hC₀⟩ := localizedFlow_rho_compact_bound X o h U P ρ hf hA.le K hK
  let C := max (C₀ + (1 + η) * |ρ o (A + 1)|) |ρ o A|
  have hC : 0 ≤ C := (abs_nonneg _).trans (le_max_right _ _)
  obtain ⟨B₀, hB₀⟩ := hH.2.2.2.2.2.2.1
  let B := max B₀ 1
  have hB : 0 ≤ B := zero_le_one.trans (le_max_right _ _)
  have hbaseDeriv : ∀ t, A ≤ t → HasDerivAt (ρ o) (scalarCurvature (h t) o) t :=
    fun t ht => rho_hasDerivAt X o h U P ρ hf o (hA.trans_le ht)
  have hbaseBound : ∀ t, A ≤ t → scalarCurvature (h t) o ≤ B :=
    fun t ht => (hB₀ t (hA.le.trans ht)).trans (le_max_left _ _)
  let D := (1 + η) * B + C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDlim : Tendsto (fun t => D / ρ o t) atTop (𝓝 0) :=
    (rho_tendsto_atTop X o h U P ρ hf hH).const_div_atTop D
  obtain ⟨T₃, hT₃⟩ := eventually_atTop.1 ((tendsto_order.1 hDlim).2 η hη)
  refine ⟨max (A + 1) T₃, ?_⟩
  intro t ht x hx
  have htA1 : A + 1 ≤ t := (le_max_left _ _).trans ht
  have htA : A ≤ t := by linarith
  have htmA : A ≤ t - 1 := by linarith
  have ht0 : 0 ≤ t := hA.le.trans htA
  have hs1 : 1 ≤ ρ o t := hT₂ t ((le_max_right T₁ T₂).trans htA)
  have hs : 0 < ρ o t := zero_lt_one.trans_le hs1
  have hu : 0 ≤ ρ x t := (hf.2.2.2.2.2.2.2.2.2.1 x t ht0).2
  have huderiv : ∀ v, A ≤ v → HasDerivAt (ρ x) (scalarCurvature (h v) x) v :=
    fun v hv => rho_hasDerivAt X o h U P ρ hf x (hA.trans_le hv)
  have hupper₀ := shifted_primitive_upper huderiv hbaseDeriv
    (fun v hv => (hcompare v ((le_max_left T₁ T₂).trans hv) x hx).1) htA
  have hlower₀ := shifted_primitive_upper hbaseDeriv huderiv
    (fun v hv => (hcompare v ((le_max_left T₁ T₂).trans hv) x hx).2) htmA
  have hCupper : ρ x A - (1 + η) * ρ o (A + 1) ≤ C := by
    have hh := hC₀ x hx
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs (ρ o (A + 1))) hk.le
    have hCa := le_max_left (C₀ + (1 + η) * |ρ o (A + 1)|) |ρ o A|
    nlinarith [le_abs_self (ρ x A)]
  have hClower : ρ o A - (1 + η) * ρ x (A + 1) ≤ C := by
    have hun : 0 ≤ ρ x (A + 1) :=
      (hf.2.2.2.2.2.2.2.2.2.1 x (A + 1) (by linarith)).2
    have hCa := le_max_right (C₀ + (1 + η) * |ρ o (A + 1)|) |ρ o A|
    nlinarith [le_abs_self (ρ o A), mul_nonneg hk.le hun]
  have hupper : ρ x t ≤ (1 + η) * ρ o (t + 1) + C := by linarith
  have hlower : ρ o (t - 1) ≤ (1 + η) * ρ x t + C := by
    have htime : t - 1 + 1 = t := by ring
    rw [htime] at hlower₀
    linarith
  have hshiftup := primitive_unit_shift_bound hbaseDeriv hbaseBound htA
  have hshiftdown := primitive_unit_shift_bound hbaseDeriv hbaseBound htmA
  have htime : t - 1 + 1 = t := by ring
  rw [htime] at hshiftdown
  have hr := ratio_bound_of_shifted_comparisons hη.le hC hB hs hu hupper hlower hshiftup hshiftdown
  have hsmall := hT₃ t ((le_max_right _ _).trans ht)
  dsimp [D] at hsmall
  dsimp [η] at hr hsmall
  linarith

end Yau.Proofs.C04Aux

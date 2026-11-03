import Yau.Blueprint.Nodes

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ}

/-- Enlarging the metric comparison constant puts the lower and upper chart
bounds in the reciprocal form used in the shrinking-chart contract. -/
theorem unitaryChart_reciprocal {M : ComplexManifold n} {k : HermitianField M}
    {p : M.Carrier} {Φ : ComplexVector n → M.Carrier} {r c C D : ℝ}
    (hc : 0 < c) (hD : 0 < D) (hCD : C ≤ D) (hcD : c⁻¹ ≤ D)
    (hΦ : UnitaryChart k p Φ r c C) : UnitaryChart k p Φ r D⁻¹ D := by
  have hinv : D⁻¹ ≤ c := (inv_le_comm₀ hD hc).2 hcD
  have hscalar {a b : ℝ} (hab : a ≤ b) :
      HermLE ((a : ℂ) • (1 : Herm n)) ((b : ℂ) • (1 : Herm n)) := by
    unfold HermLE
    rw [← sub_smul, ← Complex.ofReal_sub]
    exact (Matrix.PosSemidef.one : (1 : Herm n).PosSemidef).smul
      (show (0 : ℂ) ≤ ((b - a : ℝ) : ℂ) by
        simpa only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im, and_true]
          using sub_nonneg.mpr hab)
  refine ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, ?_⟩
  intro z hz
  rcases hΦ.2.2.2 z hz with ⟨hlo, hhi⟩
  have hleft := (hscalar hinv).add hlo
  have hright := hhi.add (hscalar hCD)
  constructor
  · convert hleft using 1 <;> unfold HermLE at * <;> congr 1 <;> abel
  · convert hright using 1 <;> unfold HermLE at * <;> congr 1 <;> abel

/-- Select the same centered charts for all physical times from the original
uniform-chart predecessor.  No clock or transition map is changed here. -/
theorem centered_chart_family {X : KahlerManifold n} (o : Pt X) (h : Flow X)
    (hcharts : UniformCharts X h) :
    ∃ r C t₀ : ℝ, ∃ Φ : ℝ → ComplexVector n → Pt X,
      0 < r ∧ 0 < C ∧
      ∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r C⁻¹ C := by
  classical
  obtain ⟨r, c, C, t₀, hr, hc, hC, Cm, hfamily⟩ :=
    hcharts {o} (isCompact_singleton : IsCompact ({o} : Set (Pt X)))
  let D := max 1 (max C c⁻¹)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCD : C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hcD : c⁻¹ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hex (t : ℝ) : ∃ Φ : ComplexVector n → Pt X,
      t₀ ≤ t → UnitaryChart (h t) o Φ r D⁻¹ D := by
    by_cases ht : t₀ ≤ t
    · obtain ⟨Φ, hΦ, _⟩ := hfamily t ht o (Set.mem_singleton o)
      exact ⟨Φ, fun _ => unitaryChart_reciprocal hc hD hCD hcD hΦ⟩
    · exact ⟨fun _ => o, fun h => False.elim (ht h)⟩
  choose Φ hΦ using hex
  exact ⟨r, D, t₀, Φ, hr, hD, hΦ⟩

end Yau.Proofs.C07Aux

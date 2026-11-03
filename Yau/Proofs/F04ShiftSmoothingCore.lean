import Yau.Proofs.F04SupportedCutoff
import Yau.Proofs.F04ScalarExteriorLocality
import Yau.Proofs.F04SmoothPositiveScalar

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Support repair for a shift nonnegative only on the actual domain. The
cutoff error disappears because the one-sided smoothing and its derivative
vanish on the nonpositive half-line. -/
theorem exists_shift_smoothing_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (δ : ℝ) (hδ : 0 < δ) (r : M.Carrier → ℝ) (hr : SmoothFn r)
    (hr0 : ∀ x ∈ O, 0 ≤ r x) (f : dirichletCore g μ hμ O) :
    ∃ q : dirichletCore g μ hμ O,
      EqOn (q.val : M.Carrier → ℝ) (fun x => smoothPositive δ (f.val x - r x)) O ∧
      ∀ x ∈ O, scalarExterior q.val x =
        multiplyRealForm (fun y => deriv (smoothPositive δ) (f.val y - r y))
          (scalarExterior f.val - scalarExterior r) x := by
  obtain ⟨η, W, hη, hcη, hηO, _, hKW, _, hηone, _⟩ :=
    exists_supported_smooth_cutoff (tsupport (f.val : M.Carrier → ℝ)) O f.val.2.2 hO f.property
  have hfr : SmoothFn (fun x => f.val x - r x) := fun c => (f.val.2.1 c).sub (hr c)
  have hb : SmoothFn (fun x => smoothPositive δ (f.val x - r x)) :=
    fun c => (smoothPositive_contDiff δ).comp_contDiffOn (hfr c)
  let q : dirichletCore g μ hμ O :=
    ⟨⟨fun x => η x * smoothPositive δ (f.val x - r x),
      (fun c => (hη c).mul (hb c)), hcη.mul_right⟩, tsupport_mul_subset_left.trans hηO⟩
  have he : EqOn (q.val : M.Carrier → ℝ) (fun x => smoothPositive δ (f.val x - r x)) O := by
    intro x hx
    change η x * smoothPositive δ (f.val x - r x) = smoothPositive δ (f.val x - r x)
    by_cases hxf : x ∈ tsupport (f.val : M.Carrier → ℝ)
    · rw [hηone x (hKW hxf), one_mul]
    · have hf0 : f.val x = 0 := image_eq_zero_of_notMem_tsupport hxf
      have hz : smoothPositive δ (f.val x - r x) = 0 :=
        smoothPositive_of_nonpos hδ (by rw [hf0, zero_sub]; exact neg_nonpos.mpr (hr0 x hx))
      rw [hz, mul_zero]
  refine ⟨q, he, ?_⟩
  intro x hx
  have hsub : scalarExterior (fun y => f.val y - r y) = scalarExterior f.val - scalarExterior r :=
    scalarExterior_sub f.val.2.1 hr
  rw [scalarExterior_congr_on_open q.val.2.1 hb O hO he x hx,
    scalarExterior_scalar_comp hfr (smoothPositive δ) (smoothPositive_contDiff δ), hsub]

end Yau.F04Proof

import spec.CHAIN.LeafCandidates

/-!
Internal adapters for the corrected L22 source statement. The two analytic
bridge targets remain unproved and are explicit parameters of the conditional
adapter; this module neither assumes a source axiom nor proves P02.
-/

open scoped Topology Manifold ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.LeafCandidates

variable {n : ℕ} {M : Yau.ComplexManifold n}

/-- The actual P02 metric supplies the regularity missing in MF-L22-01. -/
theorem smoothMetric_continuousHermitianCoefficients (g : Yau.SmoothMetric M) :
    ContinuousHermitianCoefficients g.form := by
  intro p i j
  exact (g.coordinate_smooth p i j).continuousOn

theorem smoothFn_add_const {u : M.Carrier → ℝ} (hu : Yau.SmoothFn u) (c : ℝ) :
    Yau.SmoothFn (fun x => u x + c) := by
  intro p
  exact (hu p).add contDiffOn_const

theorem levi_add_const (u : M.Carrier → ℝ) (c : ℝ) (p : M.Carrier) :
    Yau.levi (fun x => u x + c) p = Yau.levi u p := by
  ext i j
  simp only [Yau.levi, Yau.leviC, Yau.leviMatrix, Yau.inChart, Yau.wirt,
    Yau.wirtBar, Complex.ofReal_add, fderiv_add_const]

/-- Conditional P02 adapter. The two internal bridge targets are explicit
parameters and remain unproved; they are not part of L22. A half-unit fine
approximation followed by a constant half-unit shift proves the required
one-sided unit bounds, without perturbing by a merely continuous error. -/
theorem richberg_one_sided_unit_of_bridge_targets
    (h22 : RichbergApproximation)
    (hViscosity : ViscosityToClassicalBridgeTarget)
    (hSmooth : SmoothClassicalLeviBridgeTarget)
    (g : Yau.SmoothMetric M) (u : M.Carrier → ℝ)
    (hu : ContinuousStrictPsh g.form u) :
    ∃ ψ : M.Carrier → ℝ, Yau.IsSmoothStrictPsh ψ ∧
      ∀ x, u x ≤ ψ x ∧ ψ x ≤ u x + 1 := by
  have hclassical := hViscosity n M g.form u
    (smoothMetric_continuousHermitianCoefficients g) hu
  obtain ⟨φ, hφsmooth, hφclassical, herror⟩ :=
    h22 n M u (fun _ => (1 / 2 : ℝ)) hclassical continuous_const (by intro x; norm_num)
  refine ⟨fun x => φ x + 1 / 2, ⟨smoothFn_add_const hφsmooth (1 / 2), ?_⟩, ?_⟩
  · intro x
    rw [levi_add_const]
    exact hSmooth n M φ hφsmooth hφclassical x
  · intro x
    have hx := abs_lt.mp (herror x)
    constructor <;> linarith [hx.1, hx.2]

end Yau.LeafCandidates

import spec.CHAIN.LeafObligations

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A connected noncompact carrier cannot be a zero-dimensional complex
manifold. This handles the dimension-zero case of the frozen root without
adding a positive-dimension hypothesis to its statement. -/
theorem dimension_pos (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := PreconnectedSpace.trivial_of_discrete
  letI : CompactSpace M.Carrier := inferInstance
  exact (isCompact_univ : IsCompact (univ : Set M.Carrier)).ne_univ rfl

/-- The actual affine circle of a disc lying in the coordinate domain stays
in that domain and pulls a continuous coordinate function back continuously. -/
theorem continuous_affine_circle {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : ContinuousOn f O)
    (z w : ComplexVector n)
    (hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ O) :
    Continuous (fun θ : ℝ => f (z + Complex.exp (θ * Complex.I) • w)) := by
  have hpath : Continuous (fun θ : ℝ => z + Complex.exp (θ * Complex.I) • w) := by
    fun_prop
  apply hf.comp_continuous hpath
  intro θ
  apply hdisc
  simp

theorem circleAverage_const (c : ℝ) : circleAverage (fun _ => c) = c := by
  unfold circleAverage
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

theorem circleAverage_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    circleAverage (fun θ => f θ + g θ) = circleAverage f + circleAverage g := by
  unfold circleAverage
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
    mul_add]

theorem circleAverage_smul (c : ℝ) (f : ℝ → ℝ) :
    circleAverage (fun θ => c * f θ) = c * circleAverage f := by
  unfold circleAverage
  rw [intervalIntegral.integral_const_mul]
  ring

theorem circleAverage_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) : circleAverage f ≤ circleAverage g := by
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) (fun θ _ => hfg θ))
  positivity

theorem complexLinePshOn_const (O : Set (ComplexVector n)) (c : ℝ) :
    LeafCandidates.ComplexLinePshOn O (fun _ => c) := by
  refine ⟨continuousOn_const, ?_⟩
  intro z w hdisc
  rw [circleAverage_const]

theorem complexLinePshOn_mono {O V : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (hVO : V ⊆ O) : LeafCandidates.ComplexLinePshOn V f := by
  refine ⟨hf.1.mono hVO, ?_⟩
  intro z w hdisc
  exact hf.2 z w (fun ζ hζ => hVO (hdisc ζ hζ))

theorem complexLinePshOn_congr {O : Set (ComplexVector n)}
    {f g : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (hfg : EqOn f g O) : LeafCandidates.ComplexLinePshOn O g := by
  refine ⟨hf.1.congr hfg.symm, ?_⟩
  intro z w hdisc
  have hz : z ∈ O := by simpa using hdisc 0 (by simp)
  have hc : (fun θ : ℝ => f (z + Complex.exp (θ * Complex.I) • w)) =
      (fun θ : ℝ => g (z + Complex.exp (θ * Complex.I) • w)) := by
    funext θ
    apply hfg
    exact hdisc _ (by simp)
  rw [← hfg hz, ← hc]
  exact hf.2 z w hdisc

theorem complexLinePshOn_add {O : Set (ComplexVector n)}
    {f g : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (hg : LeafCandidates.ComplexLinePshOn O g) :
    LeafCandidates.ComplexLinePshOn O (fun z => f z + g z) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro z w hdisc
  rw [circleAverage_add (continuous_affine_circle hf.1 z w hdisc)
    (continuous_affine_circle hg.1 z w hdisc)]
  exact add_le_add (hf.2 z w hdisc) (hg.2 z w hdisc)

theorem complexLinePshOn_smul {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    {c : ℝ} (hc : 0 ≤ c) :
    LeafCandidates.ComplexLinePshOn O (fun z => c * f z) := by
  refine ⟨continuousOn_const.mul hf.1, ?_⟩
  intro z w hdisc
  rw [circleAverage_smul]
  exact mul_le_mul_of_nonneg_left (hf.2 z w hdisc) hc

theorem complexLinePshOn_add_const {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f) (c : ℝ) :
    LeafCandidates.ComplexLinePshOn O (fun z => f z + c) :=
  complexLinePshOn_add hf (complexLinePshOn_const O c)

theorem complexLinePshOn_sub_const {O : Set (ComplexVector n)}
    {f : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f) (c : ℝ) :
    LeafCandidates.ComplexLinePshOn O (fun z => f z - c) := by
  simpa only [sub_eq_add_neg] using complexLinePshOn_add_const hf (-c)

theorem complexLinePshOn_max {O : Set (ComplexVector n)}
    {f g : ComplexVector n → ℝ} (hf : LeafCandidates.ComplexLinePshOn O f)
    (hg : LeafCandidates.ComplexLinePshOn O g) :
    LeafCandidates.ComplexLinePshOn O (fun z => max (f z) (g z)) := by
  refine ⟨continuous_max.comp_continuousOn (hf.1.prodMk hg.1), ?_⟩
  intro z w hdisc
  have hfcont := continuous_affine_circle hf.1 z w hdisc
  have hgcont := continuous_affine_circle hg.1 z w hdisc
  apply max_le
  · exact (hf.2 z w hdisc).trans
      (circleAverage_mono hfcont (hfcont.max hgcont) (fun _ => le_max_left _ _))
  · exact (hg.2 z w hdisc).trans
      (circleAverage_mono hgcont (hfcont.max hgcont) (fun _ => le_max_right _ _))

theorem classicalStrictPsh_add_const {u : M.Carrier → ℝ}
    (hu : LeafCandidates.ClassicalStrictPsh u) (c : ℝ) :
    LeafCandidates.ClassicalStrictPsh (fun x => u x + c) := by
  refine ⟨hu.1.add continuous_const, ?_⟩
  intro p
  obtain ⟨O, hO, hp, hchart, τ, hτ, hτpos, hpsh⟩ := hu.2 p
  refine ⟨O, hO, hp, hchart, τ, hτ, hτpos, ?_⟩
  convert complexLinePshOn_add_const hpsh c using 1
  funext z
  simp only [inChart]
  ring

/-- For a smooth function with positive computed Levi, its own coordinate
expression is a classical local strictifier. No converse submean theorem is
needed for this direction. -/
theorem classicalStrictPsh_of_smooth_positive {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (huc : Continuous u) (hpos : ∀ x, (levi u x).PosDef) :
    LeafCandidates.ClassicalStrictPsh u := by
  refine ⟨huc, ?_⟩
  intro p
  refine ⟨chartTarget p, isOpen_extChartAt_target p, mem_extChartAt_target p,
    Subset.rfl, inChart p u, hu p, hpos p, ?_⟩
  convert complexLinePshOn_const (chartTarget p) 0 using 1
  funext z
  exact sub_self _

/-- An already smooth input is its own approximation, with the full original
pointwise gauge and the unchanged classical strict-psh predicate. -/
theorem richberg_of_smooth {u ε : M.Carrier → ℝ}
    (hu : LeafCandidates.ClassicalStrictPsh u) (hs : SmoothFn u)
    (hε : ∀ x, 0 < ε x) :
    ∃ ψ : M.Carrier → ℝ, SmoothFn ψ ∧ LeafCandidates.ClassicalStrictPsh ψ ∧
      ∀ x, |ψ x - u x| < ε x := by
  exact ⟨u, hs, hu, fun x => by simpa using hε x⟩

end Yau.LeafProofs.L22Aux

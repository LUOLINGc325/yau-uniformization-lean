import Yau.Proofs.C05GradientFlowGradient
import Yau.LeafProofs.L12HopfRinow
import Yau.LeafProofs.L12BrokenEnergy

/-! Actual minimizing geodesics lie in the required buffered intrinsic balls. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05GradientFlowAux
open Yau Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

def gradientTrap (g : SmoothMetric M) (o : M.Carrier) (r : ℝ) : Set M.Carrier :=
  {x | inducedDistance g.form o x ≤ r / 2}

theorem gradientTrap_isCompact (g : SmoothMetric M) (o : M.Carrier) (r : ℝ) :
    IsCompact (gradientTrap g o r) := isCompact_inducedDistance_sublevel g o (r / 2)

theorem gradientTrap_mem_double_ball (g : SmoothMetric M) (o : M.Carrier)
    {r : ℝ} (hr : 0 < r) {x : M.Carrier} (hx : x ∈ gradientTrap g o r) :
    x ∈ distBall g.form o (2 * r) := by
  apply (mem_distBall_iff g o x (by positivity)).mpr
  change inducedDistance g.form o x ≤ r / 2 at hx
  linarith

theorem realGradientVectorField_norm (k : HermitianField M) (f : M.Carrier → ℝ)
    (x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup k x
    ‖realGradientVectorField k f x‖ = realNorm k x (realGrad k f x) := by
  letI := underlyingRealTangentNormedAddCommGroup k x
  rw [underlyingRealTangent_norm]
  simp only [realGradientVectorField, ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem minimizing_exponential_segment_buffer (g : SmoothMetric M) (o x y : M.Carrier)
    {R : ℝ} (hx : inducedDistance g.form o x ≤ R) (hy : inducedDistance g.form o y ≤ R) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ∃ v : TangentSpace 𝓘(ℝ, ComplexVector n) x,
      realExponentialMap g x v = y ∧ ‖v‖ = inducedDistance g.form x y ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          inducedDistance g.form o (realExponentialMap g x (t • v)) ≤ 2 * R := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  obtain ⟨v, hv, hn⟩ := exists_minimizing_realExponential g x y
  refine ⟨v, hv, hn, ?_⟩
  intro t ht
  have hL : inducedDistance g.form x y ≤ 2 * R := by
    have H := g.induced_distance_triangle x o y
    rw [g.induced_distance_symm x o] at H
    linarith
  have hleft := realExponentialMap_base_dist_le g x v 0 t
  simp only [zero_smul, realExponentialMap_zero, sub_zero, abs_of_nonneg ht.1, hn] at hleft
  have hright := realExponentialMap_base_dist_le g x v 1 t
  simp only [one_smul, hv, hn] at hright
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hright
  have H₁ := g.induced_distance_triangle o x (realExponentialMap g x (t • v))
  have H₂ := g.induced_distance_triangle o y (realExponentialMap g x (t • v))
  nlinarith only [H₁, H₂, hleft, hright, hx, hy, hL]

theorem exists_trap_minimizing_segment (g : SmoothMetric M) (o : M.Carrier)
    {r : ℝ} (hr : 0 < r) (x y : M.Carrier)
    (hx : x ∈ gradientTrap g o r) (hy : y ∈ gradientTrap g o r) :
    letI := underlyingRealTangentNormedAddCommGroup g.form x
    ∃ v : TangentSpace 𝓘(ℝ, ComplexVector n) x,
      realExponentialMap g x v = y ∧ ‖v‖ = inducedDistance g.form x y ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          inducedDistance g.form o (realExponentialMap g x (t • v)) ≤ r ∧
            realExponentialMap g x (t • v) ∈ distBall g.form o (2 * r) := by
  letI := underlyingRealTangentNormedAddCommGroup g.form x
  obtain ⟨v, hv, hn, hbuffer⟩ := minimizing_exponential_segment_buffer g o x y hx hy
  refine ⟨v, hv, hn, ?_⟩
  intro t ht
  have hb : inducedDistance g.form o (realExponentialMap g x (t • v)) ≤ r := by
    linarith [hbuffer t ht]
  refine ⟨hb, (mem_distBall_iff g o _ (by positivity)).mpr ?_⟩
  linarith

theorem exists_minimizing_radial_segment (g : SmoothMetric M) (o x : M.Carrier) :
    letI := underlyingRealTangentNormedAddCommGroup g.form o
    ∃ v : TangentSpace 𝓘(ℝ, ComplexVector n) o,
      realExponentialMap g o v = x ∧ ‖v‖ = inducedDistance g.form o x ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          inducedDistance g.form o (realExponentialMap g o (t • v)) =
            t * inducedDistance g.form o x := by
  letI := underlyingRealTangentNormedAddCommGroup g.form o
  obtain ⟨v, hv, hn⟩ := exists_minimizing_realExponential g o x
  refine ⟨v, hv, hn, ?_⟩
  have hmin : inducedDistance g.form o
      (realGeodesicFlow g (⟨o, v⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) 1).proj = 1 * ‖v‖ := by
    change inducedDistance g.form o (realExponentialMap g o v) = _
    rw [hv, hn, one_mul]
  intro t ht
  rw [realExponentialMap_smul, ← hn]
  exact realGeodesicFlow_dist_eq_of_minimizing g ⟨o, v⟩ 1 hmin t ht

end Yau.Proofs.C05GradientFlowAux

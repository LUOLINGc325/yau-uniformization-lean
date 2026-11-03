import Yau.Proofs.C03FlatCompleteField

/-! The actual length infimum and Riemannian edistance of the half-flat field. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ENNReal
open MeasureTheory Filter Bundle
namespace Yau.Proofs.C03Aux.FlatComplete
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

/-- The tangent norm is exactly the standard Euclidean norm, including its enorm. -/
theorem euclidean_realTangent_enorm (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    let standard := ‖tangentSpaceCastModel 𝓘(ℝ, ComplexVector n) x v‖ₑ
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup (euclideanHermitianField n hn) x
    ‖v‖ₑ = standard := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup (euclideanHermitianField n hn) x
  simpa only [ofReal_norm] using
    congrArg ENNReal.ofReal (euclidean_realTangent_norm n hn x v)

theorem euclidean_riemannianEDist (n : ℕ) (hn : 1 ≤ n)
    (x y : ComplexVector n) :
    letI : ∀ z : (ComplexEuclideanManifold n hn).Carrier,
        NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => L12Aux.underlyingRealTangentNormedAddCommGroup (euclideanHermitianField n hn) z
    Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y = edist x y := by
  let D := Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y
  have hD : D = edist x y := (IsRiemannianManifold.out (I := 𝓘(ℝ, ComplexVector n)) x y).symm
  letI : ∀ z : (ComplexEuclideanManifold n hn).Carrier,
      NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup (euclideanHermitianField n hn) z
  rw [← hD]
  dsimp only [D]
  simp only [Manifold.riemannianEDist_def]
  apply iInf_congr
  intro γ
  apply iInf_congr
  intro hγ
  apply lintegral_congr
  intro t
  rw [euclidean_realTangent_enorm, enorm_tangentSpace_vectorSpace]
  rfl

theorem euclidean_lengthDist (n : ℕ) (hn : 1 ≤ n)
    (x y : ComplexVector n) :
    lengthDist (euclideanHermitianField n hn) x y = dist x y := by
  have he := L23Aux.inducedDistance_eq_riemannianEDist
    (euclideanHermitianField n hn) (euclidean_metricSmooth n hn) x y
  rw [euclidean_riemannianEDist, edist_dist] at he
  simpa only [ENNReal.toReal_ofReal
      (L23Aux.inducedDistance_nonneg _ (euclidean_metricSmooth n hn) x y),
    ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal he

theorem euclidean_complete_distance (n : ℕ) (hn : 1 ≤ n) :
    IsCompleteDistance (lengthDist (euclideanHermitianField n hn)) := by
  intro s hs
  let t : ℕ → ComplexVector n := s
  have hc : CauchySeq t := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm k hk => ?_⟩
    change dist (t m) (t k) < ε
    rw [← euclidean_lengthDist n hn]
    exact hN m k hm hk
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx ε hε
  refine ⟨N, fun k hk => ?_⟩
  rw [euclidean_lengthDist]
  exact hN k hk

end Yau.Proofs.C03Aux.FlatComplete

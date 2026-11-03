import Yau.LeafProofs.L12EndpointBranch
import Yau.LeafProofs.L12IndexAnalysis

/-! Genuine three-segment energy bounds and minimizing geodesic prefixes. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L12Aux
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

/-- The three-leg weighted Cauchy--Schwarz estimate, with all durations
positive and actual nonnegative speeds. -/
theorem three_weighted_energy_lower_bound {s e d ν a b c : ℝ}
    (hs : 0 < s) (he : 0 < e) (hd : 0 < d)
    (hν : 0 ≤ ν) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hlen : (s + e + d) * ν ≤ s * a + e * b + d * c) :
    ((s + e + d) / 2) * ν ^ 2 ≤ (s / 2) * a ^ 2 + (e / 2) * b ^ 2 + (d / 2) * c ^ 2 := by
  let r := s + e + d
  let L := s * a + e * b + d * c
  have hr : 0 < r := by dsimp [r]; linarith
  have hL : 0 ≤ L := add_nonneg (add_nonneg (mul_nonneg hs.le ha) (mul_nonneg he.le hb)) (mul_nonneg hd.le hc)
  have hlen' : r * ν ≤ L := hlen
  have hsq : (r * ν) ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlen') (add_nonneg hL (mul_nonneg hr.le hν))]
  have hcs : L ^ 2 ≤ r * (s * a ^ 2 + e * b ^ 2 + d * c ^ 2) := by
    have hab := mul_nonneg (mul_nonneg hs.le he.le) (sq_nonneg (a - b))
    have hac := mul_nonneg (mul_nonneg hs.le hd.le) (sq_nonneg (a - c))
    have hbc := mul_nonneg (mul_nonneg he.le hd.le) (sq_nonneg (b - c))
    dsimp only [r, L]
    nlinarith
  have htotal : r * (r * ν ^ 2) ≤ r * (s * a ^ 2 + e * b ^ 2 + d * c ^ 2) := by
    nlinarith [hsq.trans hcs]
  have h := le_of_mul_le_mul_left htotal hr
  dsimp only [r] at h
  nlinarith

variable {n : ℕ} {M : ComplexManifold n}

/-- Every prefix of an actual minimizing geodesic segment minimizes for
the original project length distance. -/
theorem realGeodesicFlow_dist_eq_of_minimizing (g : SmoothMetric M)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier) (T : ℝ) :
    letI := underlyingRealTangentNormedAddCommGroup g.form p.proj
    inducedDistance g.form p.proj (realGeodesicFlow g p T).proj = T * ‖p.2‖ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        inducedDistance g.form p.proj (realGeodesicFlow g p t).proj = t * ‖p.2‖ := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  intro hmin t ht
  have hfirst := realGeodesicFlow_distFrom_le g p t
  rw [realTangentEnergy_eq_norm_sq, Real.sqrt_sq (norm_nonneg p.2), abs_of_nonneg ht.1] at hfirst
  have htail := realGeodesicFlow_base_dist_le g p t T
  rw [abs_of_nonneg (sub_nonneg.mpr ht.2)] at htail
  have htri := g.induced_distance_triangle p.proj (realGeodesicFlow g p t).proj (realGeodesicFlow g p T).proj
  rw [hmin] at htri
  apply le_antisymm
  · nlinarith
  · nlinarith

/-- The sum of the actual energies of three joined genuine geodesic
segments dominates the endpoint distance energy. -/
theorem realBrokenGeodesicEnergy_lower_bound (g : SmoothMetric M)
    (p₀ p₁ p₂ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {s e d ν : ℝ} (hs : 0 < s) (he : 0 < e) (hd : 0 < d) (hν : 0 ≤ ν)
    (hjoin₀ : (realGeodesicFlow g p₀ s).proj = p₁.proj)
    (hjoin₁ : (realGeodesicFlow g p₁ e).proj = p₂.proj)
    (hDist : (s + e + d) * ν ≤ inducedDistance g.form p₀.proj (realGeodesicFlow g p₂ d).proj) :
    ((s + e + d) / 2) * ν ^ 2 ≤
      (s / 2) * realTangentEnergy g.form p₀ + (e / 2) * realTangentEnergy g.form p₁ +
        (d / 2) * realTangentEnergy g.form p₂ := by
  have h₀ := realGeodesicFlow_distFrom_le g p₀ s
  have h₁ := realGeodesicFlow_distFrom_le g p₁ e
  have h₂ := realGeodesicFlow_distFrom_le g p₂ d
  rw [hjoin₀, abs_of_pos hs] at h₀
  rw [hjoin₁, abs_of_pos he] at h₁
  rw [abs_of_pos hd] at h₂
  have htri₀ := g.induced_distance_triangle p₀.proj p₁.proj (realGeodesicFlow g p₂ d).proj
  have htri₁ := g.induced_distance_triangle p₁.proj p₂.proj (realGeodesicFlow g p₂ d).proj
  have hlen : (s + e + d) * ν ≤ s * Real.sqrt (realTangentEnergy g.form p₀) +
      e * Real.sqrt (realTangentEnergy g.form p₁) + d * Real.sqrt (realTangentEnergy g.form p₂) := by
    nlinarith
  have h := three_weighted_energy_lower_bound hs he hd hν
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hlen
  rwa [Real.sq_sqrt (realTangentEnergy_nonneg g.form p₀),
    Real.sq_sqrt (realTangentEnergy_nonneg g.form p₁),
    Real.sq_sqrt (realTangentEnergy_nonneg g.form p₂)] at h

end Yau.LeafProofs.L12Aux

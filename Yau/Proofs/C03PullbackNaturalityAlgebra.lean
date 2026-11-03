import Yau.LeafProofs.L23FieldMetricConnection

/-! The pointwise uniqueness argument for a metric-compatible torsion-free
connection, including a surjective coordinate derivative. -/

noncomputable section

namespace Yau.Proofs.C03Aux.PullbackNaturality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem symmetric_metric_skew_vanish
    (g : E →L[ℝ] E →L[ℝ] ℝ) (J : E → E) (D : E → E → E)
    (hg : ∀ u v, g u v = g v u)
    (hpos : ∀ u, g u u = 0 → u = 0) (hJ : Function.Surjective J)
    (hD : ∀ u v, D u v = D v u)
    (hcomp : ∀ u v w, g (D u v) (J w) + g (J v) (D u w) = 0) :
    ∀ u v, D u v = 0 := by
  have hpair (u v w : E) : g (D u v) (J w) = 0 := by
    have h₁ := hcomp u v w
    have h₂ := hcomp w u v
    have h₃ := hcomp v w u
    rw [hg (J v) (D u w)] at h₁
    rw [hD w u, hg (J u) (D w v)] at h₂
    rw [hD v w, hD v u, hg (J w) (D u v)] at h₃
    linarith
  intro u v
  apply hpos
  obtain ⟨w, hw⟩ := hJ (D u v)
  simpa only [hw] using hpair u v w

end Yau.Proofs.C03Aux.PullbackNaturality

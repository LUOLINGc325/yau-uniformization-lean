import Yau.Proofs.P01RayFinite

noncomputable section
open scoped NNReal

namespace Yau.NodeProofs.P01Aux

variable {E : Type*} [MetricSpace E] [ProperSpace E] [NoncompactSpace E]

theorem exists_dist_gt_of_proper_noncompact (o : E) (R : ℝ) :
    ∃ y : E, R < dist o y := by
  classical
  by_contra! h
  have hball : Metric.closedBall o R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    simpa only [Metric.mem_closedBall, dist_comm] using h y
  exact (isCompact_closedBall o R).ne_univ hball

theorem exists_isometric_ray_of_exact_radial
    (hrad : ∀ (x y : E) {r : ℝ}, 0 ≤ r → r ≤ dist x y →
      ∃ z : E, dist x z = r ∧ dist z y = dist x y - r)
    (o : E) :
    ∃ ray : ℝ≥0 → E, ray 0 = o ∧
      ∀ s t, dist (ray s) (ray t) = |(t : ℝ) - (s : ℝ)| := by
  classical
  let K : Set (ℝ≥0 → E) :=
    {f | ∀ t : ℝ≥0, f t ∈ Metric.closedBall o (t : ℝ)}
  have hK : IsCompact K := by
    exact isCompact_pi_infinite (fun t : ℝ≥0 =>
      isCompact_closedBall o (t : ℝ))
  let C : (ℝ≥0 × ℝ≥0) → Set (ℝ≥0 → E) := fun p =>
    {f | dist (f p.1) (f p.2) = |(p.2 : ℝ) - (p.1 : ℝ)|}
  have hC : ∀ p, IsClosed (C p) := by
    intro p
    exact isClosed_eq ((continuous_apply p.1).dist (continuous_apply p.2))
      continuous_const
  have hFIP : ∀ U : Finset (ℝ≥0 × ℝ≥0),
      (K ∩ ⋂ p ∈ U, C p).Nonempty := by
    intro U
    let S : Finset ℝ≥0 := U.image Prod.fst ∪ U.image Prod.snd
    let R : ℝ≥0 := S.sup id
    obtain ⟨y, hy⟩ := exists_dist_gt_of_proper_noncompact o (R : ℝ)
    have hbound : ∀ t ∈ S, (t : ℝ) ≤ dist o y := by
      intro t ht
      have htR : t ≤ R := Finset.le_sup (f := id) ht
      have htR' : (t : ℝ) ≤ (R : ℝ) := by exact_mod_cast htR
      exact htR'.trans hy.le
    obtain ⟨f, hfEnd, hfPair⟩ := finite_radial_interpolation hrad S o y hbound
    let g : ℝ≥0 → E := fun t => if t ∈ S then f t else o
    have hgon : ∀ t ∈ S, g t = f t := by
      intro t ht
      simp [g, ht]
    have hgK : g ∈ K := by
      intro t
      change dist (g t) o ≤ (t : ℝ)
      by_cases ht : t ∈ S
      · calc
          dist (g t) o = dist o (f t) := by rw [hgon t ht, dist_comm]
          _ = (t : ℝ) := (hfEnd t ht).1
          _ ≤ (t : ℝ) := le_rfl
      · have hgo : g t = o := if_neg ht
        rw [hgo, dist_self]
        exact t.property
    refine ⟨g, hgK, ?_⟩
    simp only [Set.mem_iInter]
    intro p hp
    have hp1 : p.1 ∈ S := by
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have hp2 : p.2 ∈ S := by
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    change dist (g p.1) (g p.2) = |(p.2 : ℝ) - (p.1 : ℝ)|
    rw [hgon p.1 hp1, hgon p.2 hp2]
    exact hfPair p.1 hp1 p.2 hp2
  obtain ⟨ray, hRayK, hRayC⟩ := hK.inter_iInter_nonempty C hC hFIP
  refine ⟨ray, ?_, ?_⟩
  · have h0 : dist (ray 0) o ≤ (0 : ℝ) := by
      simpa only [Metric.mem_closedBall, NNReal.coe_zero]
        using hRayK (0 : ℝ≥0)
    exact dist_eq_zero.mp (le_antisymm h0 dist_nonneg)
  · intro s t
    exact Set.mem_iInter.mp hRayC (s, t)

end Yau.NodeProofs.P01Aux

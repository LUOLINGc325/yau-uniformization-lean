import Yau.Proofs.V01FiniteGermSupport
import Yau.Proofs.V01StrictMargin
import Yau.Proofs.V01Cylinder

/-! A finite C² lower test yields a genuine compact strict-contact cylinder.
The reassociation is explicit because the original test has type E × E × ℝ. -/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

def contactAssoc : (CotangentCoord n × ℝ) ≃ₜ
    (ComplexVector n × ComplexVector n × ℝ) :=
  Homeomorph.prodAssoc _ _ _

@[simp] theorem contactAssoc_apply (p : CotangentCoord n × ℝ) :
    contactAssoc p = (p.1.1, p.1.2, p.2) := rfl

/-- All compact-frontier strictness follows from the explicit quadratic
margin, including the case of an empty frontier. -/
theorem exists_strict_quadratic_cylinder
    {f : ComplexVector n × ComplexVector n × ℝ → ℝ}
    {v : ComplexVector n × ComplexVector n × ℝ → EReal}
    (a : ComplexVector n × ComplexVector n × ℝ)
    (hf : ContDiffAt ℝ 2 f a) (hfa : (f a : EReal) = v a)
    (hbelow : ∀ᶠ p in 𝓝 a, (f p : EReal) ≤ v p)
    (D : Set (CotangentCoord n × ℝ)) (hD : D ∈ 𝓝 ((a.1, a.2.1), a.2.2))
    {α : ℝ} (hα : 0 < α) :
    ∃ (r : ℝ) (V : Set (CotangentCoord n × ℝ)), 0 < r ∧ IsOpen V ∧
      let K := closedBall (a.1, a.2.1) r ×ˢ Icc (a.2.2 - r) (a.2.2 + r)
      IsCompact K ∧ ((a.1, a.2.1), a.2.2) ∈ interior K ∧ K ⊆ V ∧ V ⊆ D ∧
      ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
        canonicalQuadraticSupport f a α (contactAssoc p)) V ∧
      (∀ p ∈ K, (canonicalQuadraticSupport f a α (contactAssoc p) : EReal) ≤
        v (contactAssoc p)) ∧
      (∀ p ∈ K, (canonicalQuadraticSupport f a α (contactAssoc p) : EReal) =
        v (contactAssoc p) ↔ p = ((a.1, a.2.1), a.2.2)) ∧
      ∃ gap : ℝ, 0 < gap ∧ ∀ p ∈ frontier K,
        ((canonicalQuadraticSupport f a α (contactAssoc p) + gap : ℝ) : EReal) ≤
          v (contactAssoc p) := by
  let aL : CotangentCoord n × ℝ := ((a.1, a.2.1), a.2.2)
  have hAssoc : Tendsto (contactAssoc (n := n)) (𝓝 aL) (𝓝 a) :=
    contactAssoc.continuous.continuousAt.tendsto
  have hm := hAssoc.eventually (canonicalQuadraticSupport_strict_margin hf hα)
  have hb := hAssoc.eventually hbelow
  obtain ⟨V, hVsub, hVopen, haV⟩  := _root_.mem_nhds_iff.mp ((hm.and hb).and hD)
  have hVD : V ⊆ D := fun p hp => (hVsub hp).2
  obtain ⟨r, hr, hKcompact, haK, hKV⟩ :=
    exists_compact_cylinder_subset_nhds (a.1, a.2.1) a.2.2
      (hVopen.mem_nhds haV)
  let K := closedBall (a.1, a.2.1) r ×ˢ Icc (a.2.2 - r) (a.2.2 + r)
  have hMargin (p) (hp : p ∈ K) :
      canonicalQuadraticSupport f a α (contactAssoc p) +
        (α / 2) * coordinateSquare a (contactAssoc p) ≤ f (contactAssoc p) :=
    (hVsub (hKV hp)).1.1
  have hBelow (p) (hp : p ∈ K) :
      (f (contactAssoc p) : EReal) ≤ v (contactAssoc p) :=
    (hVsub (hKV hp)).1.2
  refine ⟨r, V, hr, hVopen, hKcompact, haK, hKV, hVD, ?_, ?_, ?_, ?_⟩
  · exact ((canonicalQuadraticSupport_contDiff f a α).comp
      (by change ContDiff ℝ ∞ (fun p : CotangentCoord n × ℝ => (p.1.1, p.1.2, p.2)); fun_prop)).contDiffOn
  · intro p hp
    have hn : 0 ≤ (α / 2) * coordinateSquare a (contactAssoc p) :=
      mul_nonneg (half_pos hα).le (coordinateSquare_nonneg _ _)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hMargin p hp])).trans (hBelow p hp)
  · intro p hp
    have htouch := touch_iff_of_quadratic_margin hα
      (canonicalQuadraticSupport_self f a α) hfa (hMargin p hp) (hBelow p hp)
    rw [htouch]
    change contactAssoc p = contactAssoc aL ↔ p = aL
    exact contactAssoc.injective.eq_iff
  · have hFront : IsCompact (frontier K) :=
      hKcompact.of_isClosed_subset isClosed_frontier hKcompact.isClosed.frontier_subset
    have haFront : a ∉ contactAssoc '' frontier K := by
      rintro ⟨p, hp, heq⟩
      have hpEq : p = aL := contactAssoc.injective (by simpa [aL] using heq)
      subst p
      exact hp.2 haK
    obtain ⟨gap, hgap, hgaple⟩ := exists_uniform_quadratic_gap a
      (contactAssoc '' frontier K) (hFront.image contactAssoc.continuous) haFront hα
    refine ⟨gap, hgap, ?_⟩
    intro p hp
    have hpK : p ∈ K := hKcompact.isClosed.frontier_subset hp
    have hg := hgaple (contactAssoc p) (mem_image_of_mem _ hp)
    exact (EReal.coe_le_coe_iff.mpr (by linarith [hMargin p hpK])).trans (hBelow p hpK)

end Yau.Blueprint.V01Proof

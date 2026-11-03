import Yau.LeafProofs.L01ProximalTaylor
import Yau.LeafProofs.L01NullImage
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.Compactness.Lindelof
import spec.CHAIN.LeafObligations

open MeasureTheory Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Shorthand for the literal symmetric-bilinear Peano conclusion. -/
def Peano2At (f : E → ℝ) (x : E) : Prop :=
  ∃ (p : E →L[ℝ] ℝ) (A : E →L[ℝ] E →L[ℝ] ℝ),
    (∀ v w, A v w = A w v) ∧
    (fun y => f y - f x - p (y - x) - (1 / 2) * A (y - x) (y - x))
      =o[𝓝 x] (fun y => ‖y - x‖ ^ 2)

/-- The compact-local Aleksandrov theorem with an explicit outer-null exceptional set. -/
theorem exists_null_bad_second_peano_on_interior
    (K : Set E) (f : E → ℝ)
    (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ConvexOn ℝ K f) (hcont : ContinuousOn f K) :
    ∃ B : Set E, volume B = 0 ∧
      ∀ x, x ∈ interior K → x ∉ B → Peano2At f x := by
  obtain ⟨P, hmem, hstrong, hfirm, hLip⟩ := exists_proximal K f hK hne hc hcont
  have hmin (y z : E) (hz : z ∈ K) : proxCost f y (P y) ≤ proxCost f y z :=
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg _))).trans (hstrong y z hz)
  have hrange := interior_subset_range_prox K f P hK hcont hmem hmin hLip
  obtain ⟨B, hB, hgood⟩ := exists_null_bad_image hLip
  refine ⟨B, hB, ?_⟩
  intro x hx hxB
  obtain ⟨y₀, hy₀⟩ := hrange hx
  have hreg := hgood y₀ (by simpa only [hy₀] using hxB)
  have hjet := second_peano_of_proximal_regular K f P hK hcont hmem hmin hfirm hLip y₀
    (by simpa only [hy₀] using hx) (fderiv ℝ P y₀) hreg.1.hasFDerivAt hreg.2
  simpa only [Peano2At, hy₀] using hjet

/-- Countable localization keeps the expansion along the full neighborhood filter. -/
theorem ae_second_peano_on_open (O : Set E) (f : E → ℝ)
    (hO : IsOpen O) (hf : ConvexOn ℝ O f) :
    ∀ᵐ x ∂((volume : Measure E).restrict O), Peano2At f x := by
  classical
  have hcont : ContinuousOn f O := hf.continuousOn hO
  have hballs (a : O) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (a : E) r ⊆ O := by
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hO a a.property
    exact ⟨R / 2, half_pos hR, (Metric.closedBall_subset_ball (half_lt_self hR)).trans hsub⟩
  choose r hr hsub using hballs
  let U : O → Set E := fun a => Metric.ball (a : E) (r a / 2)
  have hlocal (a : O) : ∃ B : Set E, volume B = 0 ∧
      ∀ x, x ∈ U a → x ∉ B → Peano2At f x := by
    obtain ⟨B, hB, hgood⟩ := exists_null_bad_second_peano_on_interior
      (Metric.closedBall (a : E) (r a)) f (isCompact_closedBall _ _)
      ⟨a, Metric.mem_closedBall_self (hr a).le⟩
      (hf.subset (hsub a) (convex_closedBall _ _)) (hcont.mono (hsub a))
    refine ⟨B, hB, fun x hx hxB => hgood x ?_ hxB⟩
    have hxball : x ∈ Metric.ball (a : E) (r a) :=
      Metric.ball_subset_ball (half_le_self (hr a).le) hx
    exact mem_interior_iff_mem_nhds.mpr
      (mem_of_superset (Metric.isOpen_ball.mem_nhds hxball) Metric.ball_subset_closedBall)
  choose B hB hgood using hlocal
  have hcover : O ⊆ ⋃ a : O, U a := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact Metric.mem_ball_self (half_pos (hr ⟨x, hx⟩))
  obtain ⟨J, hJ, hcoverJ⟩ := (HereditarilyLindelofSpace.isLindelof O).elim_countable_subcover
    U (fun _ => Metric.isOpen_ball) hcover
  let Bad : Set E := ⋃ a ∈ J, B a
  have hBad : volume Bad = 0 := (measure_biUnion_null_iff hJ).mpr fun a _ => hB a
  have haegood : ∀ᵐ x ∂(volume : Measure E), x ∉ Bad := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hBad
  apply (ae_restrict_iff' hO.measurableSet).mpr
  filter_upwards [haegood] with x hxBad hxO
  obtain ⟨a, haJ, hxa⟩ := mem_iUnion₂.mp (hcoverJ hxO)
  exact hgood a x hxa (fun hxBa => hxBad (mem_iUnion₂.mpr ⟨a, haJ, hxBa⟩))

end Yau.LeafProofs.L01Aux

namespace Yau.LeafProofs

/-- Native Aleksandrov theorem, with exactly the original local open-domain statement. -/
theorem l01 : Yau.LeafObligations.L01 := by
  intro m O f hO hf
  by_cases hm : m = 0
  · subst m
    apply Filter.Eventually.of_forall
    intro x
    refine ⟨0, 0, by simp, ?_⟩
    have heq : (fun y => f y - f x - (0 : LeafCandidates.RV 0 →L[ℝ] ℝ) (y - x) -
        (1 / 2) * (0 : LeafCandidates.RV 0 →L[ℝ] LeafCandidates.RV 0 →L[ℝ] ℝ)
          (y - x) (y - x)) = fun _ => (0 : ℝ) := by
      funext y
      have hy : y = x := Subsingleton.elim y x
      simp [hy]
    rw [heq]
    exact isLittleO_zero _ _
  · by_cases hOempty : O = ∅
    · subst O
      simp
    · exact L01Aux.ae_second_peano_on_open O f hO hf

/-- Canonical citation-leaf endpoint. -/
theorem L01 : Yau.LeafObligations.L01 := l01

end Yau.LeafProofs

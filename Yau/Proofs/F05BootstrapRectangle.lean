import Yau.Proofs.F05BootstrapClosedPrimitive

/-! Rectangle calculus: an actual parameter derivative whose spatial
jet is continuous commutes with the actual within spatial derivative.
The argument integrates the supplied derivative and differentiates that
identity, rather than assuming a joint second derivative. -/

open Set Filter MeasureTheory
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem F05_rectangle_spatial_parameter_commute {X : Set E}
    (hX : IsCompact X) (hConv : Convex ℝ X) (hClosure : closure (interior X) = X)
    (hUnique : UniqueDiffOn ℝ X) {l r : ℝ}
    {v w : E → ℝ → V} {A B : E → ℝ → E →L[ℝ] V}
    (hw : ContinuousOn (fun z : E × ℝ => w z.1 z.2) (X ×ˢ Icc l r))
    (hB : ContinuousOn (fun z : E × ℝ => B z.1 z.2) (X ×ˢ Icc l r))
    (hSpatial : ∀ t ∈ Icc l r, ∀ x ∈ X,
      HasFDerivWithinAt (fun y => v y t) (A x t) X x)
    (hWSpatial : ∀ t ∈ Icc l r, ∀ x ∈ X,
      HasFDerivWithinAt (fun y => w y t) (B x t) X x)
    (hParameter : ∀ x ∈ X, ∀ t ∈ Icc l r,
      HasDerivWithinAt (v x) (w x t) (Icc l r) t)
    {x : E} (hx : x ∈ X) {t : ℝ} (ht : t ∈ Icc l r) :
    HasDerivWithinAt (A x) (B x t) (Icc l r) t := by
  have hSub (q : ℝ) (hq : q ∈ Icc l r) : uIcc l q ⊆ Icc l r := by
    rw [uIcc_of_le hq.1]
    exact Icc_subset_Icc_right hq.2
  have hIntegral (q : ℝ) (hq : q ∈ Icc l r) (y : E) (hy : y ∈ X) :
      ∫ a in l..q, w y a = v y q-v y l := by
    have hV : ContinuousOn (v y) (Icc l r) :=
      fun a ha => (hParameter y hy a ha).continuousWithinAt
    have hW : ContinuousOn (w y) (Icc l r) :=
      hw.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hy,ha⟩)
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hq.1
      (hV.mono (Icc_subset_Icc_right hq.2))
    · intro a ha
      exact (hParameter y hy a ⟨ha.1.le,ha.2.le.trans hq.2⟩).hasDerivAt
        (Icc_mem_nhds ha.1 (ha.2.trans_le hq.2))
    · exact (hW.mono (hSub q hq)).intervalIntegrable
  have hDIntegral (q : ℝ) (hq : q ∈ Icc l r) :
      ∫ a in l..q, B x a = A x q-A x l := by
    have hInt := F05_compact_parameter_integral_derivative hX hConv hClosure
      (hw.mono (fun z hz => ⟨hz.1,hSub q hq hz.2⟩))
      (hB.mono (fun z hz => ⟨hz.1,hSub q hq hz.2⟩))
      (fun a ha y hy => hWSpatial a (hSub q hq ha) y hy) hx
    have hV := (hSpatial q hq x hx).sub (hSpatial l ⟨le_rfl,hq.1.trans hq.2⟩ x hx)
    calc
      (∫ a in l..q, B x a) = fderivWithin ℝ (fun y => ∫ a in l..q, w y a) X x :=
        (hInt.fderivWithin (hUnique x hx)).symm
      _ = fderivWithin ℝ (fun y => v y q-v y l) X x :=
        fderivWithin_congr (fun y hy => hIntegral q hq y hy) (hIntegral q hq x hx)
      _ = A x q-A x l := hV.fderivWithin (hUnique x hx)
  have hBC : ContinuousOn (B x) (Icc l r) :=
    hB.comp (continuous_const.prodMk continuous_id).continuousOn (fun a ha => ⟨hx,ha⟩)
  have hEq (q : ℝ) (hq : q ∈ Icc l r) : A x q = A x l+(∫ a in l..q, B x a) := by
    rw [hDIntegral q hq]
    abel
  exact ((F05_closed_primitive_derivative hBC ht).const_add (A x l)).congr_of_mem hEq ht

end Yau.Proofs.F05Aux

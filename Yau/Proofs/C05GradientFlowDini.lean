import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Right upper slope comparison applies to distance functions without assuming differentiability. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.C05GradientFlowAux

def UpperRightSlopeLE (u : ℝ → ℝ) (t d : ℝ) : Prop :=
  ∀ q, d < q → ∀ᶠ z in 𝓝[>] t, slope u t z < q

theorem UpperRightSlopeLE.mono {u : ℝ → ℝ} {t d e : ℝ}
    (h : UpperRightSlopeLE u t d) (hde : d ≤ e) : UpperRightSlopeLE u t e :=
  fun q hq => h q (hde.trans_lt hq)

theorem upperRightSlopeLE_of_upper_support {u v : ℝ → ℝ} {t d : ℝ}
    (h0 : u t = v t) (hu : ∀ᶠ z in 𝓝[>] t, u z ≤ v z)
    (hv : HasDerivAt v d t) : UpperRightSlopeLE u t d := by
  intro q hq
  have hd : HasDerivWithinAt v d (Ioi t) t := hv.hasDerivWithinAt
  filter_upwards [hu, hd.limsup_slope_le' (lt_irrefl t) hq, self_mem_nhdsWithin] with z huz hvz hz
  have hs : slope u t z ≤ slope v t z := by
    rw [slope_def_field, slope_def_field, h0]
    exact div_le_div_of_nonneg_right (sub_le_sub_right huz _) (sub_nonneg.mpr hz.le)
  exact hs.trans_lt hvz

theorem upperRightSlopeLE_linear_comparison (u : ℝ → ℝ) {s T a b : ℝ}
    (ha : 0 < a) (hu : ContinuousOn u (Icc s T))
    (hD : ∀ t ∈ Ico s T, UpperRightSlopeLE u t (b - a * u t))
    {t : ℝ} (ht : t ∈ Icc s T) :
    u t ≤ b / a + Real.exp (-a * (t - s)) * (u s - b / a) := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let C := b / a
  let B : ℝ → ℝ := fun x => C + Real.exp (-a * (x - s)) * (u s - C) + δ
  let B' : ℝ → ℝ := fun x => (-a * Real.exp (-a * (x - s))) * (u s - C)
  have hB (x : ℝ) : HasDerivAt B (B' x) x := by
    have H := (((hasDerivAt_id x).sub_const s).const_mul (-a)).exp.mul_const (u s - C)
    convert (H.const_add C).add_const δ using 1 <;> dsimp [B, B'] <;> ring
  have hCs : a * C = b := by dsimp [C]; field_simp
  have hstart : u s ≤ B s := by dsimp [B]; simp only [sub_self, mul_zero, Real.exp_zero, one_mul]; linarith
  have hbound : ∀ x ∈ Ico s T, u x = B x → b - a * u x < B' x := by
    intro x hx heq
    have he : B' x - (b - a * u x) = a * δ := by
      rw [heq]
      dsimp [B, B']
      nlinarith only [hCs]
    linarith [mul_pos ha hδ]
  exact image_le_of_liminf_slope_right_lt_deriv_boundary hu
    (fun x hx q hq => (hD x hx q hq).frequently) hstart hB hbound ht

theorem upperRightSlopeLE_exponential_decay (u : ℝ → ℝ) {s T a : ℝ}
    (ha : 0 < a) (hu : ContinuousOn u (Icc s T))
    (hD : ∀ t ∈ Ico s T, UpperRightSlopeLE u t (-a * u t))
    {t : ℝ} (ht : t ∈ Icc s T) : u t ≤ Real.exp (-a * (t - s)) * u s := by
  simpa using upperRightSlopeLE_linear_comparison u (b := 0) ha hu
    (fun x hx => by simpa using hD x hx) ht

/-- For trapping it suffices to control the right slope on the positive boundary level. -/
theorem boundary_fence (u : ℝ → ℝ) {s T c : ℝ}
    (hu : ContinuousOn u (Icc s T)) (hs : u s ≤ c)
    (hboundary : ∀ x ∈ Ico s T, u x = c →
      ∃ d : ℝ, d < 0 ∧ UpperRightSlopeLE u x d) :
    ∀ ⦃t⦄, t ∈ Icc s T → u t ≤ c := by
  let A := {x | u x ≤ c} ∩ Icc s T
  have hclosed : IsClosed A := by
    dsimp [A]
    rw [inter_comm]
    exact (hu.prodMk (continuousOn_const (c := c))).preimage_isClosed_of_isClosed
      isClosed_Icc OrderClosedTopology.isClosed_le'
  apply hclosed.Icc_subset_of_forall_exists_gt hs
  rintro x ⟨hxc, hx⟩ y hy
  change u x ≤ c at hxc
  rcases hxc.lt_or_eq with hlt | heq
  · have hnear : ∀ᶠ z in 𝓝[Icc s T] x, u z < c :=
      (hu x (Ico_subset_Icc_self hx)).eventually (Iio_mem_nhds hlt)
    have hright : ∀ᶠ z in 𝓝[>] x, u z < c :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hnear
    obtain ⟨z, hz, hzy⟩ := (hright.and (Ioc_mem_nhdsGT hy)).exists
    exact ⟨z, hz.le, hzy⟩
  · obtain ⟨d, hd, hD⟩ := hboundary x hx heq
    obtain ⟨z, hz, hzy⟩ := ((hD 0 hd).and (Ioc_mem_nhdsGT hy)).exists
    refine ⟨z, ?_, hzy⟩
    rw [slope_def_field] at hz
    have hneg : u z - u x < 0 := by
      simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr hzy.1)).mp hz
    change u z ≤ c
    exact (sub_neg.mp hneg).le.trans_eq heq

end Yau.Proofs.C05GradientFlowAux

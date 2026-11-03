import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-!
# Energy identity for finite-dimensional integral primitives

An integrable Euclidean-valued forcing and its actual interval-integral primitive satisfy
an energy identity at every pair of closed-interval times, including the endpoints.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Yau.LeafProofs.L16Aux

private theorem scalarPrimitive_absolutelyContinuous {T : ℝ} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 T) (a : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ a + ∫ r in 0..t, q r) 0 T := by
  have ha : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ a) 0 T := by
    simpa [AbsolutelyContinuousOnInterval] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ ↦ (0 : ℝ)) _ (nhds 0))
  exact ha.fun_add (hq.absolutelyContinuousOnInterval_intervalIntegral (by simp))

private theorem scalarPrimitive_product_intervalIntegrable {T : ℝ} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 T) (a : ℝ) :
    IntervalIntegrable (fun t ↦ q t * (a + ∫ r in 0..t, q r)) volume 0 T :=
  hq.mul_continuousOn (scalarPrimitive_absolutelyContinuous hq a).continuousOn

private theorem scalarPrimitive_energy {T : ℝ} {q : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 T) (a : ℝ) {s t : ℝ}
    (hs : s ∈ uIcc (0 : ℝ) T) (ht : t ∈ uIcc (0 : ℝ) T) :
    (a + ∫ r in 0..t, q r) ^ 2 - (a + ∫ r in 0..s, q r) ^ 2 =
      2 * ∫ r in s..t, q r * (a + ∫ v in 0..r, q v) := by
  let p : ℝ → ℝ := fun r ↦ a + ∫ v in 0..r, q v
  have hp : AbsolutelyContinuousOnInterval p s t :=
    (scalarPrimitive_absolutelyContinuous hq a).mono (uIcc_subset_uIcc hs ht)
  have hderiv : ∀ᵐ r, r ∈ uIcc (0 : ℝ) T → deriv p r = q r := by
    filter_upwards [hq.ae_hasDerivAt_integral] with r hr hrI
    exact ((hr hrI 0 (by simp)).const_add a).deriv
  have hprod := hp.integral_deriv_mul_eq_sub hp
  have hcongr : (∫ r in s..t, deriv p r * p r + p r * deriv p r) =
      ∫ r in s..t, 2 * (q r * p r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with r hr hrI
    rw [hr (uIcc_subset_uIcc hs ht (uIoc_subset_uIcc hrI))]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at hprod
  simpa only [p, pow_two] using hprod.symm

private theorem finitePrimitive_coordinate {m : ℕ} {T : ℝ}
    {q c : ℝ → EuclideanSpace ℝ (Fin m)} {c0 : EuclideanSpace ℝ (Fin m)}
    (hq : IntervalIntegrable q volume 0 T)
    (hc : ∀ t ∈ uIcc (0 : ℝ) T, c t = c0 + ∫ r in 0..t, q r)
    (i : Fin m) {t : ℝ} (ht : t ∈ uIcc (0 : ℝ) T) :
    c t i = c0 i + ∫ r in 0..t, q r i := by
  rw [hc t ht]
  change c0 i + (∫ r in 0..t, q r) i = c0 i + ∫ r in 0..t, q r i
  congr 1
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i).intervalIntegral_comp_comm
    (hq.mono_set (uIcc_subset_uIcc left_mem_uIcc ht))).symm

private theorem finitePrimitive_coordinate_integrable {m : ℕ} {T : ℝ}
    {q : ℝ → EuclideanSpace ℝ (Fin m)} (hq : IntervalIntegrable q volume 0 T)
    (i : Fin m) : IntervalIntegrable (fun r ↦ q r i) volume 0 T := by
  exact ⟨(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i).integrable_comp hq.1,
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ ℝ) i).integrable_comp hq.2⟩

private theorem finitePrimitive_coordinate_product_integrable {m : ℕ} {T : ℝ}
    {q c : ℝ → EuclideanSpace ℝ (Fin m)} {c0 : EuclideanSpace ℝ (Fin m)}
    (hq : IntervalIntegrable q volume 0 T)
    (hc : ∀ t ∈ uIcc (0 : ℝ) T, c t = c0 + ∫ r in 0..t, q r)
    (i : Fin m) : IntervalIntegrable (fun r ↦ q r i * c r i) volume 0 T := by
  refine (scalarPrimitive_product_intervalIntegrable
    (finitePrimitive_coordinate_integrable hq i) (c0 i)).congr ?_
  intro r hr
  dsimp only
  rw [finitePrimitive_coordinate hq hc i (uIoc_subset_uIcc hr)]

/-- The actual forcing/primitive energy pairing is integrable on every subinterval of the
closed time slab. The forcing is only assumed to be Lebesgue integrable on the open slab. -/
theorem finitePrimitive_energy_pairing_intervalIntegrable {m : ℕ} {T : ℝ}
    (hT : 0 < T) {q c : ℝ → EuclideanSpace ℝ (Fin m)}
    {c0 : EuclideanSpace ℝ (Fin m)}
    (hq : Integrable q (volume.restrict (Ioo 0 T)))
    (hc : ∀ t ∈ Icc 0 T, c t = c0 + ∫ r in 0..t, q r)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun r ↦ inner ℝ (q r) (c r)) volume s t := by
  have hq' : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hq
  have hc' : ∀ r ∈ uIcc (0 : ℝ) T, c r = c0 + ∫ v in 0..r, q v := by
    simpa only [uIcc_of_le hT.le] using hc
  have hi : IntervalIntegrable (fun r ↦ ∑ i : Fin m, q r i * c r i) volume 0 T := by
    simpa only [Finset.sum_fn] using
      IntervalIntegrable.sum Finset.univ
        (fun i _ ↦ finitePrimitive_coordinate_product_integrable hq' hc' i)
  have heq : (fun r ↦ inner ℝ (q r) (c r)) =
      (fun r ↦ ∑ i : Fin m, q r i * c r i) := by
    funext r
    simp [PiLp.inner_apply, mul_comm]
  rw [heq]
  exact hi.mono_set (uIcc_subset_uIcc
    (by simpa only [uIcc_of_le hT.le] using hs)
    (by simpa only [uIcc_of_le hT.le] using ht))

/-- The finite-dimensional energy identity for an actual interval-integral primitive.
It holds at all closed-slab times, in either order, and also in dimension zero. -/
theorem finitePrimitive_energy_identity {m : ℕ} {T : ℝ}
    (hT : 0 < T) {q c : ℝ → EuclideanSpace ℝ (Fin m)}
    {c0 : EuclideanSpace ℝ (Fin m)}
    (hq : Integrable q (volume.restrict (Ioo 0 T)))
    (hc : ∀ t ∈ Icc 0 T, c t = c0 + ∫ r in 0..t, q r)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = 2 * ∫ r in s..t, inner ℝ (q r) (c r) := by
  have hq' : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hq
  have hc' : ∀ r ∈ uIcc (0 : ℝ) T, c r = c0 + ∫ v in 0..r, q v := by
    simpa only [uIcc_of_le hT.le] using hc
  have hs' : s ∈ uIcc (0 : ℝ) T := by simpa only [uIcc_of_le hT.le] using hs
  have ht' : t ∈ uIcc (0 : ℝ) T := by simpa only [uIcc_of_le hT.le] using ht
  have hsub := uIcc_subset_uIcc hs' ht'
  have hcoord (i : Fin m) : (c t i) ^ 2 - (c s i) ^ 2 =
      2 * ∫ r in s..t, q r i * c r i := by
    rw [finitePrimitive_coordinate hq' hc' i ht', finitePrimitive_coordinate hq' hc' i hs']
    rw [scalarPrimitive_energy (finitePrimitive_coordinate_integrable hq' i) (c0 i) hs' ht']
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [finitePrimitive_coordinate hq' hc' i (hsub hr)]
  have hint (i : Fin m) : IntervalIntegrable (fun r ↦ q r i * c r i) volume s t :=
    (finitePrimitive_coordinate_product_integrable hq' hc' i).mono_set hsub
  calc
    ‖c t‖ ^ 2 - ‖c s‖ ^ 2 = ∑ i : Fin m, ((c t i) ^ 2 - (c s i) ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        Finset.sum_sub_distrib]
    _ = ∑ i : Fin m, 2 * ∫ r in s..t, q r i * c r i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcoord i
    _ = 2 * ∫ r in s..t, ∑ i : Fin m, q r i * c r i := by
      rw [intervalIntegral.integral_finsetSum (fun i _ ↦ hint i), Finset.mul_sum]
    _ = 2 * ∫ r in s..t, inner ℝ (q r) (c r) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro r _
      simp [PiLp.inner_apply, mul_comm]

private theorem scalarPrimitive_test_by_parts {T : ℝ} {q η : ℝ → ℝ}
    (hq : IntervalIntegrable q volume 0 T)
    (hη : AbsolutelyContinuousOnInterval η 0 T) (a : ℝ) :
    (∫ r in 0..T, -deriv η r * (a + ∫ v in 0..r, q v)) =
      (∫ r in 0..T, η r * q r) + η 0 * a - η T * (a + ∫ r in 0..T, q r) := by
  let p : ℝ → ℝ := fun r ↦ a + ∫ v in 0..r, q v
  have hp : AbsolutelyContinuousOnInterval p 0 T :=
    scalarPrimitive_absolutelyContinuous hq a
  have hderiv : ∀ᵐ r, r ∈ uIcc (0 : ℝ) T → deriv p r = q r := by
    filter_upwards [hq.ae_hasDerivAt_integral] with r hr hrI
    exact ((hr hrI 0 (by simp)).const_add a).deriv
  have hparts := hη.integral_mul_deriv_eq_deriv_mul hp
  have hcongr : (∫ r in 0..T, η r * deriv p r) = ∫ r in 0..T, η r * q r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with r hr hrI
    rw [hr (uIoc_subset_uIcc hrI)]
  rw [hcongr] at hparts
  change (∫ r in 0..T, -deriv η r * p r) =
    (∫ r in 0..T, η r * q r) + η 0 * a - η T * p T
  simp_rw [neg_mul]
  rw [intervalIntegral.integral_neg, hparts]
  have hp0 : p 0 = a := by simp [p]
  rw [hp0]
  ring

/-- Integration by parts against a scalar `C¹` time test. No endpoint vanishing is assumed:
the initial term is `η 0 * inner ℝ c0 w` and the terminal term is retained as well. -/
theorem finitePrimitive_timeTest_integrationByParts {m : ℕ} {T : ℝ}
    (hT : 0 < T) {q c : ℝ → EuclideanSpace ℝ (Fin m)}
    {c0 : EuclideanSpace ℝ (Fin m)}
    (hq : Integrable q (volume.restrict (Ioo 0 T)))
    (hc : ∀ t ∈ Icc 0 T, c t = c0 + ∫ r in 0..t, q r)
    {η : ℝ → ℝ} (hη : ContDiffOn ℝ 1 η (Icc 0 T)) (w : EuclideanSpace ℝ (Fin m)) :
    (∫ r in 0..T, -deriv η r * inner ℝ (c r) w) =
      (∫ r in 0..T, η r * inner ℝ (q r) w) +
        η 0 * inner ℝ c0 w - η T * inner ℝ (c T) w := by
  let L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := innerSL ℝ w
  have hq' : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr hq
  have hLq : IntervalIntegrable (fun r ↦ L (q r)) volume 0 T :=
    ⟨L.integrable_comp hq'.1, L.integrable_comp hq'.2⟩
  have hLc {r : ℝ} (hr : r ∈ Icc 0 T) :
      inner ℝ (c r) w = L c0 + ∫ v in 0..r, L (q v) := by
    rw [real_inner_comm, hc r hr]
    change L (c0 + ∫ v in 0..r, q v) = _
    rw [L.map_add, L.intervalIntegral_comp_comm
      (hq'.mono_set (uIcc_subset_uIcc left_mem_uIcc
        (by simpa only [uIcc_of_le hT.le] using hr)))]
  have hη' : AbsolutelyContinuousOnInterval η 0 T :=
    (show ContDiffOn ℝ 1 η (uIcc (0 : ℝ) T) by
      simpa only [uIcc_of_le hT.le] using hη).absolutelyContinuousOnInterval
  calc
    (∫ r in 0..T, -deriv η r * inner ℝ (c r) w) =
        ∫ r in 0..T, -deriv η r * (L c0 + ∫ v in 0..r, L (q v)) := by
      apply intervalIntegral.integral_congr
      intro r hr
      dsimp only
      rw [hLc (by simpa only [uIcc_of_le hT.le] using hr)]
    _ = (∫ r in 0..T, η r * L (q r)) +
        η 0 * L c0 - η T * (L c0 + ∫ r in 0..T, L (q r)) :=
      scalarPrimitive_test_by_parts hLq hη' (L c0)
    _ = (∫ r in 0..T, η r * inner ℝ (q r) w) +
        η 0 * inner ℝ c0 w - η T * inner ℝ (c T) w := by
      rw [← hLc ⟨hT.le, le_rfl⟩]
      simp only [L, innerSL_apply_apply, real_inner_comm w]

end Yau.LeafProofs.L16Aux

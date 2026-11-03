import Yau.LeafProofs.L22RegularizedMax

noncomputable section

open scoped Topology ContDiff Convolution
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

/-- A single product-coordinate split integrates out all the complementary
coordinates at once. -/
theorem regularizedMaxProductKernel_marginal {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) (p : κ → Prop) [DecidablePred p]
    (f : (Subtype p → ℝ) → ℝ) :
    (∫ x : κ → ℝ, f (fun i : Subtype p => x i) * regularizedMaxProductKernel δ x) =
      ∫ y : Subtype p → ℝ, f y * regularizedMaxProductKernel (fun i : Subtype p => δ i) y := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => ℝ) p
  have he := volume_preserving_piEquivPiSubtypeProd (fun _ : κ => ℝ) p
  rw [← he.symm.integral_comp']
  have hprod (q : (Subtype p → ℝ) × ({i // ¬p i} → ℝ)) :
      regularizedMaxProductKernel δ (e.symm q) =
        regularizedMaxProductKernel (fun i : Subtype p => δ i) q.1 *
        regularizedMaxProductKernel (fun i : {i // ¬p i} => δ i) q.2 := by
    unfold regularizedMaxProductKernel
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro i _
    · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
    · simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
  have hrestrict (q : (Subtype p → ℝ) × ({i // ¬p i} → ℝ)) :
      (fun i : Subtype p => e.symm q i) = q.1 := by
    ext i
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
  change (∫ q : (Subtype p → ℝ) × ({i // ¬p i} → ℝ),
    f (fun i : Subtype p => e.symm q i) * regularizedMaxProductKernel δ (e.symm q)
      ∂(volume.prod volume)) = _
  simp only [hrestrict, hprod, ← mul_assoc]
  rw [integral_prod_mul
    (fun y : Subtype p → ℝ => f y * regularizedMaxProductKernel (fun i : Subtype p => δ i) y)
    (regularizedMaxProductKernel (fun i : {i // ¬p i} => δ i)),
    regularizedMaxProductKernel_mass, mul_one]

theorem finiteMaximum_reindex {κ η : Type*} [Fintype κ] [Fintype η]
    (e : κ ≃ η) (z : η → ℝ) : finiteMaximum (fun i => z (e i)) = finiteMaximum z := by
  classical
  by_cases h : Nonempty η
  · letI : Nonempty η := h
    letI : Nonempty κ := h.map e.symm
    apply le_antisymm
    · exact finiteMaximum_le _ (fun i => le_finiteMaximum z (e i))
    · exact finiteMaximum_le _ (fun i => by
        simpa only [e.apply_symm_apply] using le_finiteMaximum (fun j => z (e j)) (e.symm i))
  · have hκ : ¬Nonempty κ := fun hn => h (hn.map e)
    simp only [finiteMaximum, dif_neg hκ, dif_neg h]

theorem regularizedMaxCoords_reindex {κ η : Type*} [Fintype κ] [Fintype η]
    (e : κ ≃ η) (δ z : η → ℝ) :
    regularizedMaxCoords (fun i => δ (e i)) (fun i => z (e i)) = regularizedMaxCoords δ z := by
  classical
  have he := volume_measurePreserving_piCongrLeft (fun _ : η => ℝ) e
  unfold regularizedMaxCoords
  rw [← he.integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  have hmax := finiteMaximum_reindex e
    (z + MeasurableEquiv.piCongrLeft (fun _ : η => ℝ) e x)
  have hk := e.prod_comp
    (fun j => regularizedMaxKernel (δ j)
      (MeasurableEquiv.piCongrLeft (fun _ : η => ℝ) e x j))
  simp only [Pi.add_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply, e.symm_apply_apply] at hmax hk
  change finiteMaximum (fun i => z (e i) + x i) *
      (∏ i, regularizedMaxKernel (δ (e i)) (x i)) =
    finiteMaximum (z + MeasurableEquiv.piCongrLeft (fun _ : η => ℝ) e x) *
      (∏ j, regularizedMaxKernel (δ j) (MeasurableEquiv.piCongrLeft (fun _ : η => ℝ) e x j))
  exact congrArg₂ (· * ·) hmax hk

/-- On the product support every discarded coordinate is dominated by a
retained one; all discarded coordinates are then integrated out in one step. -/
theorem regularizedMaxCoords_restrict {κ : Type*} [Fintype κ]
    (δ z : κ → ℝ) (p : κ → Prop) [DecidablePred p]
    (hp : Nonempty (Subtype p)) (hδ : ∀ i, 0 < δ i)
    (hdom : ∀ i, ¬p i → ∃ j : Subtype p, z i + δ i ≤ z j - δ j) :
    regularizedMaxCoords δ z =
      regularizedMaxCoords (fun i : Subtype p => δ i) (fun i : Subtype p => z i) := by
  classical
  letI : Nonempty (Subtype p) := hp
  letI : Nonempty κ := hp.map Subtype.val
  have hmax (x : κ → ℝ) (hx : regularizedMaxProductKernel δ x ≠ 0) :
      finiteMaximum (z + x) = finiteMaximum (fun j : Subtype p => z j + x j) := by
    have hxs (i : κ) : |x i| < δ i :=
      regularizedMaxKernel_support_of_pos (hδ i)
        ((Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i))
    apply le_antisymm
    · apply finiteMaximum_le
      intro i
      by_cases hi : p i
      · exact le_finiteMaximum (fun j : Subtype p => z j + x j) ⟨i, hi⟩
      · obtain ⟨j, hj⟩ := hdom i hi
        have hxi := (abs_lt.mp (hxs i)).2
        have hxj := (abs_lt.mp (hxs j)).1
        have hb : z i + x i ≤ z j + x j := by linarith
        exact hb.trans (le_finiteMaximum (fun j : Subtype p => z j + x j) j)
    · exact finiteMaximum_le _ (fun j => le_finiteMaximum (z + x) j)
  calc
    regularizedMaxCoords δ z = ∫ x : κ → ℝ,
        finiteMaximum (fun j : Subtype p => z j + x j) * regularizedMaxProductKernel δ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : regularizedMaxProductKernel δ x = 0
      · simp only [hx, mul_zero]
      · rw [hmax x hx]
    _ = regularizedMaxCoords (fun i : Subtype p => δ i) (fun i : Subtype p => z i) :=
      regularizedMaxProductKernel_marginal δ p
        (fun y => finiteMaximum ((fun j : Subtype p => z j) + y))

/-- Arbitrary finite restriction, with all removed branches discarded at once.
The ambient index type may be infinite. -/
theorem regularizedMax_restrict {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (ht : t.Nonempty) (hts : t ⊆ s) (δ v : ι → ℝ)
    (hδ : ∀ i ∈ s, 0 < δ i)
    (hdom : ∀ i ∈ s \ t, ∃ j ∈ t, v i + δ i ≤ v j - δ j) :
    regularizedMax s δ v = regularizedMax t δ v := by
  classical
  let p : s → Prop := fun i => (i : ι) ∈ t
  have hp : Nonempty (Subtype p) := by
    obtain ⟨i, hi⟩ := ht
    exact ⟨⟨⟨i, hts hi⟩, hi⟩⟩
  have hd : ∀ i : s, ¬p i →
      ∃ j : Subtype p, v i + δ i ≤ v j.val - δ j.val := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := hdom i (Finset.mem_sdiff.mpr ⟨i.property, hi⟩)
    exact ⟨⟨⟨j, hts hj⟩, hj⟩, hij⟩
  let e : Subtype p ≃ t :=
    { toFun := fun i => ⟨i.val.val, i.property⟩
      invFun := fun j => ⟨⟨j.val, hts j.property⟩, j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold regularizedMax
  rw [regularizedMaxCoords_restrict (fun i : s => δ i) (fun i : s => v i)
    p hp (fun i => hδ i i.property) hd]
  exact regularizedMaxCoords_reindex e (fun i : t => δ i) (fun i : t => v i)

end Yau.LeafProofs.L22Aux

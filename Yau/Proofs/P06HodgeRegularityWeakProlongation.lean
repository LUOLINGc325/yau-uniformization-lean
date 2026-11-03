import Yau.Proofs.P06HodgeRegularityWeakCommutator

/-! Prolongation of the actual local forward weak equation, by packing
independently constructed weak gradients of the value and source. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityProlongE1_contDiff
    (v : ι → E) (q : ι → ι → E → ℝ) (e1 : α → α → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (r c : RegularityProlongIndex α ι) (i : ι) :
    ContDiff ℝ ∞ (regularityProlongE1 v q e1 r c i) := by
  rcases r with ⟨r,sr⟩
  rcases c with ⟨c,sc⟩
  cases sr <;> cases sc
  · exact he1 r c i
  · exact contDiff_const
  · exact contDiff_const
  · unfold regularityProlongE1
    apply ContDiff.sub
    · split_ifs <;> first | exact he1 r c i | exact contDiff_const
    · split_ifs <;> first | exact regularityDirection_contDiff (hq i _) (v _) | exact contDiff_const

theorem regularityProlongE0_contDiff
    (v : ι → E) (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (r c : RegularityProlongIndex α ι) :
    ContDiff ℝ ∞ (regularityProlongE0 v e1 e0 r c) := by
  rcases r with ⟨r,sr⟩
  rcases c with ⟨c,sc⟩
  cases sr <;> cases sc
  · exact he0 r c
  · exact contDiff_const
  · exact regularityDirection_contDiff (he0 r c) (v _)
  · unfold regularityProlongE0
    apply ContDiff.add
    · split_ifs <;> first | exact he0 r c | exact contDiff_const
    · exact regularityDirection_contDiff (he1 r c _) (v _)

theorem regularityProlongWeakValue_memLp
    {O : Set E} (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hG : ∀ j c, MemLp (fun z => G z j c) 2 (ν.restrict O))
    (p : RegularityProlongIndex α ι) :
    MemLp (fun z => regularityProlongWeakValue U G z p) 2 (ν.restrict O) := by
  rcases p with ⟨c,sc⟩
  cases sc with
  | none => exact hU c
  | some j => exact hG j c

theorem regularityProlong_pairing_row
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} (U : E → α → ℝ) (G : E → ι → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hG : ∀ j c, MemLp (fun z => G z j c) 2 (ν.restrict O))
    (hd : ∀ j c, regularityWeakDeriv ν O (v j) (fun z => U z c) (fun z => G z j c))
    {φ : E → ℝ} (hφ : regularityTest O φ) (ell : ι) (r c : α) :
    (∑ sc : Option ι, ∫ z, regularityProlongWeakValue U G z (c,sc) *
      regularityScalarTranspose v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
        φ z (r,some ell) (c,sc) ∂ν.restrict O) =
      -(∫ z, U z c * regularityScalarTranspose v q e1 e0
        (regularityDirection (v ell) φ) z r c ∂ν.restrict O) := by
  have hT := regularityScalarTranspose_test v q e1 e0 hq he1 he0 hφ r c
  have hK j := regularityProlongK_test v q e1 hq he1 hφ ell r c j
  have hsplit (j : ι) :
      (∫ z, G z j c * ((if j = ell then regularityScalarTranspose v q e1 e0 φ z r c else 0) +
        regularityProlongK v q e1 φ ell r c j z) ∂ν.restrict O) =
      (if j = ell then ∫ z, G z j c * regularityScalarTranspose v q e1 e0 φ z r c ∂ν.restrict O else 0) +
        ∫ z, G z j c * regularityProlongK v q e1 φ ell r c j z ∂ν.restrict O := by
    by_cases hj : j = ell
    · simp only [if_pos hj, mul_add]
      exact integral_add ((hG j c).integrable_mul (regularityTest_memLp ν hT))
        ((hG j c).integrable_mul (regularityTest_memLp ν (hK j)))
    · simp only [if_neg hj, zero_add]
  rw [Fintype.sum_option]
  simp_rw [regularityProlongWeakValue_none, regularityProlongWeakValue_some,
    regularityProlongTranspose_some_none, regularityProlongTranspose_some_some v q e1 e0 hq he1 φ hφ.1,
    hsplit]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa only [add_assoc] using regularityWeakTranspose_commutator ν v q e1 e0 hq he1 he0
    (fun z => U z c) (fun j z => G z j c) (hU c) (fun j => hG j c) (fun j => hd j c) hφ ell r c

/-- Natural rough prolongation: first weak gradients are packed as new
components. They are never replaced by classical derivatives of raw fields. -/
theorem regularityForwardWeak_prolong
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} (U W : E → α → ℝ) (G H : E → ι → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hG : ∀ j c, MemLp (fun z => G z j c) 2 (ν.restrict O))
    (hdU : ∀ j c, regularityWeakDeriv ν O (v j) (fun z => U z c) (fun z => G z j c))
    (hdW : ∀ j c, regularityWeakDeriv ν O (v j) (fun z => W z c) (fun z => H z j c))
    (hweak : regularityForwardWeak ν O v q e1 e0 U W) :
    regularityForwardWeak ν O v q (regularityProlongE1 v q e1) (regularityProlongE0 v e1 e0)
      (regularityProlongWeakValue U G) (regularityProlongWeakValue W H) := by
  have hp := (regularityForwardWeak_pairing_iff ν v q e1 e0 hq he1 he0 U W hU).mp hweak
  apply (regularityForwardWeak_pairing_iff ν v q _ _ hq
    (regularityProlongE1_contDiff v q e1 hq he1)
    (regularityProlongE0_contDiff v e1 e0 he1 he0) _ _
    (regularityProlongWeakValue_memLp ν U G hU hG)).mpr
  rintro ⟨r,sr⟩ φ hφ
  rw [Fintype.sum_prod_type]
  cases sr with
  | none =>
    simp only [Fintype.sum_option, regularityProlongTranspose_none_none,
      regularityProlongTranspose_none_some, regularityProlongWeakValue_none,
      mul_zero, integral_zero, Finset.sum_const_zero, add_zero]
    exact hp r φ hφ
  | some ell =>
    simp_rw [regularityProlong_pairing_row ν v q e1 e0 hq he1 he0 U G hU hG hdU hφ ell r]
    rw [Finset.sum_neg_distrib, hp r (regularityDirection (v ell) φ) (regularityTest_direction hφ (v ell))]
    have hh := hdW ell r φ hφ
    change -(∫ z, W z r * fderiv ℝ φ z (v ell) ∂ν.restrict O) =
      ∫ z, H z ell r * φ z ∂ν.restrict O
    linarith

end Yau.NodeProofs.P06Aux

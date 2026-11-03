import Yau.LeafProofs.L16CompactCoefficientBounds
import Yau.LeafProofs.L16ExpLogTransform

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

/-- Local Taylor derivative fields on a compact set control the actual second
derivative on its open interior. No boundary value of the ambient derivative
is asserted or used. -/
theorem bounded_secondFDeriv_on_open_subset_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {g : E → F}
    (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K)
    (hg : ContDiffOn ℝ 2 g K) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ U, ‖fderiv ℝ (fderiv ℝ g) p‖ ≤ A := by
  classical
  have hLocal (x : K) : ∃ V : Set E, IsOpen V ∧ (x : E) ∈ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ V, y ∈ U → ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ C := by
    obtain ⟨u, hu, hus, han, g', hder, hcont⟩ :=
      (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (𝕜 := ℝ) (n := 1) (by simp)).mp
        (by convert hg x x.property using 1 <;> norm_num)
    rw [insert_eq_of_mem x.property] at hu
    obtain ⟨v, hv, hvs, hvan, g'', hder', hcont'⟩ :=
      (contDiffWithinAt_succ_iff_hasFDerivWithinAt' (𝕜 := ℝ) (n := 0) (by simp)).mp
        (by simpa using hcont)
    rw [insert_eq_of_mem x.property] at hv
    have hnorm : ∀ᶠ y in 𝓝[K] (x : E), ‖g'' y‖ < ‖g'' x‖+1 :=
      hcont'.continuousWithinAt.norm.eventually (gt_mem_nhds (lt_add_one ‖g'' x‖))
    obtain ⟨V, hV, hxV, hVu⟩ := mem_nhdsWithin.mp (inter_mem hu (inter_mem hv hnorm))
    refine ⟨V,hV,hxV,‖g'' x‖+1,by positivity,?_⟩
    intro y hyV hyU
    have hy := hVu ⟨hyV,hUK hyU⟩
    have hEq : fderiv ℝ g =ᶠ[𝓝 y] g' := by
      filter_upwards [hV.mem_nhds hyV,hU.mem_nhds hyU] with z hzV hzU
      exact ((hder z (hVu ⟨hzV,hUK hzU⟩).1).hasFDerivAt
        (Filter.mem_of_superset (hU.mem_nhds hzU) hUK)).fderiv
    rw [hEq.fderiv_eq, ((hder' y hy.2.1).hasFDerivAt
      (Filter.mem_of_superset (hU.mem_nhds hyU) hUK)).fderiv]
    exact hy.2.2.le
  choose V hV hxV C hC hBound using hLocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hsum : 0 ≤ ∑ x ∈ s, C x := Finset.sum_nonneg (fun x _ => (hC x).le)
  refine ⟨1+∑ x ∈ s, C x,by linarith,?_⟩
  intro p hp
  obtain ⟨x,hxs,hpx⟩ := mem_iUnion₂.mp (hs (hUK hp))
  have hle : C x ≤ ∑ y ∈ s, C y :=
    Finset.single_le_sum (fun y _ => (hC y).le) hxs
  exact (hBound x p hpx hp).trans (by linarith)

/-- Every fixed smooth datum has bounded actual interior jets of order at most
two; all three constants are chosen before any candidate solution. -/
theorem compact_fixed_data_bounds {n : ℕ} {O : Set (Space n)}
    (hO : SmoothDomain O) {T : ℝ} {P : Point n → ℝ}
    (hP : ContDiffOn ℝ ∞ P (cylinder (closure O) 0 T)) :
    ∃ P₀ P₁ P₂ : ℝ, 0 < P₀ ∧ 0 < P₁ ∧ 0 < P₂ ∧
      (∀ z ∈ cylinder (closure O) 0 T, |P z| ≤ P₀) ∧
      (∀ z ∈ O ×ˢ Ioo 0 T, ‖fderiv ℝ P z‖ ≤ P₁) ∧
      ∀ z ∈ O ×ˢ Ioo 0 T, ‖fderiv ℝ (fderiv ℝ P) z‖ ≤ P₂ := by
  have hK : IsCompact (cylinder (closure O) 0 T) := hO.2.2.1.prod isCompact_Icc
  have hU : IsOpen (O ×ˢ Ioo 0 T) := hO.1.prod isOpen_Ioo
  have hUK : O ×ˢ Ioo 0 T ⊆ cylinder (closure O) 0 T := by
    intro z hz
    exact ⟨subset_closure hz.1,Ioo_subset_Icc_self hz.2⟩
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hP.continuousOn
  obtain ⟨P₁,hP₁,hFirst⟩ := L16Aux.bounded_fderiv_on_open_subset_of_compact
    hK hU hUK (hP.of_le (by simp))
  obtain ⟨P₂,hP₂,hSecond⟩ := bounded_secondFDeriv_on_open_subset_of_compact
    hK hU hUK (hP.of_le (by simp))
  refine ⟨1+|C|,P₁,P₂,by positivity,hP₁,hP₂,?_,hFirst,hSecond⟩
  intro z hz
  have hzC : |P z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
  exact hzC.trans (by linarith [le_abs_self C])

/-- The fixed clipped logarithm is smooth on the closed cylinder, even when
the prescribed extension takes nonpositive values in its interior. -/
theorem fixed_log_data {n : ℕ} {O : Set (Space n)} (hO : SmoothDomain O)
    {T m B : ℝ} (hm : 0 < m) (hmB : m ≤ B) {p : Point n → ℝ}
    (hp : ContDiffOn ℝ ∞ p (cylinder (closure O) 0 T)) :
    ∃ ℓ : ℝ → ℝ, ContDiff ℝ ∞ ℓ ∧ HasCompactSupport ℓ ∧
      EqOn ℓ Real.log (Ioo (m/2) (B+1)) ∧
      ContDiffOn ℝ ∞ (fun z => ℓ (p z)) (cylinder (closure O) 0 T) ∧
      ∃ P₀ P₁ P₂ : ℝ, 0 < P₀ ∧ 0 < P₁ ∧ 0 < P₂ ∧
        (∀ z ∈ cylinder (closure O) 0 T, |ℓ (p z)| ≤ P₀) ∧
        (∀ z ∈ O ×ˢ Ioo 0 T, ‖fderiv ℝ (fun z => ℓ (p z)) z‖ ≤ P₁) ∧
        ∀ z ∈ O ×ˢ Ioo 0 T,
          ‖fderiv ℝ (fderiv ℝ (fun z => ℓ (p z))) z‖ ≤ P₂ := by
  obtain ⟨ℓ,hℓ,hcompact,heq,hgerm⟩ := L16Log.exists_smooth_log_transform hm hmB
  have hP := hℓ.comp_contDiffOn hp
  exact ⟨ℓ,hℓ,hcompact,heq,hP,compact_fixed_data_bounds hO hP⟩

end Yau.LeafProofs.L16ExpBoundaryAux

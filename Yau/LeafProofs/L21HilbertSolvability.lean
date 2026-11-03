import Yau.Analysis.RangeRiesz

/-! Closed Hilbert complexes: projection to the closed-source space and a
range Riesz argument give an actual small solution, without closed range as
an input. -/

open scoped InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {H₀ H₁ H₂ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- A closed densely defined operator is determined by its adjoint pairing.
The proof uses the double orthogonal of its actual closed graph. -/
theorem closed_operator_mem_graph_of_adjoint_identity
    (T : H₀ →ₗ.[ℂ] H₁) (hTdense : Dense (T.domain : Set H₀)) (hTclosed : T.IsClosed)
    (u : H₀) (f : H₁)
    (hp : ∀ v : T.adjoint.domain, inner ℂ u (T.adjoint v) = inner ℂ f (v : H₁)) :
    ∃ x : T.domain, (x : H₀) = u ∧ T x = f := by
  let e := WithLp.linearEquiv 2 ℂ (H₀ × H₁)
  let G : Submodule ℂ (WithLp 2 (H₀ × H₁)) := T.graph.comap e.toLinearMap
  have hG : IsClosed (G : Set (WithLp 2 (H₀ × H₁))) :=
    hTclosed.preimage (WithLp.homeomorphProd 2 H₀ H₁).continuous
  have hGG : Gᗮᗮ = G := by
    rw [G.orthogonal_orthogonal_eq_closure, hG.submodule_topologicalClosure_eq]
  have hmem : WithLp.toLp 2 (u, f) ∈ G := by
    rw [← hGG]
    intro w hw
    let a : H₀ := (WithLp.ofLp w).1
    let b : H₁ := (WithLp.ofLp w).2
    have hb (x : T.domain) : inner ℂ (-a) (x : H₀) = inner ℂ b (T x) := by
      have hx : WithLp.toLp 2 ((x : H₀), T x) ∈ G := T.mem_graph x
      have hh := inner_eq_zero_symm.mp (hw _ hx)
      have hh' : inner ℂ a (x : H₀) + inner ℂ b (T x) = 0 := by
        simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp] using hh
      rw [inner_neg_left]
      apply sub_eq_zero.mp
      have hz := congrArg Neg.neg hh'
      convert hz using 1 <;> abel
    have hbadj : b ∈ T.adjoint.domain :=
      T.mem_adjoint_domain_of_exists b ⟨-a, hb⟩
    have hbadj_eq : T.adjoint ⟨b, hbadj⟩ = -a :=
      T.adjoint_apply_eq hTdense _ hb
    have hh := hp ⟨b, hbadj⟩
    rw [hbadj_eq, inner_neg_right] at hh
    have hc := congrArg (starRingEnd ℂ) hh
    simp only [map_neg, inner_conj_symm] at hc
    change inner ℂ a u + inner ℂ b f = 0
    have hz := congrArg Neg.neg (sub_eq_zero.mpr hc)
    convert hz using 1 <;> abel
  exact T.mem_graph_iff.mp hmem

theorem closed_operator_kernel_isClosed (S : H₁ →ₗ.[ℂ] H₂) (hS : S.IsClosed) :
    IsClosed (S.ker : Set H₁) := by
  have he : (S.ker : Set H₁) = (fun y : H₁ => (y, (0 : H₂))) ⁻¹' (S.graph : Set (H₁ × H₂)) := by
    ext y
    change y ∈ S.ker ↔ (y, 0) ∈ S.graph
    rw [LinearPMap.mem_ker_iff, LinearPMap.mem_graph_iff]
    constructor <;> rintro ⟨x, hx, hzero⟩ <;> exact ⟨x, hx.symm, hzero⟩
  rw [he]
  exact hS.preimage (continuous_id.prodMk continuous_const)

theorem adjoint_project_subspace
    (T : H₀ →ₗ.[ℂ] H₁) (hTdense : Dense (T.domain : Set H₀))
    (K : Submodule ℂ H₁) [K.HasOrthogonalProjection]
    (hRan : ∀ x : T.domain, T x ∈ K) (v : T.adjoint.domain) :
    ∃ hv : (K.orthogonalProjectionOnto (v : H₁) : H₁) ∈ T.adjoint.domain,
      T.adjoint ⟨K.orthogonalProjectionOnto (v : H₁), hv⟩ = T.adjoint v := by
  have hb (x : T.domain) :
      inner ℂ (T.adjoint v) (x : H₀) =
        inner ℂ (K.orthogonalProjectionOnto (v : H₁) : H₁) (T x) := by
    rw [LinearPMap.adjoint_isFormalAdjoint hTdense v x]
    exact (K.inner_orthogonalProjectionOnto_eq_of_mem_right ⟨T x, hRan x⟩ (v : H₁)).symm
  have hv := T.mem_adjoint_domain_of_exists
    (K.orthogonalProjectionOnto (v : H₁)) ⟨T.adjoint v, hb⟩
  exact ⟨hv, T.adjoint_apply_eq hTdense _ hb⟩

/-- The closed Hilbert-complex solvability theorem with constant one. All
operator domains are actual submodules; the conclusion is an actual element
of the first operator's domain. -/
theorem exists_solution_of_hilbert_complex
    (T : H₀ →ₗ.[ℂ] H₁) (S : H₁ →ₗ.[ℂ] H₂)
    (hTdense : Dense (T.domain : Set H₀)) (hTclosed : T.IsClosed) (hSclosed : S.IsClosed)
    (hRan : ∀ x : T.domain, T x ∈ S.ker)
    (hcoerce : ∀ v : T.adjoint.domain, ∀ hs : (v : H₁) ∈ S.domain,
      ‖(v : H₁)‖ ^ 2 ≤ ‖T.adjoint v‖ ^ 2 + ‖S ⟨(v : H₁), hs⟩‖ ^ 2)
    (f : H₁) (hf : f ∈ S.ker) :
    ∃ x : T.domain, T x = f ∧ ‖(x : H₀)‖ ≤ ‖f‖ := by
  let K := S.ker
  letI : CompleteSpace K := (closed_operator_kernel_isClosed S hSclosed).completeSpace_coe
  have hbound (v : T.adjoint.domain) : ‖inner ℂ f (v : H₁)‖ ≤ ‖f‖ * ‖T.adjoint v‖ := by
    obtain ⟨hvp, hpAdj⟩ := adjoint_project_subspace T hTdense K hRan v
    let w : T.adjoint.domain := ⟨K.orthogonalProjectionOnto (v : H₁), hvp⟩
    have hwK : (w : H₁) ∈ S.ker := (K.orthogonalProjectionOnto (v : H₁)).property
    obtain ⟨sx, hxs, hsx⟩ := LinearPMap.mem_ker_iff.mp hwK
    have hSin : (w : H₁) ∈ S.domain := by rw [hxs]; exact sx.property
    have hSzero : S ⟨(w : H₁), hSin⟩ = 0 :=
      (congrArg S (Subtype.ext hxs)).trans hsx
    have hnorm := hcoerce w hSin
    rw [hSzero, norm_zero, zero_pow (by omega), add_zero] at hnorm
    change ‖(K.orthogonalProjectionOnto (v : H₁) : H₁)‖ ^ 2 ≤ ‖T.adjoint w‖ ^ 2 at hnorm
    rw [hpAdj] at hnorm
    have hnorm1 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm
    have hfproj : inner ℂ f (v : H₁) =
        inner ℂ f (K.orthogonalProjectionOnto (v : H₁) : H₁) :=
      (K.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨f, hf⟩ (v : H₁)).symm
    rw [hfproj]
    exact (norm_inner_le_norm f _).trans (mul_le_mul_of_nonneg_left hnorm1 (norm_nonneg f))
  let ell : T.adjoint.domain →ₗ[ℂ] ℂ :=
    (innerSL ℂ f).toLinearMap.comp T.adjoint.domain.subtype
  obtain ⟨u, hu, hpair⟩ := Yau.Analysis.exists_norm_le_inner_eq_of_range_bound
    T.adjoint.toFun ell ‖f‖ (norm_nonneg f) hbound
  obtain ⟨x, hxu, hxf⟩ := closed_operator_mem_graph_of_adjoint_identity
    T hTdense hTclosed u f hpair
  exact ⟨x, hxf, by rw [hxu]; exact hu⟩

end Yau.LeafProofs.L21Aux

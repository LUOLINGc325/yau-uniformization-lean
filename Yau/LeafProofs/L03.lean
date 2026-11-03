import spec.CHAIN.LeafObligations
import Yau.LeafProofs.L12
import Yau.LeafProofs.L18
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Internal operator lemmas for the three components of `LeafObligations.L03`.
The geometric minimal/maximal graph equalities are separate obligations.
-/

open MeasureTheory Filter Module
open scoped Topology InnerProductSpace ComplexConjugate ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A densely defined symmetric operator has a closed extension, its adjoint. -/
theorem symmetric_isClosable (D : H →ₗ.[ℂ] H)
    (hd : Dense (D.domain : Set H)) (hs : D.IsFormalAdjoint D) : D.IsClosable :=
  (D.adjoint_isClosed hd).isClosable.leIsClosable (hs.le_adjoint hd)

/-- Taking graph closure preserves containment in a closed operator. -/
theorem closure_le_of_isClosed {D T : H →ₗ.[ℂ] H} (hc : D.IsClosable)
    (hT : T.IsClosed) (hDT : D ≤ T) : D.closure ≤ T := by
  apply LinearPMap.le_of_le_graph
  rw [← hc.graph_closure_eq_closure_graph]
  exact D.graph.topologicalClosure_minimal (LinearPMap.le_graph_of_le hDT) hT

/-- The formal-adjoint identity is preserved by closure of its first graph. -/
theorem formalAdjoint_closure_left {D T : H →ₗ.[ℂ] H}
    (hc : D.IsClosable) (hs : D.IsFormalAdjoint T) : D.closure.IsFormalAdjoint T := by
  intro x y
  have hclosed : IsClosed {p : H × H |
      inner ℂ p.2 (y : H) = inner ℂ p.1 (T y)} := by
    exact isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const)
  have hsub : (D.graph : Set (H × H)) ⊆
      {p : H × H | inner ℂ p.2 (y : H) = inner ℂ p.1 (T y)} := by
    rintro p hp
    rcases D.mem_graph_iff.mp hp with ⟨v, hv, hw⟩
    change inner ℂ p.2 (y : H) = inner ℂ p.1 (T y)
    rw [← hv, ← hw]
    exact hs v y
  have hx : ((x : H), D.closure x) ∈ closure (D.graph : Set (H × H)) := by
    rw [← D.graph.topologicalClosure_coe, hc.graph_closure_eq_closure_graph]
    exact D.closure.mem_graph x
  exact (closure_minimal hsub hclosed) hx

/-- In particular, the closure of a densely defined symmetric operator is symmetric. -/
theorem symmetric_closure {D : H →ₗ.[ℂ] H} (hc : D.IsClosable)
    (hs : D.IsFormalAdjoint D) : D.closure.IsFormalAdjoint D.closure :=
  (formalAdjoint_closure_left hc (formalAdjoint_closure_left hc hs).symm).symm

/-- Graph-factorization of a square supplies its domain containment. -/
theorem square_domain_le {D A : H →ₗ.[ℂ] H}
    (hsq : OperatorCandidates.SquareGraph D A) : A.domain ≤ D.domain := by
  intro x hx
  obtain ⟨v, hv, _⟩ := (hsq x (A ⟨x, hx⟩)).mp (A.mem_graph ⟨x, hx⟩)
  exact LinearPMap.mem_domain_of_mem_graph hv

/-- The value of a symmetric square has a nonnegative quadratic form. -/
theorem square_nonnegative {D A : H →ₗ.[ℂ] H} (hs : D.IsFormalAdjoint D)
    (hsq : OperatorCandidates.SquareGraph D A) (u : A.domain) :
    0 ≤ (inner ℂ (u : H) (A u)).re := by
  obtain ⟨v, hv, hw⟩ := (hsq (u : H) (A u)).mp (A.mem_graph u)
  obtain ⟨x, hxv, hDx⟩ := D.mem_graph_iff.mp hv
  obtain ⟨y, hyv, hDy⟩ := D.mem_graph_iff.mp hw
  change (x : H) = (u : H) at hxv
  change D x = v at hDx
  change (y : H) = v at hyv
  change D y = A u at hDy
  have heq : inner ℂ (u : H) (A u) = inner ℂ v v := by
    rw [← hxv, ← hDy, ← hs x y, hDx, hyv]
  rw [heq]
  exact inner_self_nonneg (𝕜 := ℂ)

/-- The same formal-adjoint identity, expressed using two graph elements. -/
theorem formalAdjoint_graph {D T : H →ₗ.[ℂ] H} (hs : D.IsFormalAdjoint T)
    {u v x y : H} (huv : (u, v) ∈ D.graph) (hxy : (x, y) ∈ T.graph) :
    inner ℂ v x = inner ℂ u y := by
  rcases D.mem_graph_iff.mp huv with ⟨a, ha, hb⟩
  rcases T.mem_graph_iff.mp hxy with ⟨b, hc, hd⟩
  change (a : H) = u at ha
  change D a = v at hb
  change (b : H) = x at hc
  change T b = y at hd
  rw [← ha, ← hb, ← hc, ← hd]
  exact hs a b

/-- Positivity of the quadratic form passes to graph closure. -/
theorem nonnegative_closure {A : H →ₗ.[ℂ] H} (hc : A.IsClosable)
    (hn : ∀ u : A.domain, 0 ≤ (inner ℂ (u : H) (A u)).re)
    (u : A.closure.domain) : 0 ≤ (inner ℂ (u : H) (A.closure u)).re := by
  have hclosed : IsClosed {p : H × H | 0 ≤ (inner ℂ p.1 p.2).re} :=
    isClosed_le continuous_const (Complex.continuous_re.comp
      (continuous_fst.inner continuous_snd))
  have hsub : (A.graph : Set (H × H)) ⊆
      {p : H × H | 0 ≤ (inner ℂ p.1 p.2).re} := by
    intro p hp
    rcases A.mem_graph_iff.mp hp with ⟨v, hv, hw⟩
    change 0 ≤ (inner ℂ p.1 p.2).re
    rw [← hv, ← hw]
    exact hn v
  have hu : ((u : H), A.closure u) ∈ closure (A.graph : Set (H × H)) := by
    rw [← A.graph.topologicalClosure_coe, hc.graph_closure_eq_closure_graph]
    exact A.closure.mem_graph u
  exact closure_minimal hsub hclosed hu

/-- When the closure is self-adjoint, every adjoint graph element is in that closure. -/
theorem adjoint_le_closure_of_selfAdjoint_closure {A : H →ₗ.[ℂ] H}
    (hd : Dense (A.domain : Set H)) (hc : A.IsClosable)
    (hsa : IsSelfAdjoint A.closure) : A.adjoint ≤ A.closure := by
  have h := (formalAdjoint_closure_left hc (A.adjoint_isFormalAdjoint hd).symm).symm
  have hle := h.symm.le_adjoint hsa.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hsa] at hle

/-- An adjoint eigenvector of D is an adjoint eigenvector of its computed square. -/
theorem square_adjoint_eigenvector {D A : H →ₗ.[ℂ] H}
    (hd : Dense (D.domain : Set H)) (ha : Dense (A.domain : Set H))
    (hsq : OperatorCandidates.SquareGraph D A)
    (u : D.adjoint.domain) (c : ℂ) (hu : D.adjoint u = c • (u : H)) :
    ∃ v : A.adjoint.domain, (v : H) = (u : H) ∧
      A.adjoint v = (c * c) • (u : H) := by
  have heq (x : A.domain) :
      inner ℂ ((c * c) • (u : H)) (x : H) = inner ℂ (u : H) (A x) := by
    obtain ⟨y, hxy, hyz⟩ := (hsq (x : H) (A x)).mp (A.mem_graph x)
    have h1 := formalAdjoint_graph (D.adjoint_isFormalAdjoint hd)
      (D.adjoint.mem_graph u) hxy
    have h2 := formalAdjoint_graph (D.adjoint_isFormalAdjoint hd)
      (D.adjoint.mem_graph u) hyz
    rw [hu] at h1 h2
    rw [inner_smul_left] at h1 h2
    rw [inner_smul_left, map_mul, mul_assoc, h1, h2]
  have hmem : (u : H) ∈ A.adjoint.domain :=
    A.mem_adjoint_domain_of_exists _ ⟨(c * c) • (u : H), heq⟩
  exact ⟨⟨(u : H), hmem⟩, rfl, LinearPMap.adjoint_apply_eq ha _ heq⟩

/-- The square's self-adjoint closure rules out both imaginary deficiency spaces. -/
theorem square_deficiency_eq_zero {D A : H →ₗ.[ℂ] H}
    (hd : Dense (D.domain : Set H)) (hs : D.IsFormalAdjoint D)
    (hsq : OperatorCandidates.SquareGraph D A)
    (ha : Dense (A.domain : Set H)) (hc : A.IsClosable)
    (hsa : IsSelfAdjoint A.closure)
    (u : D.adjoint.domain) (c : ℂ) (hc2 : c * c = -1)
    (hu : D.adjoint u = c • (u : H)) : (u : H) = 0 := by
  obtain ⟨v, hv, hAv⟩ := square_adjoint_eigenvector hd ha hsq u c hu
  have hle := adjoint_le_closure_of_selfAdjoint_closure ha hc hsa
  let w : A.closure.domain := ⟨(v : H), hle.1 v.prop⟩
  have hw : A.closure w = -(u : H) := by
    rw [← hle.2 (show (v : H) = (w : H) from rfl), hAv, hc2, neg_one_smul]
  have hn := nonnegative_closure hc (square_nonnegative hs hsq) w
  change 0 ≤ (inner ℂ (v : H) (A.closure w)).re at hn
  rw [hv, hw, inner_neg_right, Complex.neg_re] at hn
  apply (re_inner_self_nonpos (𝕜 := ℂ)).mp
  change (inner ℂ (u : H) (u : H)).re ≤ 0
  linarith

/-- The resolvent shift on the closed graph, equipped with its induced product norm. -/
def shiftedGraphMap (D : H →ₗ.[ℂ] H) (c : ℂ) : D.graph →L[ℂ] H :=
  (ContinuousLinearMap.snd ℂ H H).comp D.graph.subtypeL +
    c • (ContinuousLinearMap.fst ℂ H H).comp D.graph.subtypeL

theorem shiftedGraphMap_apply (D : H →ₗ.[ℂ] H) (c : ℂ) (p : D.graph) :
    shiftedGraphMap D c p = (p : H × H).2 + c • (p : H × H).1 := rfl

/-- Symmetry cancels the cross term for a purely imaginary unit shift. -/
theorem shiftedGraphMap_norm_sq {D : H →ₗ.[ℂ] H} (hs : D.IsFormalAdjoint D)
    (c : ℂ) (hcre : c.re = 0) (hcn : ‖c‖ = 1) (p : D.graph) :
    ‖shiftedGraphMap D c p‖ ^ 2 = ‖(p : H × H).2‖ ^ 2 + ‖(p : H × H).1‖ ^ 2 := by
  have hs' := formalAdjoint_graph hs p.prop p.prop
  have him : (inner ℂ (p : H × H).2 (p : H × H).1).im = 0 := by
    have h := congrArg Complex.im hs'
    have hi := inner_im_symm (𝕜 := ℂ) (p : H × H).2 (p : H × H).1
    change (inner ℂ (p : H × H).2 (p : H × H).1).im =
      -(inner ℂ (p : H × H).1 (p : H × H).2).im at hi
    linarith
  rw [shiftedGraphMap_apply, norm_add_sq (𝕜 := ℂ), inner_smul_right]
  change ‖(p : H × H).2‖ ^ 2 +
      2 * (c * inner ℂ (p : H × H).2 (p : H × H).1).re +
      ‖c • (p : H × H).1‖ ^ 2 = _
  simp [Complex.mul_re, hcre, him, norm_smul, hcn]

/-- This shift is bounded below in the graph norm. -/
theorem shiftedGraphMap_antilipschitz {D : H →ₗ.[ℂ] H} (hs : D.IsFormalAdjoint D)
    (c : ℂ) (hcre : c.re = 0) (hcn : ‖c‖ = 1) :
    AntilipschitzWith 1 (shiftedGraphMap D c) := by
  apply (shiftedGraphMap D c).antilipschitz_of_bound
  intro p
  have h := shiftedGraphMap_norm_sq hs c hcre hcn p
  have h1 : ‖(p : H × H).1‖ ≤ ‖shiftedGraphMap D c p‖ := by nlinarith [norm_nonneg (shiftedGraphMap D c p), norm_nonneg (p : H × H).1, sq_nonneg ‖(p : H × H).2‖]
  have h2 : ‖(p : H × H).2‖ ≤ ‖shiftedGraphMap D c p‖ := by nlinarith [norm_nonneg (shiftedGraphMap D c p), norm_nonneg (p : H × H).2, sq_nonneg ‖(p : H × H).1‖]
  change max ‖(p : H × H).1‖ ‖(p : H × H).2‖ ≤ 1 * _
  simpa using max_le h1 h2

/-- A closed symmetric operator has closed ranges at the imaginary unit shifts. -/
theorem shiftedGraphMap_isClosed_range {D : H →ₗ.[ℂ] H} (hs : D.IsFormalAdjoint D)
    (hclosed : D.IsClosed) (c : ℂ) (hcre : c.re = 0) (hcn : ‖c‖ = 1) :
    IsClosed (Set.range (shiftedGraphMap D c)) := by
  letI : IsClosed (D.graph : Set (H × H)) := hclosed
  exact (shiftedGraphMap_antilipschitz hs c hcre hcn).isClosed_range
    (shiftedGraphMap D c).uniformContinuous

/-- Reversing a densely defined operator inclusion reverses the adjoint inclusion. -/
theorem adjoint_antitone {D C : H →ₗ.[ℂ] H}
    (hd : Dense (D.domain : Set H)) (hC : Dense (C.domain : Set H))
    (hDC : D ≤ C) : C.adjoint ≤ D.adjoint := by
  have hf : C.adjoint.IsFormalAdjoint D := by
    intro x y
    let z : C.domain := ⟨(y : H), hDC.1 y.prop⟩
    have hz : C z = D y := (hDC.2 (show (y : H) = (z : H) from rfl)).symm
    simpa only [hz] using C.adjoint_isFormalAdjoint hC x z
  exact hf.symm.le_adjoint hd

/-- Vanishing of the matching adjoint deficiency space makes the closed shift onto. -/
theorem shiftedGraphMap_surjective_of_deficiency {D C : H →ₗ.[ℂ] H}
    (hd : Dense (D.domain : Set H)) (hDC : D ≤ C)
    (hsC : C.IsFormalAdjoint C) (hclosed : C.IsClosed)
    (c : ℂ) (hcre : c.re = 0) (hcn : ‖c‖ = 1)
    (hdef : ∀ u : D.adjoint.domain,
      D.adjoint u = c • (u : H) → (u : H) = 0) :
    Function.Surjective (shiftedGraphMap C c) := by
  let K : Submodule ℂ H := (shiftedGraphMap C c).range
  have hKclosed : IsClosed (K : Set H) :=
    shiftedGraphMap_isClosed_range hsC hclosed c hcre hcn
  letI : IsClosed (K : Set H) := hKclosed
  have hconj : star c = -c := by
    apply Complex.ext <;> simp [hcre]
  have hKorth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have heq (x : D.domain) : inner ℂ (c • y) (x : H) = inner ℂ y (D x) := by
      let p : C.graph := ⟨((x : H), D x),
        LinearPMap.le_graph_of_le hDC (D.mem_graph x)⟩
      have hz := (K.mem_orthogonal' y).mp hy (shiftedGraphMap C c p)
        (show shiftedGraphMap C c p ∈ K from ⟨p, rfl⟩)
      change inner ℂ y (D x + c • (x : H)) = 0 at hz
      rw [inner_add_right, inner_smul_right] at hz
      rw [inner_smul_left]
      change star c * inner ℂ y (x : H) = inner ℂ y (D x)
      rw [hconj]
      linear_combination -hz
    have hm : y ∈ D.adjoint.domain :=
      D.mem_adjoint_domain_of_exists _ ⟨c • y, heq⟩
    have hDy : D.adjoint ⟨y, hm⟩ = c • y :=
      LinearPMap.adjoint_apply_eq hd _ heq
    exact hdef ⟨y, hm⟩ hDy
  have hK : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hKorth
  intro y
  have hy : y ∈ K := by rw [hK]; trivial
  exact hy

/-- The complete Hilbert-space square implication appearing in the L03 root. -/
theorem essentialSelfAdjointOfSquare :
    OperatorCandidates.EssentialSelfAdjointOfSquare (H := H) := by
  intro D A hd hs hsq ha hc hsa
  have hDc : D.IsClosable := symmetric_isClosable D hd hs
  have hCd : Dense (D.closure.domain : Set H) := hd.mono D.le_closure.1
  have hCs : D.closure.IsFormalAdjoint D.closure := symmetric_closure hDc hs
  have hCstar : D.closure.adjoint ≤ D.adjoint := adjoint_antitone hd hCd D.le_closure
  have hCstar' : D.closure ≤ D.adjoint := (hCs.le_adjoint hCd).trans hCstar
  have hsurj : Function.Surjective (shiftedGraphMap D.closure Complex.I) :=
    shiftedGraphMap_surjective_of_deficiency hd D.le_closure hCs hDc.closure_isClosed
      Complex.I (by simp) (by simp)
      (fun u hu => square_deficiency_eq_zero hd hs hsq ha hc hsa u Complex.I
        (by simp) hu)
  refine ⟨hDc, LinearPMap.isSelfAdjoint_def.mpr (le_antisymm ?_ (hCs.le_adjoint hCd))⟩
  apply LinearPMap.le_of_le_graph
  intro q hq
  obtain ⟨p, hp⟩ := hsurj (q.2 + Complex.I • q.1)
  change (p : H × H).2 + Complex.I • (p : H × H).1 = q.2 + Complex.I • q.1 at hp
  have hqD := LinearPMap.le_graph_of_le hCstar hq
  have hpD := LinearPMap.le_graph_of_le hCstar' p.prop
  have hdiff := D.adjoint.graph.sub_mem hqD hpD
  rcases D.adjoint.mem_graph_iff.mp hdiff with ⟨u, hu, hDu⟩
  change (u : H) = q.1 - (p : H × H).1 at hu
  change D.adjoint u = q.2 - (p : H × H).2 at hDu
  have heigen : D.adjoint u = (-Complex.I) • (u : H) := by
    have hv : q.2 - (p : H × H).2 =
        Complex.I • (p : H × H).1 - Complex.I • q.1 := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using hp.symm
    rw [hDu, hu, hv]
    module
  have hzero := square_deficiency_eq_zero hd hs hsq ha hc hsa u (-Complex.I)
    (by simp) heigen
  have hq1 : q.1 = (p : H × H).1 := sub_eq_zero.mp (hu.symm.trans hzero)
  have hq2 : q.2 = (p : H × H).2 := D.adjoint.mem_graph_snd_inj' hqD hpD hq1
  have hqp : q = (p : H × H) := Prod.ext hq1 hq2
  rw [hqp]
  exact p.prop

end Hilbert

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V]
  [IsScalarTower ℝ ℂ V]

/-- The real Riemannian bilinear form determined by a Hermitian inner product. -/
def hermitianRealBilin (h : HermitianInnerProduct V) : LinearMap.BilinForm ℝ V :=
  LinearMap.mk₂ ℝ (fun u v => 2 * (h.toFun u v).re)
    (by intro u v w; rw [h.map_add_left, Complex.add_re]; ring)
    (by
      intro r u v
      rw [← IsScalarTower.algebraMap_smul ℂ r u, h.map_smul_left]
      change 2 * (star (r : ℂ) * h.toFun u v).re = r * (2 * (h.toFun u v).re)
      simp [Complex.mul_re]
      ring)
    (by intro u v w; rw [h.map_add_right, Complex.add_re]; ring)
    (by
      intro r u v
      rw [← IsScalarTower.algebraMap_smul ℂ r v, h.map_smul_right]
      change 2 * (h.toFun u v * (r : ℂ)).re = r * (2 * (h.toFun u v).re)
      simp [Complex.mul_re]
      ring)

theorem hermitianRealBilin_apply (h : HermitianInnerProduct V) (u v : V) :
    hermitianRealBilin h u v = 2 * (h.toFun u v).re := rfl

theorem hermitianRealBilin_nonneg (h : HermitianInnerProduct V) (u : V) :
    0 ≤ hermitianRealBilin h u u :=
  mul_nonneg (by norm_num) (h.positive_definite u).1

theorem hermitianRealBilin_pos (h : HermitianInnerProduct V) {u : V} (hu : u ≠ 0) :
    0 < hermitianRealBilin h u u :=
  mul_pos (by norm_num) (hermitianNormSq_pos h hu)

theorem hermitianRealBilin_symm (h : HermitianInnerProduct V) (u v : V) :
    hermitianRealBilin h u v = hermitianRealBilin h v u := by
  simp only [hermitianRealBilin_apply]
  rw [h.conjugate_symmetric]
  simp

/-- Every finite Gram matrix of the actual Riemannian pairing is nonnegative. -/
theorem hermitianRealGram_posSemidef {ι : Type*} [Fintype ι]
    (h : HermitianInnerProduct V) (v : ι → V) :
    Matrix.PosSemidef (fun i j => hermitianRealBilin h (v i) (v j) : Matrix ι ι ℝ) := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa using hermitianRealBilin_symm h (v j) (v i)
  · intro a
    have hn := hermitianRealBilin_nonneg h (∑ i, a i • v i)
    convert hn using 1
    simp [dotProduct, Matrix.mulVec, map_sum, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hermitianRealBilin_symm h (v j) (v i)]
    ring

theorem hermitianRealGram_posDef {ι : Type*} [Fintype ι]
    (h : HermitianInnerProduct V) (v : ι → V) (hv : LinearIndependent ℝ v) :
    Matrix.PosDef (fun i j => hermitianRealBilin h (v i) (v j) : Matrix ι ι ℝ) := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (hermitianRealGram_posSemidef h v).isHermitian
  · intro a ha
    have hsum : (∑ i, a i • v i) ≠ 0 := by
      intro hsum
      apply ha
      apply hv.fintypeLinearCombination_injective
      simpa [Fintype.linearCombination_apply] using hsum
    have hn := hermitianRealBilin_pos h hsum
    convert hn using 1
    simp [dotProduct, Matrix.mulVec, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hermitianRealBilin_symm h (v j) (v i)]
    ring

end Hermitian

set_option backward.isDefEq.respectTransparency false in
/-- The Schur product theorem applied finitely many times, including the empty product. -/
theorem matrixEntrywiseProd_posSemidef {ι τ : Type*} [Fintype ι]
    (s : Finset τ) (B : τ → Matrix ι ι ℝ)
    (hB : ∀ r ∈ s, (B r).PosSemidef) :
    Matrix.PosSemidef (fun i j => ∏ r ∈ s, B r i j : Matrix ι ι ℝ) := by
  classical
  revert hB
  induction s using Finset.induction_on with
  | empty =>
    intro _
    convert Matrix.posSemidef_vecMulVec_star_self (fun _ : ι => (1 : ℝ)) using 1
    ext i j
    simp [Matrix.vecMulVec]
  | @insert r s hrs ih =>
    intro hB
    have hr : (B r).PosSemidef := hB r (Finset.mem_insert_self r s)
    have hs := ih (fun j hj => hB j (Finset.mem_insert_of_mem hj))
    convert hr.hadamard hs using 1
    ext i j
    simp [Matrix.hadamard_apply, Finset.prod_insert, hrs]

theorem matrixPiProd_posSemidef {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (hC : C.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun I J : Fin k → ι => ∏ r, C (I r) (J r)) := by
  let B : Fin k → Matrix (Fin k → ι) (Fin k → ι) ℝ :=
    fun r => C.submatrix (fun I : Fin k → ι => I r) (fun I : Fin k → ι => I r)
  have hB (r : Fin k) : (B r).PosSemidef :=
    hC.submatrix (fun I : Fin k → ι => I r)
  have hProd := matrixEntrywiseProd_posSemidef (ι := Fin k → ι)
    Finset.univ B (fun r _ => hB r)
  simpa only [B, Matrix.submatrix_apply] using hProd

set_option backward.isDefEq.respectTransparency false in
theorem matrixPiProd_posDef {ι : Type*} [Fintype ι] (C : Matrix ι ι ℝ)
    (hC : C.PosDef) (k : ℕ) :
    Matrix.PosDef (fun I J : Fin k → ι => ∏ r, C (I r) (J r)) := by
  classical
  induction k with
  | zero =>
    have heq : (fun I J : Fin 0 → ι => ∏ r, C (I r) (J r)) =
        (1 : Matrix (Fin 0 → ι) (Fin 0 → ι) ℝ) := by
      ext I J
      have hIJ : I = J := Subsingleton.elim _ _
      simp [Matrix.one_apply, hIJ]
    rw [heq]
    exact Matrix.PosDef.one
  | succ k ih =>
    let P : Matrix (Fin k → ι) (Fin k → ι) ℝ := fun I J => ∏ r, C (I r) (J r)
    have hP : P.PosDef := ih
    let e : (Fin (k + 1) → ι) ≃ ι × (Fin k → ι) := (Fin.consEquiv (fun _ => ι)).symm
    have hK := (hC.kronecker hP).submatrix e.injective
    have heq : (fun I J : Fin (k + 1) → ι => ∏ r, C (I r) (J r)) =
        (Matrix.kronecker C P).submatrix e e := by
      ext I J
      simp [Matrix.submatrix_apply, Matrix.kronecker_apply, Fin.prod_univ_succ,
        e, Fin.consEquiv, P, Fin.tail]
    rw [heq]
    exact hK

section TensorMatrices

/-- Matrix of the tensor power of a real change of frame. -/
def tensorMatrix {ι κ : Type*} (T : Matrix ι κ ℝ) (k : ℕ) :
    Matrix (Fin k → ι) (Fin k → κ) ℝ :=
  fun I J => ∏ r, T (I r) (J r)

theorem tensorMatrix_transpose {ι κ : Type*} (T : Matrix ι κ ℝ) (k : ℕ) :
    tensorMatrix T.transpose k = (tensorMatrix T k).transpose := rfl

theorem tensorMatrix_mul {ι κ τ : Type*} [Fintype κ]
    (S : Matrix ι κ ℝ) (T : Matrix κ τ ℝ) (k : ℕ) :
    tensorMatrix (S * T) k = tensorMatrix S k * tensorMatrix T k := by
  classical
  ext I J
  simp only [tensorMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro K _
  exact Finset.prod_mul_distrib

theorem tensorMatrix_one {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    tensorMatrix (1 : Matrix ι ι ℝ) k = 1 := by
  classical
  ext I J
  by_cases h : I = J
  · subst J
    simp [tensorMatrix, Matrix.one_apply]
  · rw [Matrix.one_apply_ne h]
    obtain ⟨r, hr⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [Matrix.one_apply, hr])

theorem tensorMatrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : IsUnit T.det) (k : ℕ) :
    tensorMatrix T⁻¹ k = (tensorMatrix T k)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← tensorMatrix_mul, Matrix.nonsing_inv_mul T hT, tensorMatrix_one]

/-- The coordinate contraction is unchanged by an invertible simultaneous change of frame. -/
theorem matrixContraction_change_frame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U P : Matrix ι ι ℝ) (hU : IsUnit U.det) (a b : ι → ℝ) :
    dotProduct (Matrix.mulVec U.transpose a)
        (Matrix.mulVec (U⁻¹ * P * U.transpose⁻¹) (Matrix.mulVec U.transpose b)) =
      dotProduct a (Matrix.mulVec P b) := by
  have hUt : IsUnit U.transpose.det := by simpa only [Matrix.det_transpose] using hU
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul U.transpose hUt,
    Matrix.mul_one]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv U hU,
    Matrix.one_mul]

end TensorMatrices

section ContractionBases

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
  {k : ℕ}

/-- Coefficients of an actual multilinear form transform by the tensor power of the frame map. -/
theorem multilinear_coefficients_change_basis (b c : Basis ι ℝ V)
    (A : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    (fun J : Fin k → ι => A (fun r => c (J r))) =
      Matrix.mulVec (tensorMatrix (b.toMatrix c) k).transpose
        (fun I : Fin k → ι => A (fun r => b (I r))) := by
  classical
  funext J
  have hexp (r : Fin k) : c (J r) = ∑ i, b.toMatrix c i (J r) • b i := by
    simpa only [Basis.toMatrix_apply] using (b.sum_repr (c (J r))).symm
  calc
    A (fun r => c (J r)) = A (fun r => ∑ i, b.toMatrix c i (J r) • b i) := by
      congr 1
      funext r
      exact hexp r
    _ = ∑ I : Fin k → ι, A (fun r => b.toMatrix c (I r) (J r) • b (I r)) :=
      A.map_sum (fun r i => b.toMatrix c i (J r) • b i)
    _ = ∑ I : Fin k → ι,
        (∏ r, b.toMatrix c (I r) (J r)) * A (fun r => b (I r)) := by
      apply Finset.sum_congr rfl
      intro I _
      exact A.map_smul_univ _ _
    _ = _ := rfl

theorem basisGram_inv_change (b c : Basis ι ℝ V) (G : LinearMap.BilinForm ℝ V) :
    (LinearMap.BilinForm.toMatrix c G)⁻¹ =
      (b.toMatrix c)⁻¹ * (LinearMap.BilinForm.toMatrix b G)⁻¹ * (b.toMatrix c).transpose⁻¹ := by
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c G,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

theorem tensorMatrix_basisGram_inv_change (b c : Basis ι ℝ V)
    (G : LinearMap.BilinForm ℝ V) (k : ℕ) :
    tensorMatrix (LinearMap.BilinForm.toMatrix c G)⁻¹ k =
      (tensorMatrix (b.toMatrix c) k)⁻¹ *
        tensorMatrix (LinearMap.BilinForm.toMatrix b G)⁻¹ k *
          (tensorMatrix (b.toMatrix c) k).transpose⁻¹ := by
  letI := b.invertibleToMatrix c
  have hU : IsUnit (b.toMatrix c).det := Matrix.isUnit_det_of_invertible _
  have hUt : IsUnit (b.toMatrix c).transpose.det := by
    simpa only [Matrix.det_transpose] using hU
  rw [basisGram_inv_change, tensorMatrix_mul, tensorMatrix_mul,
    tensorMatrix_inv _ hU, tensorMatrix_inv _ hUt, tensorMatrix_transpose]

/-- Complete inverse-Gram contraction of two covariant tensors in a basis. -/
def basisTensorContraction (b : Basis ι ℝ V) (G : LinearMap.BilinForm ℝ V)
    (A B : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) : ℝ :=
  dotProduct (fun I : Fin k → ι => A (fun r => b (I r)))
    (Matrix.mulVec (tensorMatrix (LinearMap.BilinForm.toMatrix b G)⁻¹ k)
      (fun I : Fin k → ι => B (fun r => b (I r))))

/-- This contraction is intrinsic: changing the basis changes neither value nor normalization. -/
theorem basisTensorContraction_basis_independent (b c : Basis ι ℝ V)
    (G : LinearMap.BilinForm ℝ V) (A B : MultilinearMap ℝ (fun _ : Fin k => V) ℝ) :
    basisTensorContraction c G A B = basisTensorContraction b G A B := by
  letI := b.invertibleToMatrix c
  have hU : IsUnit (b.toMatrix c).det := Matrix.isUnit_det_of_invertible _
  have hTU : IsUnit (tensorMatrix (b.toMatrix c) k).det := by
    apply Matrix.isUnit_det_of_left_inverse (B := tensorMatrix (b.toMatrix c)⁻¹ k)
    rw [← tensorMatrix_mul, Matrix.nonsing_inv_mul _ hU, tensorMatrix_one]
  unfold basisTensorContraction
  rw [multilinear_coefficients_change_basis b c A,
    multilinear_coefficients_change_basis b c B, tensorMatrix_basisGram_inv_change]
  exact matrixContraction_change_frame _ _ hTU _ _

end ContractionBases

section Forms

variable {n k : ℕ} {M : ComplexManifold n}

def realModelBasis (n : ℕ) : Basis (RIdx n) ℝ (ComplexVector n) :=
  Complex.basisOneI.smulTower' (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

theorem realModelBasis_apply (a : RIdx n) : realModelBasis n a = realVec a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;>
    simp [realModelBasis, Basis.smulTower'_apply, realVec,
      EuclideanSpace.basisFun_apply, Complex.basisOneI]

theorem realVec_linearIndependent (n : ℕ) : LinearIndependent ℝ (realVec (n := n)) := by
  have heq : (realModelBasis n : RIdx n → ComplexVector n) = realVec :=
    funext realModelBasis_apply
  rw [← heq]
  exact (realModelBasis n).linearIndependent

set_option backward.isDefEq.respectTransparency false in
theorem chartVec_self (x : M.Carrier) (v : ComplexVector n) :
    chartVec x x v = (tangentSpaceCastModel (ComplexModel n) x).symm v := by
  have h := mfderivWithin_range_extChartAt_symm (I := ComplexModel n) (x := x)
  have hrange : Set.range (ComplexModel n) = Set.univ := by
    change Set.range (id : ComplexVector n → ComplexVector n) = Set.univ
    exact Set.range_id
  rw [hrange, mfderivWithin_univ] at h
  with_unfolding_all
    exact DFunLike.congr_fun h v

theorem chartRealVec_linearIndependent (x : M.Carrier) :
    LinearIndependent ℝ (fun a : RIdx n => chartVec x x (realVec a)) := by
  let e : ComplexVector n ≃ₗ[ℝ] TangentVector M x :=
    (tangentSpaceCastModel (ComplexModel n) x).symm.toLinearEquiv.restrictScalars ℝ
  let b : Basis (RIdx n) ℝ (TangentVector M x) := (realModelBasis n).map e
  have heq : (b : RIdx n → TangentVector M x) =
      (fun a : RIdx n => chartVec x x (realVec a)) := by
    funext a
    simp only [b, Basis.map_apply, realModelBasis_apply, chartVec_self]
    rfl
  rw [← heq]
  exact b.linearIndependent

theorem formComponents_center_apply (A : RealForm M k) (x : M.Carrier)
    (I : Fin k → RIdx n) :
    formComponents A x (chartPt x x) I =
      A x (fun r => (tangentSpaceCastModel (ComplexModel n) x).symm (realVec (I r))) := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  unfold formComponents
  rw [hx]
  simp only [chartVec_self]

/-- Vanishing of every actual chart coefficient detects the intrinsic form value. -/
theorem formComponents_center_eq_zero_iff (A : RealForm M k) (x : M.Carrier) :
    formComponents A x (chartPt x x) = 0 ↔ A x = 0 := by
  constructor
  · intro h
    let e : ComplexVector n ≃ₗ[ℝ] TangentVector M x :=
      (tangentSpaceCastModel (ComplexModel n) x).symm.toLinearEquiv.restrictScalars ℝ
    let b : Basis (RIdx n) ℝ (TangentVector M x) := (realModelBasis n).map e
    have hAlt : (A x).toAlternatingMap = 0 := by
      apply b.ext_alternating
      intro I _
      have hc := congrFun h I
      change formComponents A x (chartPt x x) I = 0 at hc
      rw [formComponents_center_apply] at hc
      simpa [b, Basis.map_apply, realModelBasis_apply, e] using hc
    apply ContinuousAlternatingMap.ext
    intro v
    exact congrArg (fun f : (TangentVector M x) [⋀^Fin k]→ₗ[ℝ] ℝ => f v) hAlt
  · intro h
    funext I
    rw [formComponents_center_apply, h]
    rfl

/-- The actual inverse-chart derivative, regarded as a real linear map. -/
def chartRealLinearMap (x y : M.Carrier) : ComplexVector n →ₗ[ℝ] TangentVector M y where
  toFun := chartVec x y
  map_add' u v := by
    unfold chartVec
    exact map_add _ u v
  map_smul' r u := by
    unfold chartVec
    exact (mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) x).symm (chartPt x y)).toLinearMap.map_smul_of_tower r u

/-- The complete chart frame is an actual real linear equivalence on its source. -/
def chartRealLinearEquiv (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    ComplexVector n ≃ₗ[ℝ] TangentVector M y :=
  { chartRealLinearMap x y with
    invFun := tangentCoords x y
    left_inv := L12Aux.tangentCoords_chartVec x y hy
    right_inv := L12Aux.chartVec_tangentCoords x y hy }

def localRealBasis (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    Basis (RIdx n) ℝ (TangentVector M y) :=
  (realModelBasis n).map (chartRealLinearEquiv x y hy)

theorem localRealBasis_apply (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (a : RIdx n) :
    localRealBasis x y hy a = chartVec x y (realVec a) := by
  simp only [localRealBasis, Basis.map_apply, realModelBasis_apply]
  rfl

theorem formComponents_apply_of_mem_source (A : RealForm M k) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (I : Fin k → RIdx n) :
    formComponents A x (chartPt x y) I = A y (fun r => localRealBasis x y hy (I r)) := by
  have hx : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  unfold formComponents
  rw [hx]
  simp only [localRealBasis_apply]

theorem localRealBasis_Gram (g : HermitianField M) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    LinearMap.BilinForm.toMatrix (localRealBasis x y hy) (hermitianRealBilin (g y)) =
      realMetricFn g x (chartPt x y) := by
  have hx : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  unfold realMetricFn
  rw [hx]
  ext a b
  simp only [LinearMap.BilinForm.toMatrix_apply, localRealBasis_apply,
    hermitianRealBilin_apply]

/-- The coordinate contraction is exactly the intrinsic tensor contraction in its local frame. -/
theorem coordinateContraction_eq_basisTensorContraction (g : HermitianField M)
    (A B : RealForm M k) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    (∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
      formComponents A x (chartPt x y) I * formComponents B x (chartPt x y) J *
        ∏ r, (realMetricFn g x (chartPt x y))⁻¹ (I r) (J r)) =
      basisTensorContraction (localRealBasis x y hy) (hermitianRealBilin (g y))
        (A y).toAlternatingMap.toMultilinearMap (B y).toAlternatingMap.toMultilinearMap := by
  unfold basisTensorContraction
  rw [localRealBasis_Gram]
  simp only [dotProduct, Matrix.mulVec, tensorMatrix, Matrix.of_apply,
    Matrix.transpose_apply, Finset.mul_sum, formComponents_apply_of_mem_source A x y hy,
    formComponents_apply_of_mem_source B x y hy]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  change (A y (fun r => localRealBasis x y hy (I r))) *
      (B y (fun r => localRealBasis x y hy (J r))) *
        (∏ r, (realMetricFn g x (chartPt x y))⁻¹ (I r) (J r)) =
    (A y (fun r => localRealBasis x y hy (I r))) *
      ((∏ r, (realMetricFn g x (chartPt x y))⁻¹ (I r) (J r)) *
        (B y (fun r => localRealBasis x y hy (J r))))
  ring

/-- The actual form pairing can be evaluated in any fixed chart containing the point. -/
theorem formInner_in_fixed_chart (g : HermitianField M) (A B : RealForm M k)
    (x y : M.Carrier) (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    formInner g A B y = (Nat.factorial k : ℝ)⁻¹ *
      ∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
        formComponents A x (chartPt x y) I * formComponents B x (chartPt x y) J *
          ∏ r, (realMetricFn g x (chartPt x y))⁻¹ (I r) (J r) := by
  unfold formInner
  rw [coordinateContraction_eq_basisTensorContraction g A B y y (mem_extChartAt_source y),
    coordinateContraction_eq_basisTensorContraction g A B x y hy]
  rw [basisTensorContraction_basis_independent
    (localRealBasis x y hy) (localRealBasis y y (mem_extChartAt_source y))]

theorem realMetricFn_posDef_of_mem_target (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) : (realMetricFn g x z).PosDef := by
  let y := chartInv x z
  have hy : y ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  have hzy : chartPt x y = z := (extChartAt (ComplexModel n) x).right_inv hz
  rw [← hzy, ← localRealBasis_Gram g x y hy]
  have heq : LinearMap.BilinForm.toMatrix (localRealBasis x y hy)
      (hermitianRealBilin (g y)) =
      (fun a b => hermitianRealBilin (g y) (localRealBasis x y hy a) (localRealBasis x y hy b)) := by
    ext a b
    simp only [LinearMap.BilinForm.toMatrix_apply]
  rw [heq]
  exact hermitianRealGram_posDef (g y) (localRealBasis x y hy)
    (localRealBasis x y hy).linearIndependent

theorem realMetricFn_continuousOn (g : SmoothMetric M) (x : M.Carrier) :
    ContinuousOn (realMetricFn g.form x) (chartTarget x) := by
  apply continuousOn_pi.mpr
  intro a
  apply continuousOn_pi.mpr
  intro b
  exact (L18Aux.metricSmooth_of_smoothMetric g x a b).continuousOn

theorem realMetricFn_inv_continuousOn (g : SmoothMetric M) (x : M.Carrier) :
    ContinuousOn (fun z => (realMetricFn g.form x z)⁻¹) (chartTarget x) := by
  intro z hz
  have hdet : IsUnit (realMetricFn g.form x z).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (realMetricFn_posDef_of_mem_target g.form x hz).isUnit
  have hi : ContinuousAt Ring.inverse (realMetricFn g.form x z).det := by
    simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt hdet.unit
  exact (continuousAt_matrix_inv _ hi).comp_continuousWithinAt
    (realMetricFn_continuousOn g x z hz)

theorem realMetricFn_inv_in_chart_continuousOn (g : SmoothMetric M) (x : M.Carrier) :
    ContinuousOn (fun y => (realMetricFn g.form x (chartPt x y))⁻¹)
      (chartAt (ComplexVector n) x).source := by
  have hc : ContinuousOn (chartPt x) (chartAt (ComplexVector n) x).source := by
    have h := continuousOn_extChartAt (I := ComplexModel n) x
    rw [extChartAt_source] at h
    with_unfolding_all
      exact h
  apply (realMetricFn_inv_continuousOn g x).comp hc
  intro y hy
  exact (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy)

theorem realMetricFn_inv_in_chart_aestronglyMeasurable (g : SmoothMetric M)
    (μ : Measure M.Carrier) (x : M.Carrier) (a b : RIdx n) :
    AEStronglyMeasurable (fun y => (realMetricFn g.form x (chartPt x y))⁻¹ a b)
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
  have h := (continuous_apply b).comp_continuousOn
    ((continuous_apply a).comp_continuousOn (realMetricFn_inv_in_chart_continuousOn g x))
  exact h.aestronglyMeasurable (chartAt (ComplexVector n) x).open_source.measurableSet

/-- Local coefficient measurability in the L² definition gives measurability of the intrinsic pairing. -/
theorem formInner_aestronglyMeasurable_on_chart_of_coefficients (g : SmoothMetric M)
    (μ : Measure M.Carrier) (A B : RealForm M k)
    (hA : ∀ x (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source))
    (hB : ∀ x (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => B y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source)) (x : M.Carrier) :
    AEStronglyMeasurable (formInner g.form A B)
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
  let F : M.Carrier → ℝ := fun y => (Nat.factorial k : ℝ)⁻¹ *
    ∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
      (A y (fun r => chartVec x y (realVec (I r)))) *
        (B y (fun r => chartVec x y (realVec (J r)))) *
          ∏ r, (realMetricFn g.form x (chartPt x y))⁻¹ (I r) (J r)
  have hF : AEStronglyMeasurable F (μ.restrict (chartAt (ComplexVector n) x).source) := by
    dsimp only [F]
    apply aestronglyMeasurable_const.mul
    apply Finset.aestronglyMeasurable_fun_sum
    intro I _
    apply Finset.aestronglyMeasurable_fun_sum
    intro J _
    apply ((hA x I).mul (hB x J)).mul
    apply Finset.aestronglyMeasurable_fun_prod
    intro r _
    exact realMetricFn_inv_in_chart_aestronglyMeasurable g μ x (I r) (J r)
  have heq : formInner g.form A B =ᵐ[μ.restrict (chartAt (ComplexVector n) x).source] F := by
    filter_upwards [self_mem_ae_restrict (chartAt (ComplexVector n) x).open_source.measurableSet]
      with y hy
    have hye : y ∈ (extChartAt (ComplexModel n) x).source := by
      simpa only [extChartAt_source] using hy
    rw [formInner_in_fixed_chart g.form A B x y hye]
    simp only [F, formComponents_apply_of_mem_source A x y hye,
      formComponents_apply_of_mem_source B x y hye, localRealBasis_apply]
  exact hF.congr heq.symm

theorem formInner_aestronglyMeasurable_on_chart (g : SmoothMetric M)
    (μ : Measure M.Carrier) (A B : RealForm M k)
    (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) (x : M.Carrier) :
    AEStronglyMeasurable (formInner g.form A B)
      (μ.restrict (chartAt (ComplexVector n) x).source) :=
  formInner_aestronglyMeasurable_on_chart_of_coefficients g μ A B hA.1 hB.1 x

/-- A countable chart subcover promotes the actual local coefficient data to global measurability. -/
theorem formInner_aestronglyMeasurable_of_coefficients (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k)
    (hA : ∀ x (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source))
    (hB : ∀ x (I : Fin k → RIdx n), AEStronglyMeasurable
      (fun y => B y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source)) :
    AEStronglyMeasurable (formInner g.form A B) μ := by
  obtain ⟨u, hu⟩ := isLindelof_univ.indexed_countable_subcover
    (fun x : M.Carrier => (chartAt (ComplexVector n) x).source)
    (fun x => (chartAt (ComplexVector n) x).open_source)
    (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_chart_source (ComplexVector n) y⟩)
  have hcover : (⋃ j, (chartAt (ComplexVector n) (u j)).source) = Set.univ :=
    Set.eq_univ_of_univ_subset hu
  have h := AEStronglyMeasurable.iUnion
    (fun j => formInner_aestronglyMeasurable_on_chart_of_coefficients g μ A B hA hB (u j))
  simpa only [hcover, Measure.restrict_univ] using h

theorem formInner_aestronglyMeasurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    AEStronglyMeasurable (formInner g.form A B) μ :=
  formInner_aestronglyMeasurable_of_coefficients g μ A B hA.1 hB.1

theorem formNormSq_aestronglyMeasurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    AEStronglyMeasurable (formNormSq g.form A) μ :=
  formInner_aestronglyMeasurable g μ A A hA hA

theorem formComponents_zero (x : M.Carrier) :
    formComponents (0 : RealForm M k) x = 0 := by
  funext z I
  simp [formComponents]

theorem formComponents_add (A B : RealForm M k) (x : M.Carrier) :
    formComponents (A + B) x = formComponents A x + formComponents B x := by
  funext z I
  simp [formComponents]

theorem formComponents_smul (a : ℝ) (A : RealForm M k) (x : M.Carrier) :
    formComponents (a • A) x = a • formComponents A x := by
  funext z I
  simp [formComponents]

theorem formInner_zero_left (g : HermitianField M) (A : RealForm M k) :
    formInner g 0 A = 0 := by
  funext x
  simp [formInner, formComponents]

theorem formInner_zero_right (g : HermitianField M) (A : RealForm M k) :
    formInner g A 0 = 0 := by
  funext x
  simp [formInner, formComponents]

theorem formInner_add_left (g : HermitianField M) (A B C : RealForm M k) :
    formInner g (A + B) C = formInner g A C + formInner g B C := by
  funext x
  simp [formInner, formComponents, add_mul, mul_add, Finset.sum_add_distrib]

theorem formInner_add_right (g : HermitianField M) (A B C : RealForm M k) :
    formInner g A (B + C) = formInner g A B + formInner g A C := by
  funext x
  simp [formInner, formComponents, add_mul, mul_add, Finset.sum_add_distrib]

theorem formInner_smul_left (g : HermitianField M) (a : ℝ) (A B : RealForm M k) :
    formInner g (a • A) B = a • formInner g A B := by
  funext x
  simp only [formInner, formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm a (Nat.factorial k : ℝ)⁻¹]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem formInner_smul_right (g : HermitianField M) (a : ℝ) (A B : RealForm M k) :
    formInner g A (a • B) = a • formInner g A B := by
  funext x
  simp only [formInner, formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm a (Nat.factorial k : ℝ)⁻¹]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem formInner_sub_left (g : HermitianField M) (A B C : RealForm M k) :
    formInner g (A - B) C = formInner g A C - formInner g B C := by
  funext x
  simp [formInner, formComponents, sub_mul, mul_sub, Finset.sum_sub_distrib]

theorem formInner_sub_right (g : HermitianField M) (A B C : RealForm M k) :
    formInner g A (B - C) = formInner g A B - formInner g A C := by
  funext x
  simp [formInner, formComponents, sub_mul, mul_sub, Finset.sum_sub_distrib]

/-- The real metric calculator inherits symmetry directly from the Hermitian form. -/
theorem realMetricFn_isSymm (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : (realMetricFn g x z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  unfold realMetricFn
  rw [(g (chartInv x z)).conjugate_symmetric]
  simp

/-- This also holds for the totalized inverse used in the actual form pairing. -/
theorem realMetricFn_inv_isSymm (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : ((realMetricFn g x z)⁻¹).IsSymm :=
  (realMetricFn_isSymm g x z).inv

theorem realMetricFn_posSemidef (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : (realMetricFn g x z).PosSemidef :=
  hermitianRealGram_posSemidef (g (chartInv x z))
    (fun a => chartVec x (chartInv x z) (realVec a))

theorem realMetricFn_inv_posSemidef (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : ((realMetricFn g x z)⁻¹).PosSemidef :=
  (realMetricFn_posSemidef g x z).inv

/-- At the evaluation point used by `formInner`, the coordinate frame is a genuine basis. -/
theorem realMetricFn_posDef_at_center (g : HermitianField M) (x : M.Carrier) :
    (realMetricFn g x (chartPt x x)).PosDef := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  unfold realMetricFn
  rw [hx]
  exact hermitianRealGram_posDef (g x) (fun a => chartVec x x (realVec a))
    (chartRealVec_linearIndependent x)

theorem realMetricFn_inv_posDef_at_center (g : HermitianField M) (x : M.Carrier) :
    ((realMetricFn g x (chartPt x x))⁻¹).PosDef :=
  (realMetricFn_posDef_at_center g x).inv

/-- The inverse-metric tensor-product matrix occurring verbatim in `formInner`. -/
theorem formPairingMatrix_posSemidef (g : HermitianField M) (x : M.Carrier) :
    Matrix.PosSemidef (fun I J : Fin k → RIdx n =>
      ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r)) :=
  matrixPiProd_posSemidef _ (realMetricFn_inv_posSemidef g x (chartPt x x)) k

theorem formPairingMatrix_posDef (g : HermitianField M) (x : M.Carrier) :
    Matrix.PosDef (fun I J : Fin k → RIdx n =>
      ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r)) :=
  matrixPiProd_posDef _ (realMetricFn_inv_posDef_at_center g x) k

theorem formInner_symm (g : HermitianField M) (A B : RealForm M k) :
    formInner g A B = formInner g B A := by
  funext x
  unfold formInner
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  have hprod :
      (∏ r, (realMetricFn g x (chartPt x x))⁻¹ (J r) (I r)) =
        ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r) := by
    apply Finset.prod_congr rfl
    intro r _
    exact (realMetricFn_inv_isSymm g x (chartPt x x)).apply (I r) (J r)
  rw [hprod]
  ring

/-- Alternating forms above the actual real dimension vanish pointwise. -/
theorem realForm_eq_zero_of_degree_gt (A : RealForm M k) (hk : 2 * n < k) : A = 0 := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  change (A x).toAlternatingMap v = 0
  apply AlternatingMap.map_linearDependent
  intro hv
  have hle := hv.fintype_card_le_finrank
  have hdim : Module.finrank ℝ (TangentVector M x) = 2 * n := by
    change Module.finrank ℝ (ComplexVector n) = 2 * n
    rw [finrank_real_of_complex]
    simp
  rw [Fintype.card_fin, hdim] at hle
  omega

/-- The full-degree cutoff in the graded L² definition follows from alternation. -/
theorem gradedL2_iff (g : HermitianField M) (μ : Measure M.Carrier)
    (A : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.GradedL2 g μ A ↔ ∀ k, L2RealForm g μ (A k) := by
  constructor
  · exact And.right
  · intro h
    exact ⟨fun k hk => realForm_eq_zero_of_degree_gt (A k) hk, h⟩

theorem formNormSq_zero (g : HermitianField M) :
    formNormSq g (0 : RealForm M k) = 0 := formInner_zero_left g 0

theorem formNormSq_eq_matrix (g : HermitianField M) (A : RealForm M k) (x : M.Carrier) :
    let a := formComponents A x (chartPt x x)
    let P : Matrix (Fin k → RIdx n) (Fin k → RIdx n) ℝ :=
      fun I J => ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r)
    formNormSq g A x = (Nat.factorial k : ℝ)⁻¹ *
      dotProduct (star a) (Matrix.mulVec P a) := by
  dsimp only
  unfold formNormSq formInner
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem formNormSq_pos_of_components_ne_zero (g : HermitianField M) (A : RealForm M k)
    (x : M.Carrier) (hA : formComponents A x (chartPt x x) ≠ 0) :
    0 < formNormSq g A x := by
  rw [formNormSq_eq_matrix]
  exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k)))
    ((formPairingMatrix_posDef (k := k) g x).dotProduct_mulVec_pos hA)

/-- The L² quadratic form is pointwise positive definite on the actual form fibre. -/
theorem formNormSq_eq_zero_iff (g : HermitianField M) (A : RealForm M k)
    (x : M.Carrier) : formNormSq g A x = 0 ↔ A x = 0 := by
  rw [← formComponents_center_eq_zero_iff A x]
  constructor
  · intro h
    by_contra hA
    exact (formNormSq_pos_of_components_ne_zero g A x hA).ne' h
  · intro h
    rw [formNormSq_eq_matrix]
    simp [h]

/-- The calculator in the L² integral is a nonnegative quadratic form in every degree. -/
theorem formNormSq_nonneg (g : HermitianField M) (A : RealForm M k) (x : M.Carrier) :
    0 ≤ formNormSq g A x := by
  unfold formNormSq formInner
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hn := (formPairingMatrix_posSemidef (k := k) g x).dotProduct_mulVec_nonneg
    (fun I => formComponents A x (chartPt x x) I)
  convert hn using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

/-- Pointwise Cauchy--Schwarz for the exact inverse-metric form pairing. -/
theorem formInner_sq_le (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) :
    (formInner g A B x) ^ 2 ≤ formNormSq g A x * formNormSq g B x := by
  have hpoly (t : ℝ) : 0 ≤ formNormSq g B x * (t * t) +
      (2 * formInner g A B x) * t + formNormSq g A x := by
    have h := formNormSq_nonneg g (A + t • B) x
    simp only [formNormSq, formInner_add_left, formInner_add_right,
      formInner_smul_left, formInner_smul_right, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h
    rw [congrFun (formInner_symm g B A) x] at h
    change 0 ≤ formInner g B B x * (t * t) +
      (2 * formInner g A B x) * t + formInner g A A x
    nlinarith
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

theorem formInner_abs_le (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) :
    |formInner g A B x| ≤ formNormSq g A x + formNormSq g B x := by
  have hA := formNormSq_nonneg g A x
  have hB := formNormSq_nonneg g B x
  have hCS := formInner_sq_le g A B x
  have hI := sq_abs (formInner g A B x)
  nlinarith [sq_nonneg (formNormSq g A x - formNormSq g B x),
    abs_nonneg (formInner g A B x)]

theorem formNormSq_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    Integrable (formNormSq g.form A) μ := by
  refine ⟨formNormSq_aestronglyMeasurable g μ A hA, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form A x)).mpr hA.2

/-- The actual L² pairing is integrable, before taking any quotient or completion. -/
theorem formInner_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    Integrable (formInner g.form A B) μ := by
  apply ((formNormSq_integrable g μ A hA).add (formNormSq_integrable g μ B hB)).mono'
    (formInner_aestronglyMeasurable g μ A B hA hB)
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using formInner_abs_le g.form A B x

theorem formNormSq_add_eq (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) :
    formNormSq g (A + B) x = formNormSq g A x + 2 * formInner g A B x + formNormSq g B x := by
  simp only [formNormSq, formInner_add_left, formInner_add_right, Pi.add_apply]
  rw [congrFun (formInner_symm g B A) x]
  ring

theorem formNormSq_sub_eq (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) :
    formNormSq g (A - B) x = formNormSq g A x - 2 * formInner g A B x + formNormSq g B x := by
  simp only [formNormSq, formInner_sub_left, formInner_sub_right, Pi.sub_apply]
  rw [congrFun (formInner_symm g B A) x]
  ring

theorem formNormSq_smul_eq (g : HermitianField M) (a : ℝ) (A : RealForm M k) (x : M.Carrier) :
    formNormSq g (a • A) x = a ^ 2 * formNormSq g A x := by
  simp only [formNormSq, formInner_smul_left, formInner_smul_right, Pi.smul_apply, smul_eq_mul]
  ring

theorem formNormSq_add_le (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) :
    formNormSq g (A + B) x ≤ 2 * (formNormSq g A x + formNormSq g B x) := by
  have h := formNormSq_nonneg g (A - B) x
  rw [formNormSq_sub_eq] at h
  rw [formNormSq_add_eq]
  linarith

theorem l2RealForm_zero (g : HermitianField M) (μ : Measure M.Carrier) :
    L2RealForm g μ (0 : RealForm M k) := by
  constructor
  · intro x I
    simpa using (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : M.Carrier => (0 : ℝ))
        (μ.restrict (chartAt (ComplexVector n) x).source))
  · simp only [formNormSq_zero, Pi.zero_apply, ENNReal.ofReal_zero, lintegral_zero]
    exact ENNReal.zero_lt_top

theorem l2RealForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    L2RealForm g.form μ (A + B) := by
  have hc (x : M.Carrier) (I : Fin k → RIdx n) : AEStronglyMeasurable
      (fun y => (A + B) y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    simpa [Pi.add_def] using (hA.1 x I).add (hB.1 x I)
  have hm : AEStronglyMeasurable (formNormSq g.form (A + B)) μ :=
    formInner_aestronglyMeasurable_of_coefficients g μ (A + B) (A + B) hc hc
  have hn : Integrable (formNormSq g.form (A + B)) μ := by
    apply (((formNormSq_integrable g μ A hA).add
      (formNormSq_integrable g μ B hB)).const_mul 2).mono_nonneg hm
      (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form (A + B) x)
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Pi.add_apply] using formNormSq_add_le g.form A B x
  refine ⟨hc, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form (A + B) x)).mp hn.2

theorem l2RealForm_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a : ℝ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (a • A) := by
  have hc (x : M.Carrier) (I : Fin k → RIdx n) : AEStronglyMeasurable
      (fun y => (a • A) y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    simpa [Pi.smul_def] using (hA.1 x I).const_smul a
  have hn : Integrable (formNormSq g.form (a • A)) μ := by
    apply ((formNormSq_integrable g μ A hA).const_mul (a ^ 2)).congr
    exact Filter.Eventually.of_forall fun x => (formNormSq_smul_eq g.form a A x).symm
  refine ⟨hc, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form (a • A) x)).mp hn.2

/-- The concrete L² sections form a real vector subspace; no analytic closure is assumed. -/
def l2FormSubmodule (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Submodule ℝ (RealForm M k) where
  carrier := {A | L2RealForm g.form μ A}
  zero_mem' := l2RealForm_zero g.form μ
  add_mem' hA hB := l2RealForm_add g μ _ _ hA hB
  smul_mem' a _ hA := l2RealForm_smul g μ a _ hA

theorem l2RealForm_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    L2RealForm g.form μ (A - B) :=
  (l2FormSubmodule g μ k).sub_mem hA hB

theorem integral_formNormSq_eq_zero_iff_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    (∫ x, formNormSq g.form A x ∂μ) = 0 ↔ ∀ᵐ x ∂μ, A x = 0 := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => formNormSq_nonneg g.form A x)
    (formNormSq_integrable g μ A hA)]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (formNormSq_eq_zero_iff g.form A x).mp hx
  · intro h
    filter_upwards [h] with x hx
    exact (formNormSq_eq_zero_iff g.form A x).mpr hx

/-- The actual squared L² distance vanishes exactly on AE equality of two L² sections. -/
theorem formL2DistanceSq_eq_zero_iff_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    formL2DistanceSq g.form μ A B = 0 ↔ ∀ᵐ x ∂μ, A x = B x := by
  have hD := l2RealForm_sub g μ A B hA hB
  have hm : AEMeasurable (fun x => ENNReal.ofReal (formNormSq g.form (A - B) x)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (formNormSq_aestronglyMeasurable g μ (A - B) hD).aemeasurable
  rw [formL2DistanceSq, lintegral_eq_zero_iff' hm]
  constructor
  · intro h
    filter_upwards [h] with x hx
    have hnorm : formNormSq g.form (A - B) x = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hx) (formNormSq_nonneg g.form (A - B) x)
    have hzero := (formNormSq_eq_zero_iff g.form (A - B) x).mp hnorm
    exact sub_eq_zero.mp hzero
  · intro h
    filter_upwards [h] with x hx
    have hzero : (A - B) x = 0 := sub_eq_zero.mpr hx
    rw [(formNormSq_eq_zero_iff g.form (A - B) x).mpr hzero]
    exact ENNReal.ofReal_zero

/-- A type synonym prevents the product topology on raw sections from being
mistaken for the topology induced by the integrated metric. -/
def L2FormSpace (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) : Type :=
  ↥(l2FormSubmodule g μ k)

instance l2FormSpaceAddCommGroup (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    AddCommGroup (L2FormSpace g μ k) :=
  inferInstanceAs (AddCommGroup ↥(l2FormSubmodule g μ k))

instance l2FormSpaceModule (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Module ℝ (L2FormSpace g μ k) :=
  inferInstanceAs (Module ℝ ↥(l2FormSubmodule g μ k))

def L2FormSpace.toSection {g : SmoothMetric M} {μ : Measure M.Carrier}
    (u : L2FormSpace g μ k) : RealForm M k :=
  (show ↥(l2FormSubmodule g μ k) from u).val

theorem L2FormSpace.toSection_l2 {g : SmoothMetric M} {μ : Measure M.Carrier}
    (u : L2FormSpace g μ k) : L2RealForm g.form μ u.toSection :=
  (show ↥(l2FormSubmodule g μ k) from u).property

theorem L2FormSpace.toSection_add {g : SmoothMetric M} {μ : Measure M.Carrier}
    (u v : L2FormSpace g μ k) : (u + v).toSection = u.toSection + v.toSection := rfl

theorem L2FormSpace.toSection_smul {g : SmoothMetric M} {μ : Measure M.Carrier}
    (a : ℝ) (u : L2FormSpace g μ k) : (a • u).toSection = a • u.toSection := rfl

theorem L2FormSpace.toSection_sub {g : SmoothMetric M} {μ : Measure M.Carrier}
    (u v : L2FormSpace g μ k) : (u - v).toSection = u.toSection - v.toSection := rfl

/-- The semidefinite scalar product is the actual Riemannian L² integral. -/
@[instance_reducible]
def l2FormSpacePreInner (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    PreInnerProductSpace.Core ℝ (L2FormSpace g μ k) where
  inner u v := ∫ x, formInner g.form u.toSection v.toSection x ∂μ
  conj_inner_symm u v := by
    change (∫ x, formInner g.form v.toSection u.toSection x ∂μ) =
      ∫ x, formInner g.form u.toSection v.toSection x ∂μ
    rw [formInner_symm g.form v.toSection u.toSection]
  re_inner_nonneg u := by
    change 0 ≤ ∫ x, formNormSq g.form u.toSection x ∂μ
    exact integral_nonneg fun x => formNormSq_nonneg g.form u.toSection x
  add_left u v w := by
    change (∫ x, formInner g.form (u + v).toSection w.toSection x ∂μ) = _
    rw [L2FormSpace.toSection_add, formInner_add_left]
    exact integral_add
      (formInner_integrable g μ u.toSection w.toSection u.toSection_l2 w.toSection_l2)
      (formInner_integrable g μ v.toSection w.toSection v.toSection_l2 w.toSection_l2)
  smul_left u v r := by
    change (∫ x, formInner g.form (r • u).toSection v.toSection x ∂μ) =
      r * ∫ x, formInner g.form u.toSection v.toSection x ∂μ
    rw [L2FormSpace.toSection_smul, formInner_smul_left]
    exact integral_smul r _

instance l2FormSpaceSeminormedAddCommGroup (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    SeminormedAddCommGroup (L2FormSpace g μ k) := by
  letI : PreInnerProductSpace.Core ℝ (L2FormSpace g μ k) := l2FormSpacePreInner g μ k
  exact InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

instance l2FormSpaceInnerProductSpace (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    InnerProductSpace ℝ (L2FormSpace g μ k) :=
  InnerProductSpace.ofCore (l2FormSpacePreInner g μ k)

theorem l2FormSpace_inner_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u v : L2FormSpace g μ k) :
    inner ℝ u v = ∫ x, formInner g.form u.toSection v.toSection x ∂μ := rfl

/-- The separated Hilbert completion of the actual L² pre-inner-product space.
Surjectivity of section representatives and density of the smooth compact core
are further assertions, not part of this construction. -/
abbrev L2FormHilbert (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :=
  UniformSpace.Completion (L2FormSpace g μ k)

def realizeL2Form (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormSpace g μ k) : L2FormHilbert g μ k := u

theorem realizeL2Form_inner (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u v : L2FormSpace g μ k) :
    inner ℝ (realizeL2Form g μ u) (realizeL2Form g μ v) =
      ∫ x, formInner g.form u.toSection v.toSection x ∂μ :=
  UniformSpace.Completion.inner_coe u v

theorem realizeL2Form_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormSpace g μ k) :
    ‖realizeL2Form g μ u‖ ^ 2 = ∫ x, formNormSq g.form u.toSection x ∂μ := by
  rw [← real_inner_self_eq_norm_sq, realizeL2Form_inner]
  rfl

theorem realizeL2Form_sub (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u v : L2FormSpace g μ k) :
    realizeL2Form g μ (u - v) = realizeL2Form g μ u - realizeL2Form g μ v :=
  UniformSpace.Completion.coe_sub u v

/-- Separation in the constructed Hilbert space is exactly AE equality of actual sections. -/
theorem realizeL2Form_eq_iff_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u v : L2FormSpace g μ k) :
    realizeL2Form g μ u = realizeL2Form g μ v ↔
      ∀ᵐ x ∂μ, u.toSection x = v.toSection x := by
  calc
    realizeL2Form g μ u = realizeL2Form g μ v ↔
        ‖realizeL2Form g μ u - realizeL2Form g μ v‖ ^ 2 = 0 := by
      simp only [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]
    _ ↔ ‖realizeL2Form g μ (u - v)‖ ^ 2 = 0 := by rw [realizeL2Form_sub]
    _ ↔ (∫ x, formNormSq g.form (u - v).toSection x ∂μ) = 0 := by
      rw [realizeL2Form_norm_sq]
    _ ↔ ∀ᵐ x ∂μ, (u - v).toSection x = 0 :=
      integral_formNormSq_eq_zero_iff_ae g μ _ (u - v).toSection_l2
    _ ↔ ∀ᵐ x ∂μ, u.toSection x = v.toSection x := by
      apply Filter.eventually_congr
      exact Filter.Eventually.of_forall fun x => by
        rw [L2FormSpace.toSection_sub, Pi.sub_apply, sub_eq_zero]

/-- Actual L² sections are dense in their Hilbert completion.
This is distinct from the still unproved density of the compact smooth core. -/
theorem realizeL2Form_denseRange (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    DenseRange (realizeL2Form (k := k) g μ) := UniformSpace.Completion.denseRange_coe

theorem l2FormHilbert_complete (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    CompleteSpace (L2FormHilbert g μ k) := inferInstance

theorem formL2DistanceSq_self (g : HermitianField M) (μ : Measure M.Carrier)
    (A : RealForm M k) : formL2DistanceSq g μ A A = 0 := by
  simp [formL2DistanceSq, formNormSq_zero]

theorem hodgeCorePair_minimal {g : HermitianField M} {μ : Measure M.Carrier}
    {A W : RealForm M k} (h : OperatorCandidates.HodgeCorePair g μ A W) :
    OperatorCandidates.HodgeMinimalGraph g μ A W := by
  refine ⟨h.2.2.2.1, h.2.2.2.2.1, (fun _ => A), (fun _ => W), (fun _ => h), ?_⟩
  simp only [formL2DistanceSq_self, zero_add]
  exact tendsto_const_nhds

theorem gradedDistanceSq_self (g : HermitianField M) (μ : Measure M.Carrier)
    (A : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedDistanceSq g μ A A = 0 := by
  simp [OperatorCandidates.gradedDistanceSq, formL2DistanceSq_self]

theorem diracCorePair_minimal {g : HermitianField M} {μ : Measure M.Carrier}
    {A W : OperatorCandidates.GradedRealForm M}
    (h : OperatorCandidates.DiracCorePair g μ A W) :
    OperatorCandidates.DiracMinimalGraph g μ A W := by
  refine ⟨h.1, h.2.1, (fun _ => A), (fun _ => W), (fun _ => h), ?_⟩
  simp only [gradedDistanceSq_self, zero_add]
  exact tendsto_const_nhds

theorem formInner_congr_at (g : HermitianField M) {A A' B B' : RealForm M k}
    {x : M.Carrier} (hA : A x = A' x) (hB : B x = B' x) :
    formInner g A B x = formInner g A' B' x := by
  simp only [formInner, formComponents_center_apply, hA, hB]

theorem formNormSq_congr_at (g : HermitianField M) {A A' : RealForm M k}
    {x : M.Carrier} (hA : A x = A' x) : formNormSq g A x = formNormSq g A' x :=
  formInner_congr_at g hA hA

theorem formInner_congr_ae (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' B B' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hB : ∀ᵐ x ∂μ, B x = B' x) :
    formInner g A B =ᵐ[μ] formInner g A' B' := by
  filter_upwards [hA, hB] with x hx hy
  exact formInner_congr_at g hx hy

theorem l2RealForm_of_ae_eq (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' : RealForm M k} (hA : ∀ᵐ x ∂μ, A x = A' x)
    (h : L2RealForm g μ A) : L2RealForm g μ A' := by
  constructor
  · intro x I
    apply (h.1 x I).congr
    filter_upwards [ae_restrict_of_ae hA] with y hy
    rw [hy]
  · have heq : (∫⁻ x, ENNReal.ofReal (formNormSq g A x) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (formNormSq g A' x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hA] with x hx
      rw [formNormSq_congr_at g hx]
    rw [← heq]
    exact h.2

theorem l2RealForm_congr_ae (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' : RealForm M k} (hA : ∀ᵐ x ∂μ, A x = A' x) :
    L2RealForm g μ A ↔ L2RealForm g μ A' :=
  ⟨l2RealForm_of_ae_eq g hA,
    l2RealForm_of_ae_eq g (hA.mono fun _ h => h.symm)⟩

theorem formL2DistanceSq_congr_ae (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' B B' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hB : ∀ᵐ x ∂μ, B x = B' x) :
    formL2DistanceSq g μ A B = formL2DistanceSq g μ A' B' := by
  apply lintegral_congr_ae
  filter_upwards [hA, hB] with x hx hy
  have hdiff : (A - B) x = (A' - B') x := by simp only [Pi.sub_apply, hx, hy]
  rw [formNormSq_congr_at g hdiff]

/-- The minimal Hodge relation depends only on the two AE classes. -/
theorem hodgeMinimalGraph_of_ae_eq {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hW : ∀ᵐ x ∂μ, W x = W' x)
    (h : OperatorCandidates.HodgeMinimalGraph g μ A W) :
    OperatorCandidates.HodgeMinimalGraph g μ A' W' := by
  rcases h with ⟨hLA, hLW, As, Ws, hcore, ht⟩
  refine ⟨l2RealForm_of_ae_eq g hA hLA, l2RealForm_of_ae_eq g hW hLW,
    As, Ws, hcore, ?_⟩
  convert ht using 1
  funext j
  rw [formL2DistanceSq_congr_ae g (Filter.Eventually.of_forall fun _ => rfl) hA,
    formL2DistanceSq_congr_ae g (Filter.Eventually.of_forall fun _ => rfl) hW]

/-- The maximal Hodge relation has the same AE descent, including its integrability clauses. -/
theorem hodgeMaximalGraph_of_ae_eq {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hW : ∀ᵐ x ∂μ, W x = W' x)
    (h : OperatorCandidates.HodgeMaximalGraph g μ A W) :
    OperatorCandidates.HodgeMaximalGraph g μ A' W' := by
  refine ⟨l2RealForm_of_ae_eq g hA h.1, l2RealForm_of_ae_eq g hW h.2.1, ?_⟩
  intro B Z hcore
  rcases h.2.2 B Z hcore with ⟨hAZ, hWB, heq⟩
  have h1 : formInner g A Z =ᵐ[μ] formInner g A' Z :=
    formInner_congr_ae g hA (Filter.Eventually.of_forall fun _ => rfl)
  have h2 : formInner g W B =ᵐ[μ] formInner g W' B :=
    formInner_congr_ae g hW (Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨hAZ.congr h1, hWB.congr h2, ?_⟩
  calc
    (∫ x, formInner g A' Z x ∂μ) = ∫ x, formInner g A Z x ∂μ :=
      integral_congr_ae h1.symm
    _ = ∫ x, formInner g W B x ∂μ := heq
    _ = ∫ x, formInner g W' B x ∂μ := integral_congr_ae h2

theorem hodgeMinimalGraph_congr_ae {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hW : ∀ᵐ x ∂μ, W x = W' x) :
    OperatorCandidates.HodgeMinimalGraph g μ A W ↔
      OperatorCandidates.HodgeMinimalGraph g μ A' W' :=
  ⟨hodgeMinimalGraph_of_ae_eq hA hW,
    hodgeMinimalGraph_of_ae_eq (hA.mono fun _ h => h.symm) (hW.mono fun _ h => h.symm)⟩

theorem hodgeMaximalGraph_congr_ae {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : RealForm M k}
    (hA : ∀ᵐ x ∂μ, A x = A' x) (hW : ∀ᵐ x ∂μ, W x = W' x) :
    OperatorCandidates.HodgeMaximalGraph g μ A W ↔
      OperatorCandidates.HodgeMaximalGraph g μ A' W' :=
  ⟨hodgeMaximalGraph_of_ae_eq hA hW,
    hodgeMaximalGraph_of_ae_eq (hA.mono fun _ h => h.symm) (hW.mono fun _ h => h.symm)⟩

theorem gradedL2_of_ae_eq (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x) (h : OperatorCandidates.GradedL2 g μ A) :
    OperatorCandidates.GradedL2 g μ A' := by
  rw [gradedL2_iff] at h ⊢
  exact fun k => l2RealForm_of_ae_eq g (hA k) (h k)

theorem gradedInner_congr_ae (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' B B' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hB : ∀ k, ∀ᵐ x ∂μ, B k x = B' k x) :
    OperatorCandidates.gradedInner g A B =ᵐ[μ] OperatorCandidates.gradedInner g A' B' := by
  have hAall : ∀ᵐ x ∂μ, ∀ k, A k x = A' k x := ae_all_iff.mpr hA
  have hBall : ∀ᵐ x ∂μ, ∀ k, B k x = B' k x := ae_all_iff.mpr hB
  filter_upwards [hAall, hBall] with x hx hy
  unfold OperatorCandidates.gradedInner
  apply Finset.sum_congr rfl
  intro i _
  exact formInner_congr_at g (hx i.val) (hy i.val)

theorem gradedDistanceSq_congr_ae (g : HermitianField M) {μ : Measure M.Carrier}
    {A A' B B' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hB : ∀ k, ∀ᵐ x ∂μ, B k x = B' k x) :
    OperatorCandidates.gradedDistanceSq g μ A B =
      OperatorCandidates.gradedDistanceSq g μ A' B' := by
  unfold OperatorCandidates.gradedDistanceSq
  apply Finset.sum_congr rfl
  intro i _
  exact formL2DistanceSq_congr_ae g (hA i.val) (hB i.val)

/-- The full-degree minimal Dirac graph descends degreewise to AE classes. -/
theorem diracMinimalGraph_of_ae_eq {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hW : ∀ k, ∀ᵐ x ∂μ, W k x = W' k x)
    (h : OperatorCandidates.DiracMinimalGraph g μ A W) :
    OperatorCandidates.DiracMinimalGraph g μ A' W' := by
  rcases h with ⟨hLA, hLW, As, Ws, hcore, ht⟩
  refine ⟨gradedL2_of_ae_eq g hA hLA, gradedL2_of_ae_eq g hW hLW,
    As, Ws, hcore, ?_⟩
  convert ht using 1
  funext j
  rw [gradedDistanceSq_congr_ae g (fun _ => Filter.Eventually.of_forall fun _ => rfl) hA,
    gradedDistanceSq_congr_ae g (fun _ => Filter.Eventually.of_forall fun _ => rfl) hW]

/-- The maximal Dirac graph, including its integral tests, has the same AE descent. -/
theorem diracMaximalGraph_of_ae_eq {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hW : ∀ k, ∀ᵐ x ∂μ, W k x = W' k x)
    (h : OperatorCandidates.DiracMaximalGraph g μ A W) :
    OperatorCandidates.DiracMaximalGraph g μ A' W' := by
  refine ⟨gradedL2_of_ae_eq g hA h.1, gradedL2_of_ae_eq g hW h.2.1, ?_⟩
  intro B Z hcore
  rcases h.2.2 B Z hcore with ⟨hAZ, hWB, heq⟩
  have h1 : OperatorCandidates.gradedInner g A Z =ᵐ[μ]
      OperatorCandidates.gradedInner g A' Z :=
    gradedInner_congr_ae g hA (fun _ => Filter.Eventually.of_forall fun _ => rfl)
  have h2 : OperatorCandidates.gradedInner g W B =ᵐ[μ]
      OperatorCandidates.gradedInner g W' B :=
    gradedInner_congr_ae g hW (fun _ => Filter.Eventually.of_forall fun _ => rfl)
  refine ⟨hAZ.congr h1, hWB.congr h2, ?_⟩
  calc
    (∫ x, OperatorCandidates.gradedInner g A' Z x ∂μ) =
        ∫ x, OperatorCandidates.gradedInner g A Z x ∂μ := integral_congr_ae h1.symm
    _ = ∫ x, OperatorCandidates.gradedInner g W B x ∂μ := heq
    _ = ∫ x, OperatorCandidates.gradedInner g W' B x ∂μ := integral_congr_ae h2

theorem diracMinimalGraph_congr_ae {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hW : ∀ k, ∀ᵐ x ∂μ, W k x = W' k x) :
    OperatorCandidates.DiracMinimalGraph g μ A W ↔
      OperatorCandidates.DiracMinimalGraph g μ A' W' :=
  ⟨diracMinimalGraph_of_ae_eq hA hW,
    diracMinimalGraph_of_ae_eq (fun k => (hA k).mono fun _ h => h.symm)
      (fun k => (hW k).mono fun _ h => h.symm)⟩

theorem diracMaximalGraph_congr_ae {g : HermitianField M} {μ : Measure M.Carrier}
    {A A' W W' : OperatorCandidates.GradedRealForm M}
    (hA : ∀ k, ∀ᵐ x ∂μ, A k x = A' k x)
    (hW : ∀ k, ∀ᵐ x ∂μ, W k x = W' k x) :
    OperatorCandidates.DiracMaximalGraph g μ A W ↔
      OperatorCandidates.DiracMaximalGraph g μ A' W' :=
  ⟨diracMaximalGraph_of_ae_eq hA hW,
    diracMaximalGraph_of_ae_eq (fun k => (hA k).mono fun _ h => h.symm)
      (fun k => (hW k).mono fun _ h => h.symm)⟩

/-- Pointwise multiplication by a real scalar function, on the actual form fibres. -/
def multiplyRealForm (η : M.Carrier → ℝ) (A : RealForm M k) : RealForm M k :=
  fun x => η x • A x

theorem multiplyRealForm_normSq (g : HermitianField M) (η : M.Carrier → ℝ)
    (A : RealForm M k) (x : M.Carrier) :
    formNormSq g (multiplyRealForm η A) x = (η x) ^ 2 * formNormSq g A x := by
  have h : (multiplyRealForm η A) x = ((η x) • A) x := rfl
  exact (formNormSq_congr_at g h).trans (formNormSq_smul_eq g (η x) A x)

theorem multiplyRealForm_normSq_le (g : HermitianField M) (η : M.Carrier → ℝ)
    (A : RealForm M k) (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (x : M.Carrier) :
    formNormSq g (multiplyRealForm η A) x ≤ C ^ 2 * formNormSq g A x := by
  rw [multiplyRealForm_normSq]
  apply mul_le_mul_of_nonneg_right _ (formNormSq_nonneg g A x)
  have h := (sq_le_sq₀ (abs_nonneg (η x)) hC).mpr (hη x)
  simpa only [sq_abs] using h

theorem l2RealForm_multiply_bounded (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (multiplyRealForm η A) := by
  have hc (x : M.Carrier) (I : Fin k → RIdx n) : AEStronglyMeasurable
      (fun y => multiplyRealForm η A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    have hηr := hηm.mono_measure (Measure.restrict_le_self :
      μ.restrict (chartAt (ComplexVector n) x).source ≤ μ)
    simpa [multiplyRealForm, Pi.mul_def] using hηr.mul (hA.1 x I)
  have hm : AEStronglyMeasurable (formNormSq g.form (multiplyRealForm η A)) μ :=
    formInner_aestronglyMeasurable_of_coefficients g μ _ _ hc hc
  have hn : Integrable (formNormSq g.form (multiplyRealForm η A)) μ := by
    apply ((formNormSq_integrable g μ A hA).const_mul (C ^ 2)).mono_nonneg hm
      (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)
    exact Filter.Eventually.of_forall fun x => multiplyRealForm_normSq_le g.form η A C hC hη x
  refine ⟨hc, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)).mp hn.2

def L2FormSpace.ofSection {g : SmoothMetric M} {μ : Measure M.Carrier}
    (A : RealForm M k) (hA : L2RealForm g.form μ A) : L2FormSpace g μ k :=
  (show ↥(l2FormSubmodule g μ k) from ⟨A, hA⟩)

theorem L2FormSpace.toSection_ofSection {g : SmoothMetric M} {μ : Measure M.Carrier}
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    (L2FormSpace.ofSection A hA).toSection = A := rfl

theorem L2FormSpace.toSection_injective (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Function.Injective (L2FormSpace.toSection (g := g) (μ := μ) (k := k)) := by
  intro u v h
  exact Subtype.ext h

def multiplyRealFormLinear (η : M.Carrier → ℝ) : RealForm M k →ₗ[ℝ] RealForm M k where
  toFun := multiplyRealForm η
  map_add' A B := by
    funext x
    exact smul_add (η x) (A x) (B x)
  map_smul' r A := by
    funext x
    exact smul_comm (η x) r (A x)

def multiplyL2FormLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) :
    L2FormSpace g μ k →ₗ[ℝ] L2FormSpace g μ k where
  toFun u := L2FormSpace.ofSection (multiplyRealForm η u.toSection)
    (l2RealForm_multiply_bounded g μ η hηm C hC hη u.toSection u.toSection_l2)
  map_add' u v := by
    apply L2FormSpace.toSection_injective g μ k
    change multiplyRealForm η (u + v).toSection =
      multiplyRealForm η u.toSection + multiplyRealForm η v.toSection
    rw [L2FormSpace.toSection_add]
    exact (multiplyRealFormLinear η).map_add _ _
  map_smul' r u := by
    apply L2FormSpace.toSection_injective g μ k
    change multiplyRealForm η (r • u).toSection = r • multiplyRealForm η u.toSection
    rw [L2FormSpace.toSection_smul]
    exact (multiplyRealFormLinear η).map_smul r _

theorem multiplyL2FormLinear_toSection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u : L2FormSpace g μ k) :
    (multiplyL2FormLinear g μ η hηm C hC hη u).toSection = multiplyRealForm η u.toSection := rfl

theorem l2FormSpace_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : L2FormSpace g μ k) : ‖u‖ ^ 2 = ∫ x, formNormSq g.form u.toSection x ∂μ := by
  rw [← real_inner_self_eq_norm_sq, l2FormSpace_inner_eq]
  rfl

theorem multiplyL2FormLinear_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u : L2FormSpace g μ k) :
    ‖multiplyL2FormLinear g μ η hηm C hC hη u‖ ≤ C * ‖u‖ := by
  have hA := u.toSection_l2
  have hM := l2RealForm_multiply_bounded g μ η hηm C hC hη u.toSection hA
  have hI := integral_mono (formNormSq_integrable g μ _ hM)
    ((formNormSq_integrable g μ _ hA).const_mul (C ^ 2))
    (fun x => multiplyRealForm_normSq_le g.form η u.toSection C hC hη x)
  rw [integral_const_mul] at hI
  have hs : ‖multiplyL2FormLinear g μ η hηm C hC hη u‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2 := by
    simpa only [l2FormSpace_norm_sq, multiplyL2FormLinear_toSection] using hI
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg u))).mp
  nlinarith

def multiplyL2FormContinuous (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) :
    L2FormSpace g μ k →L[ℝ] L2FormSpace g μ k :=
  (multiplyL2FormLinear g μ η hηm C hC hη).mkContinuous C
    (multiplyL2FormLinear_norm_le g μ η hηm C hC hη)

/-- Bounded pointwise multiplication, canonically extended to the genuine Hilbert completion. -/
def multiplyL2FormHilbert (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  (multiplyL2FormContinuous g μ η hηm C hC hη).completion

theorem multiplyL2FormHilbert_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u : L2FormSpace g μ k) :
    multiplyL2FormHilbert g μ η hηm C hC hη (realizeL2Form g μ u) =
      realizeL2Form g μ (multiplyL2FormLinear g μ η hηm C hC hη u) :=
  ContinuousLinearMap.completion_apply_coe _ u

theorem multiplyL2FormHilbert_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u : L2FormHilbert g μ k) :
    ‖multiplyL2FormHilbert g μ η hηm C hC hη u‖ ≤ C * ‖u‖ := by
  refine UniformSpace.Completion.induction_on
    (p := fun u : L2FormHilbert g μ k =>
      ‖multiplyL2FormHilbert g μ η hηm C hC hη u‖ ≤ C * ‖u‖) u ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp (multiplyL2FormHilbert g μ η hηm C hC hη).continuous)
      (continuous_const.mul continuous_norm)
  · intro v
    change ‖multiplyL2FormHilbert g μ η hηm C hC hη (realizeL2Form g μ v)‖ ≤
      C * ‖realizeL2Form g μ v‖
    rw [multiplyL2FormHilbert_realize]
    simpa only [realizeL2Form, UniformSpace.Completion.norm_coe] using
      multiplyL2FormLinear_norm_le g μ η hηm C hC hη v

theorem multiplyL2FormHilbert_opNorm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) :
    ‖multiplyL2FormHilbert (k := k) g μ η hηm C hC hη‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC
    (multiplyL2FormHilbert_norm_le g μ η hηm C hC hη)

theorem multiplyRealForm_inner_left (g : HermitianField M) (η : M.Carrier → ℝ)
    (A B : RealForm M k) (x : M.Carrier) :
    formInner g (multiplyRealForm η A) B x = η x * formInner g A B x := by
  have h : (multiplyRealForm η A) x = ((η x) • A) x := rfl
  exact (formInner_congr_at g h rfl).trans (congrFun (formInner_smul_left g (η x) A B) x)

theorem multiplyRealForm_inner_right (g : HermitianField M) (η : M.Carrier → ℝ)
    (A B : RealForm M k) (x : M.Carrier) :
    formInner g A (multiplyRealForm η B) x = η x * formInner g A B x := by
  have h : (multiplyRealForm η B) x = ((η x) • B) x := rfl
  exact (formInner_congr_at g rfl h).trans (congrFun (formInner_smul_right g (η x) A B) x)

theorem multiplyL2FormLinear_inner_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u v : L2FormSpace g μ k) :
    inner ℝ (multiplyL2FormLinear g μ η hηm C hC hη u) v =
      inner ℝ u (multiplyL2FormLinear g μ η hηm C hC hη v) := by
  rw [l2FormSpace_inner_eq, l2FormSpace_inner_eq, multiplyL2FormLinear_toSection,
    multiplyL2FormLinear_toSection]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [multiplyRealForm_inner_left, multiplyRealForm_inner_right]

/-- Real scalar multiplication is symmetric for the actual integrated metric, also after completion. -/
theorem multiplyL2FormHilbert_inner_symm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C) (u v : L2FormHilbert g μ k) :
    inner ℝ (multiplyL2FormHilbert g μ η hηm C hC hη u) v =
      inner ℝ u (multiplyL2FormHilbert g μ η hηm C hC hη v) := by
  refine UniformSpace.Completion.induction_on₂
    (p := fun u v : L2FormHilbert g μ k =>
      inner ℝ (multiplyL2FormHilbert g μ η hηm C hC hη u) v =
        inner ℝ u (multiplyL2FormHilbert g μ η hηm C hC hη v)) u v ?_ ?_
  · exact isClosed_eq
      (((multiplyL2FormHilbert g μ η hηm C hC hη).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((multiplyL2FormHilbert g μ η hηm C hC hη).continuous.comp continuous_snd))
  · intro a b
    change inner ℝ (multiplyL2FormHilbert g μ η hηm C hC hη (realizeL2Form g μ a))
        (realizeL2Form g μ b) =
      inner ℝ (realizeL2Form g μ a)
        (multiplyL2FormHilbert g μ η hηm C hC hη (realizeL2Form g μ b))
    rw [multiplyL2FormHilbert_realize, multiplyL2FormHilbert_realize,
      realizeL2Form_inner, realizeL2Form_inner]
    exact multiplyL2FormLinear_inner_symm g μ η hηm C hC hη a b

/-- The frozen squared L² distance is exactly the squared Hilbert distance after realization. -/
theorem realizeL2Form_distanceSq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u v : L2FormSpace g μ k) :
    ENNReal.ofReal (‖realizeL2Form g μ u - realizeL2Form g μ v‖ ^ 2) =
      formL2DistanceSq g.form μ u.toSection v.toSection := by
  rw [← realizeL2Form_sub, realizeL2Form_norm_sq,
    ofReal_integral_eq_lintegral_ofReal
      (formNormSq_integrable g μ _ (u - v).toSection_l2)
      (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)]
  rfl

theorem tendsto_realizeL2Form_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (u : ℕ → L2FormSpace g μ k) (v : L2FormSpace g μ k) :
    Tendsto (fun j => realizeL2Form g μ (u j)) atTop (𝓝 (realizeL2Form g μ v)) ↔
      Tendsto (fun j => formL2DistanceSq g.form μ (u j).toSection v.toSection) atTop (𝓝 0) := by
  constructor
  · intro h
    have hn := tendsto_iff_norm_sub_tendsto_zero.mp h
    have hp : Tendsto (fun j => ‖realizeL2Form g μ (u j) - realizeL2Form g μ v‖ ^ 2)
        atTop (𝓝 0) := by simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hn.pow 2
    simpa only [realizeL2Form_distanceSq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hp
  · intro h
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    have hp : Tendsto (fun j => ‖realizeL2Form g μ (u j) - realizeL2Form g μ v‖ ^ 2)
        atTop (𝓝 0) := by
      simpa only [← realizeL2Form_distanceSq, ENNReal.toReal_ofReal (sq_nonneg _),
        ENNReal.toReal_zero, Function.comp_def] using ht
    have hs := (Real.continuous_sqrt.tendsto 0).comp hp
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def] using hs

theorem hodgeMaximalGraph_iff_realize_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W ↔
      ∀ B Z (hcore : OperatorCandidates.HodgeCorePair g.form μ B Z),
        inner ℝ (realizeL2Form g μ (L2FormSpace.ofSection A hA))
            (realizeL2Form g μ (L2FormSpace.ofSection Z hcore.2.2.2.2.1)) =
          inner ℝ (realizeL2Form g μ (L2FormSpace.ofSection W hW))
            (realizeL2Form g μ (L2FormSpace.ofSection B hcore.2.2.2.1)) := by
  constructor
  · intro h B Z hcore
    simpa only [realizeL2Form_inner, L2FormSpace.toSection_ofSection] using
      (h.2.2 B Z hcore).2.2
  · intro h
    refine ⟨hA, hW, ?_⟩
    intro B Z hcore
    refine ⟨formInner_integrable g μ A Z hA hcore.2.2.2.2.1,
      formInner_integrable g μ W B hW hcore.2.2.2.1, ?_⟩
    simpa only [realizeL2Form_inner, L2FormSpace.toSection_ofSection] using h B Z hcore

/-- The actual compact smooth Hodge core, realized as pairs in the constructed Hilbert space. -/
def hodgeCoreRealizedGraph (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Set (L2FormHilbert g μ k × L2FormHilbert g μ k) :=
  {p | ∃ (A W : RealForm M k) (hcore : OperatorCandidates.HodgeCorePair g.form μ A W),
    p = (realizeL2Form g μ (L2FormSpace.ofSection A hcore.2.2.2.1),
      realizeL2Form g μ (L2FormSpace.ofSection W hcore.2.2.2.2.1))}

/-- The distributional maximal graph is exactly the real Hilbert pairing against that same core. -/
theorem hodgeMaximalGraph_iff_core_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W ↔
      ∀ p ∈ hodgeCoreRealizedGraph g μ k,
        inner ℝ (realizeL2Form g μ (L2FormSpace.ofSection A hA)) p.2 =
          inner ℝ (realizeL2Form g μ (L2FormSpace.ofSection W hW)) p.1 := by
  rw [hodgeMaximalGraph_iff_realize_pairing g μ A W hA hW]
  constructor
  · intro h p hp
    rcases hp with ⟨B, Z, hcore, rfl⟩
    exact h B Z hcore
  · intro h B Z hcore
    exact h _ ⟨B, Z, hcore, rfl⟩

/-- The original sequence-based minimal graph is exactly closure of the very same realized core. -/
theorem hodgeMinimalGraph_iff_core_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A W : RealForm M k) (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W) :
    OperatorCandidates.HodgeMinimalGraph g.form μ A W ↔
      (realizeL2Form g μ (L2FormSpace.ofSection A hA),
        realizeL2Form g μ (L2FormSpace.ofSection W hW)) ∈
          closure (hodgeCoreRealizedGraph g μ k) := by
  classical
  let a : L2FormSpace g μ k := L2FormSpace.ofSection A hA
  let w : L2FormSpace g μ k := L2FormSpace.ofSection W hW
  constructor
  · rintro ⟨_, _, As, Ws, hc, ht⟩
    let us : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (As j) (hc j).2.2.2.1
    let vs : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (Ws j) (hc j).2.2.2.2.1
    have htA : Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_right (by positivity))
    have htW : Tendsto (fun j => formL2DistanceSq g.form μ (Ws j) W) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
        (fun _ => bot_le) (fun _ => le_add_of_nonneg_left (by positivity))
    have htu : Tendsto (fun j => realizeL2Form g μ (us j)) atTop (𝓝 (realizeL2Form g μ a)) :=
      (tendsto_realizeL2Form_iff g μ us a).mpr (by
        simpa only [us, a, L2FormSpace.toSection_ofSection] using htA)
    have htv : Tendsto (fun j => realizeL2Form g μ (vs j)) atTop (𝓝 (realizeL2Form g μ w)) :=
      (tendsto_realizeL2Form_iff g μ vs w).mpr (by
        simpa only [vs, w, L2FormSpace.toSection_ofSection] using htW)
    exact mem_closure_of_tendsto (htu.prodMk_nhds htv)
      (Filter.Eventually.of_forall fun j => ⟨As j, Ws j, hc j, rfl⟩)
  · intro h
    rcases mem_closure_iff_seq_limit.mp h with ⟨p, hp, ht⟩
    choose As Ws hc heq using hp
    let us : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (As j) (hc j).2.2.2.1
    let vs : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (Ws j) (hc j).2.2.2.2.1
    have htu : Tendsto (fun j => realizeL2Form g μ (us j)) atTop (𝓝 (realizeL2Form g μ a)) := by
      have hf := (continuous_fst.tendsto
        (realizeL2Form g μ (L2FormSpace.ofSection A hA),
          realizeL2Form g μ (L2FormSpace.ofSection W hW))).comp ht
      convert hf using 1
      funext j
      exact (congrArg Prod.fst (heq j)).symm
    have htv : Tendsto (fun j => realizeL2Form g μ (vs j)) atTop (𝓝 (realizeL2Form g μ w)) := by
      have hf := (continuous_snd.tendsto
        (realizeL2Form g μ (L2FormSpace.ofSection A hA),
          realizeL2Form g μ (L2FormSpace.ofSection W hW))).comp ht
      convert hf using 1
      funext j
      exact (congrArg Prod.snd (heq j)).symm
    have htA : Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
      simpa only [us, a, L2FormSpace.toSection_ofSection] using
        (tendsto_realizeL2Form_iff g μ us a).mp htu
    have htW : Tendsto (fun j => formL2DistanceSq g.form μ (Ws j) W) atTop (𝓝 0) := by
      simpa only [vs, w, L2FormSpace.toSection_ofSection] using
        (tendsto_realizeL2Form_iff g μ vs w).mp htv
    refine ⟨hA, hW, As, Ws, hc, ?_⟩
    simpa only [zero_add] using htA.add htW

theorem chartPt_continuousOn (x : M.Carrier) :
    ContinuousOn (chartPt x) (chartAt (ComplexVector n) x).source := by
  have h := continuousOn_extChartAt (I := ComplexModel n) x
  rw [extChartAt_source] at h
  with_unfolding_all
    exact h

theorem formInner_continuousOn_chart (g : SmoothMetric M) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (x : M.Carrier) :
    ContinuousOn (formInner g.form A B) (chartAt (ComplexVector n) x).source := by
  let F : ComplexVector n → ℝ := fun z => (Nat.factorial k : ℝ)⁻¹ *
    ∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
      formComponents A x z I * formComponents B x z J *
        ∏ r, (realMetricFn g.form x z)⁻¹ (I r) (J r)
  have hi (a b : RIdx n) : ContinuousOn (fun z => (realMetricFn g.form x z)⁻¹ a b)
      (chartTarget x) :=
    (continuous_apply b).comp_continuousOn
      ((continuous_apply a).comp_continuousOn (realMetricFn_inv_continuousOn g x))
  have hF : ContinuousOn F (chartTarget x) := by
    dsimp only [F]
    apply continuousOn_const.mul
    apply continuousOn_finsetSum
    intro I _
    apply continuousOn_finsetSum
    intro J _
    apply ((hA x I).continuousOn.mul (hB x J).continuousOn).mul
    apply continuousOn_finsetProd
    intro r _
    exact hi (I r) (J r)
  have hcomp : ContinuousOn (fun y => F (chartPt x y)) (chartAt (ComplexVector n) x).source :=
    hF.comp (chartPt_continuousOn x) (fun y hy =>
      (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy))
  apply hcomp.congr
  intro y hy
  exact formInner_in_fixed_chart g.form A B x y (by simpa only [extChartAt_source] using hy)

theorem formInner_continuous (g : SmoothMetric M) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) : Continuous (formInner g.form A B) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (formInner_continuousOn_chart g A B hA hB y).continuousAt
    ((chartAt (ComplexVector n) y).open_source.mem_nhds (mem_chart_source (ComplexVector n) y))

theorem formNormSq_continuous (g : SmoothMetric M) (A : RealForm M k)
    (hA : SmoothRealForm A) : Continuous (formNormSq g.form A) :=
  formInner_continuous g A A hA hA

theorem formNormSq_hasCompactSupport (g : HermitianField M) (A : RealForm M k)
    (hA : CompactlySupportedRealForm A) : HasCompactSupport (formNormSq g A) := by
  apply hA.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  change A x ≠ 0
  intro hzero
  exact hx ((formNormSq_eq_zero_iff g A x).mpr hzero)

theorem smoothRealForm_coefficient_aestronglyMeasurable (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier) (I : Fin k → RIdx n) :
    AEStronglyMeasurable (fun y => A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
  have hc : ContinuousOn (fun y => formComponents A x (chartPt x y) I)
      (chartAt (ComplexVector n) x).source :=
    (hA x I).continuousOn.comp (chartPt_continuousOn x) (fun y hy =>
      (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy))
  have hcont : ContinuousOn (fun y => A y (fun r => chartVec x y (realVec (I r))))
      (chartAt (ComplexVector n) x).source := by
    apply hc.congr
    intro y hy
    have hye : y ∈ (extChartAt (ComplexModel n) x).source := by
      simpa only [extChartAt_source] using hy
    simpa only [localRealBasis_apply] using (formComponents_apply_of_mem_source A x y hye I).symm
  exact hcont.aestronglyMeasurable (chartAt (ComplexVector n) x).open_source.measurableSet

/-- Every actual compactly supported smooth form belongs to the frozen L² space. -/
theorem smooth_compactlySupported_l2RealForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) : L2RealForm g.form μ A := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  have hI : Integrable (formNormSq g.form A) μ :=
    (formNormSq_continuous g A hA).integrable_of_hasCompactSupport
      (formNormSq_hasCompactSupport g.form A hcA)
  refine ⟨smoothRealForm_coefficient_aestronglyMeasurable μ A hA, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form A x)).mp hI.2


theorem smoothRealForm_zero : SmoothRealForm (0 : RealForm M k) := by
  intro x I
  simpa only [formComponents_zero, Pi.zero_apply] using
    (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ComplexVector n => (0 : ℝ)) (chartTarget x))

theorem smoothRealForm_add (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) : SmoothRealForm (A + B) := by
  intro x I
  simpa only [formComponents_add, Pi.add_apply] using (hA x I).add (hB x I)

theorem smoothRealForm_smul (c : ℝ) (A : RealForm M k)
    (hA : SmoothRealForm A) : SmoothRealForm (c • A) := by
  intro x I
  simpa only [formComponents_smul, Pi.smul_apply, smul_eq_mul] using (hA x I).const_smul c

theorem formComponents_multiplyRealForm (η : M.Carrier → ℝ) (A : RealForm M k)
    (x : M.Carrier) (z : ComplexVector n) (I : Fin k → RIdx n) :
    formComponents (multiplyRealForm η A) x z I =
      inChart x η z * formComponents A x z I := by
  simp only [formComponents, multiplyRealForm, inChart, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]

theorem smoothRealForm_multiply (η : M.Carrier → ℝ) (A : RealForm M k)
    (hη : SmoothFn η) (hA : SmoothRealForm A) : SmoothRealForm (multiplyRealForm η A) := by
  intro x I
  simpa only [formComponents_multiplyRealForm] using (hη x).mul (hA x I)

theorem compactlySupportedRealForm_add (A B : RealForm M k)
    (hA : CompactlySupportedRealForm A) (hB : CompactlySupportedRealForm B) :
    CompactlySupportedRealForm (A + B) := by
  apply (hA.union hB).of_isClosed_subset isClosed_closure
  rw [← closure_union]
  apply closure_mono
  intro x hx
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  exact hx (by simp only [Pi.add_apply, h.1, h.2, add_zero])

theorem compactlySupportedRealForm_multiply (η : M.Carrier → ℝ) (A : RealForm M k)
    (hA : CompactlySupportedRealForm A) : CompactlySupportedRealForm (multiplyRealForm η A) := by
  apply hA.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  change A x ≠ 0
  intro h
  exact hx (by simp only [multiplyRealForm, h, smul_zero])

theorem smoothRealForm_coefficient_differentiableAt (A : RealForm M k)
    (hA : SmoothRealForm A) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (I : Fin k → RIdx n) : DifferentiableAt ℝ (fun w => formComponents A x w I) z :=
  ((hA x I).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)

theorem rDeriv_add_at (f h : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (a : RIdx n) :
    rDeriv (fun w => f w + h w) z a = rDeriv f z a + rDeriv h z a := by
  simp only [rDeriv, fderiv_fun_add hf hh, ContinuousLinearMap.add_apply]

theorem rDeriv_mul_at (f h : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) (a : RIdx n) :
    rDeriv (fun w => f w * h w) z a = f z * rDeriv h z a + h z * rDeriv f z a := by
  simp only [rDeriv, fderiv_fun_mul hf hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem rDeriv_const_mul_at (c : ℝ) (f : ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : DifferentiableAt ℝ f z) (a : RIdx n) :
    rDeriv (fun w => c * f w) z a = c * rDeriv f z a := by
  simpa only [rDeriv, smul_eq_mul, ContinuousLinearMap.smul_apply] using
    DFunLike.congr_fun (fderiv_fun_const_smul hf c) (realVec a)


theorem covariantComponents_add_at (g : HermitianField M) (x : M.Carrier)
    (F H : FormComponents n k) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x (F + H) z a I =
      covariantComponents g x F z a I + covariantComponents g x H z a I := by
  simp only [covariantComponents, Pi.add_apply, rDeriv_add_at _ _ z (hF I) (hH I),
    mul_add, Finset.sum_add_distrib]
  ring

theorem covariantComponents_smul_at (g : HermitianField M) (x : M.Carrier)
    (c : ℝ) (F : FormComponents n k) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x (c • F) z a I = c * covariantComponents g x F z a I := by
  simp only [covariantComponents, Pi.smul_apply, smul_eq_mul, rDeriv_const_mul_at c _ z (hF I),
    mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem exteriorComponents_add_at (F H : FormComponents n k) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) (I : Fin (k + 1) → RIdx n) :
    exteriorComponents (F + H) z I = exteriorComponents F z I + exteriorComponents H z I := by
  simp only [exteriorComponents, Pi.add_apply,
    rDeriv_add_at _ _ z (hF _) (hH _), mul_add, Finset.sum_add_distrib]

theorem exteriorComponents_smul_at (c : ℝ) (F : FormComponents n k) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (I : Fin (k + 1) → RIdx n) :
    exteriorComponents (c • F) z I = c * exteriorComponents F z I := by
  simp only [exteriorComponents, Pi.smul_apply, smul_eq_mul,
    rDeriv_const_mul_at c _ z (hF _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem codifferentialComponents_add_at (g : HermitianField M) (x : M.Carrier)
    (F H : FormComponents n (k + 1)) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) (I : Fin k → RIdx n) :
    codifferentialComponents g x (F + H) z I =
      codifferentialComponents g x F z I + codifferentialComponents g x H z I := by
  simp only [codifferentialComponents, covariantComponents_add_at g x F H z hF hH,
    mul_add, Finset.sum_add_distrib, neg_add_rev]
  ring

theorem codifferentialComponents_smul_at (g : HermitianField M) (x : M.Carrier)
    (c : ℝ) (F : FormComponents n (k + 1)) (z : ComplexVector n)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (I : Fin k → RIdx n) :
    codifferentialComponents g x (c • F) z I = c * codifferentialComponents g x F z I := by
  simp only [codifferentialComponents, covariantComponents_smul_at g x c F z hF,
    Finset.mul_sum, mul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem covariantComponents_multiply_at (g : HermitianField M) (x : M.Carrier)
    (η : ComplexVector n → ℝ) (F : FormComponents n k) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x (fun w J => η w * F w J) z a I =
      η z * covariantComponents g x F z a I + rDeriv η z a * F z I := by
  have hs : (∑ r, ∑ b, christoffel g x z b a (I r) * (η z * F z (Function.update I r b))) =
      η z * ∑ r, ∑ b, christoffel g x z b a (I r) * F z (Function.update I r b) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [covariantComponents, rDeriv_mul_at η _ z hη (hF I), hs]
  ring

theorem exteriorComponents_multiply_at (η : ComplexVector n → ℝ) (F : FormComponents n k)
    (z : ComplexVector n) (hη : DifferentiableAt ℝ η z)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (I : Fin (k + 1) → RIdx n) :
    exteriorComponents (fun w J => η w * F w J) z I =
      η z * exteriorComponents F z I + ∑ r : Fin (k + 1),
        (-1 : ℝ) ^ r.val * rDeriv η z (I r) * F z (fun t => I (r.succAbove t)) := by
  simp only [exteriorComponents, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [rDeriv_mul_at η _ z hη (hF _)]
  ring

theorem codifferentialComponents_multiply_at (g : HermitianField M) (x : M.Carrier)
    (η : ComplexVector n → ℝ) (F : FormComponents n (k + 1)) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z) (I : Fin k → RIdx n) :
    codifferentialComponents g x (fun w J => η w * F w J) z I =
      η z * codifferentialComponents g x F z I -
        ∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b * rDeriv η z a * F z (Fin.cons b I) := by
  simp only [codifferentialComponents, covariantComponents_multiply_at g x η F z hη hF,
    mul_add, Finset.sum_add_distrib, mul_neg, Finset.mul_sum]
  have hs : (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
      (η z * covariantComponents g x F z a (Fin.cons b I))) =
      ∑ a, ∑ b, η z * ((realMetricFn g x z)⁻¹ a b *
        covariantComponents g x F z a (Fin.cons b I)) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs]
  simp only [mul_assoc]
  ring


theorem covariantComponents_zero (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x 0 z a I = 0 := by
  simp [covariantComponents, rDeriv]

theorem exteriorComponents_zero : exteriorComponents (0 : FormComponents n k) = 0 := by
  funext z I
  simp [exteriorComponents, rDeriv]

theorem codifferentialComponents_zero (g : HermitianField M) (x : M.Carrier) :
    codifferentialComponents (k := k) g x 0 = 0 := by
  funext z I
  simp only [codifferentialComponents, covariantComponents_zero, mul_zero, Finset.sum_const_zero,
    neg_zero, Pi.zero_apply]

theorem hodgeComponents_zero (g : HermitianField M) (x : M.Carrier) (k : ℕ) :
    hodgeComponents g x k 0 = 0 := by
  cases k with
  | zero => simp only [hodgeComponents, exteriorComponents_zero, codifferentialComponents_zero]
  | succ k =>
    funext z I
    simp only [hodgeComponents, exteriorComponents_zero, codifferentialComponents_zero,
      Pi.zero_apply, add_zero]

theorem covariantComponents_congr_nhds (g : HermitianField M) (x : M.Carrier)
    {F H : FormComponents n k} {z : ComplexVector n} (h : F =ᶠ[𝓝 z] H)
    (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x F z a I = covariantComponents g x H z a I := by
  have hI : (fun w => F w I) =ᶠ[𝓝 z] (fun w => H w I) :=
    h.mono fun w hw => congrFun hw I
  have hd : fderiv ℝ (fun w => F w I) z = fderiv ℝ (fun w => H w I) z := hI.fderiv_eq
  simp only [covariantComponents, rDeriv, hd, h.self_of_nhds]

theorem exteriorComponents_congr_nhds {F H : FormComponents n k} {z : ComplexVector n}
    (h : F =ᶠ[𝓝 z] H) : exteriorComponents F z = exteriorComponents H z := by
  funext I
  simp only [exteriorComponents, rDeriv]
  apply Finset.sum_congr rfl
  intro r _
  have hI : (fun w => F w (fun t => I (r.succAbove t))) =ᶠ[𝓝 z]
      (fun w => H w (fun t => I (r.succAbove t))) := h.mono fun w hw => congrFun hw _
  have hd : fderiv ℝ (fun w => F w (fun t => I (r.succAbove t))) z =
      fderiv ℝ (fun w => H w (fun t => I (r.succAbove t))) z := hI.fderiv_eq
  rw [hd]

theorem exteriorComponents_eventuallyEq {F H : FormComponents n k} {z : ComplexVector n}
    (h : F =ᶠ[𝓝 z] H) : exteriorComponents F =ᶠ[𝓝 z] exteriorComponents H :=
  h.eventuallyEq_nhds.mono fun _ hw => exteriorComponents_congr_nhds hw

theorem codifferentialComponents_congr_nhds (g : HermitianField M) (x : M.Carrier)
    {F H : FormComponents n (k + 1)} {z : ComplexVector n} (h : F =ᶠ[𝓝 z] H) :
    codifferentialComponents g x F z = codifferentialComponents g x H z := by
  funext I
  simp only [codifferentialComponents, covariantComponents_congr_nhds g x h]

theorem codifferentialComponents_eventuallyEq (g : HermitianField M) (x : M.Carrier)
    {F H : FormComponents n (k + 1)} {z : ComplexVector n} (h : F =ᶠ[𝓝 z] H) :
    codifferentialComponents g x F =ᶠ[𝓝 z] codifferentialComponents g x H :=
  h.eventuallyEq_nhds.mono fun _ hw => codifferentialComponents_congr_nhds g x hw

theorem hodgeComponents_congr_nhds (g : HermitianField M) (x : M.Carrier)
    {k : ℕ} {F H : FormComponents n k} {z : ComplexVector n} (h : F =ᶠ[𝓝 z] H) :
    hodgeComponents g x k F z = hodgeComponents g x k H z := by
  cases k with
  | zero => exact codifferentialComponents_congr_nhds g x (exteriorComponents_eventuallyEq h)
  | succ k =>
    funext I
    exact congrArg₂ (· + ·)
      (congrFun (exteriorComponents_congr_nhds (codifferentialComponents_eventuallyEq g x h)) I)
      (congrFun (codifferentialComponents_congr_nhds g x (exteriorComponents_eventuallyEq h)) I)

theorem formComponents_eventuallyEq_of_eventuallyEq {A B : RealForm M k}
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (h : ∀ᶠ y in 𝓝 (chartInv x z), A y = B y) :
    formComponents A x =ᶠ[𝓝 z] formComponents B x := by
  have hc : ContinuousAt (chartInv x) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  filter_upwards [hc.tendsto.eventually h] with w hw
  funext I
  simp only [formComponents, hw]

/-- A represented Hodge expression is local, without regularity assumptions on the input. -/
theorem representsHodge_eq_zero_of_eventuallyEq_zero (g : HermitianField M)
    {A W : RealForm M k} (hAW : RepresentsHodge g A W) (x : M.Carrier)
    (hA : ∀ᶠ y in 𝓝 x, A y = 0) : W x = 0 := by
  apply (formComponents_center_eq_zero_iff W x).mp
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hlocal : formComponents A x =ᶠ[𝓝 (chartPt x x)] 0 := by
    have hA' : ∀ᶠ y in 𝓝 (chartInv x (chartPt x x)), A y = (0 : RealForm M k) y := by
      simpa only [hx, Pi.zero_apply] using hA
    simpa only [formComponents_zero] using formComponents_eventuallyEq_of_eventuallyEq x ht hA'
  have hh := hodgeComponents_congr_nhds g x hlocal
  funext I
  rw [hAW x (chartPt x x) ht I]
  exact (congrFun hh I).trans (by rw [hodgeComponents_zero]; rfl)

/-- The support of the actual represented differential expression cannot grow. -/
theorem representsHodge_support_subset (g : HermitianField M) {A W : RealForm M k}
    (hAW : RepresentsHodge g A W) :
    closure {x | W x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hA : ∀ᶠ y in 𝓝 x, A y = 0 := by
    filter_upwards [isClosed_closure.compl_mem_nhds h] with y hy
    by_contra hne
    exact hy (subset_closure hne)
  exact hx (representsHodge_eq_zero_of_eventuallyEq_zero g hAW x hA)

theorem representsHodge_compactlySupported (g : HermitianField M) {A W : RealForm M k}
    (hAW : RepresentsHodge g A W) (hA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm W :=
  hA.of_isClosed_subset isClosed_closure (representsHodge_support_subset g hAW)

/-- On the actual smooth compact core, both frozen L² requirements are automatic. -/
theorem hodgeCorePair_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k) :
    OperatorCandidates.HodgeCorePair g.form μ A W ↔
      SmoothRealForm A ∧ CompactlySupportedRealForm A ∧ SmoothRealForm W ∧
        RepresentsHodge g.form A W := by
  constructor
  · rintro ⟨hA, hcA, hW, _, _, hAW⟩
    exact ⟨hA, hcA, hW, hAW⟩
  · rintro ⟨hA, hcA, hW, hAW⟩
    exact ⟨hA, hcA, hW, smooth_compactlySupported_l2RealForm g μ hμ A hA hcA,
      smooth_compactlySupported_l2RealForm g μ hμ W hW
        (representsHodge_compactlySupported g.form hAW hcA), hAW⟩


/-- Contraction by the actual inverse Gram matrix recovers any coordinate covector. -/
theorem symmetricMatrix_inverse_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsSymm) (hunit : IsUnit G.det) (X : ι → ℝ) (b : ι) :
    (∑ c, ∑ d, G⁻¹ c d * X d * G c b) = X b := by
  calc
    _ = (G.mulVec (G⁻¹.mulVec X)) b := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [hG.apply c b]
      ring
    _ = X b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunit, Matrix.one_mulVec]

/-- Lowering the output index of the computed Levi-Civita symbol. -/
theorem christoffel_lower_index (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a i j : RIdx n) :
    (∑ c, christoffel g x z c a i * realMetricFn g x z c j) =
      (1 / 2 : ℝ) * (rDeriv (fun w => realMetricFn g x w i j) z a +
        rDeriv (fun w => realMetricFn g x w a j) z i -
        rDeriv (fun w => realMetricFn g x w a i) z j) := by
  let X : RIdx n → ℝ := fun d => rDeriv (fun w => realMetricFn g x w i d) z a +
    rDeriv (fun w => realMetricFn g x w a d) z i -
    rDeriv (fun w => realMetricFn g x w a i) z d
  have hs : (∑ c, christoffel g x z c a i * realMetricFn g x z c j) =
      (1 / 2 : ℝ) * ∑ c, ∑ d,
        (realMetricFn g x z)⁻¹ c d * X d * realMetricFn g x z c j := by
    simp only [christoffel, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    dsimp only [X]
    ring
  rw [hs, symmetricMatrix_inverse_contraction (realMetricFn g x z)
    (realMetricFn_isSymm g x z)
    ((Matrix.isUnit_iff_isUnit_det _).mp (realMetricFn_posDef_of_mem_target g x hz).isUnit)]

/-- The computed metric has zero covariant derivative in every actual chart. -/
theorem realMetricFn_covariant_derivative (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a i j : RIdx n) :
    rDeriv (fun w => realMetricFn g x w i j) z a =
      (∑ c, christoffel g x z c a i * realMetricFn g x z c j) +
        ∑ c, christoffel g x z c a j * realMetricFn g x z c i := by
  rw [christoffel_lower_index g x hz a i j, christoffel_lower_index g x hz a j i,
    L18Aux.rDeriv_realMetricFn_symm g x z a j i]
  ring

/-- Matrix of the actual connection coefficients for one coordinate direction. -/
def christoffelMatrix (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ := fun c b => christoffel g x z c a b

def metricDerivativeMatrix (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a : RIdx n) : Matrix (RIdx n) (RIdx n) ℝ :=
  fun i j => rDeriv (fun w => realMetricFn g x w i j) z a

theorem metricDerivativeMatrix_eq_connection (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
    metricDerivativeMatrix g x z a =
      (christoffelMatrix g x z a).transpose * realMetricFn g x z +
        realMetricFn g x z * christoffelMatrix g x z a := by
  ext i j
  simp only [metricDerivativeMatrix, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, christoffelMatrix]
  rw [realMetricFn_covariant_derivative g x hz]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [(realMetricFn_isSymm g x z).apply i c]
  ring


theorem inverseMetric_derivative_matrix (g : SmoothMetric M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
    (Matrix.of fun i j => rDeriv (fun w => (realMetricFn g.form x w)⁻¹ i j) z a) =
      -((realMetricFn g.form x z)⁻¹ * metricDerivativeMatrix g.form x z a *
        (realMetricFn g.form x z)⁻¹) := by
  ext i j
  exact L18Aux.fderiv_matrix_inv_entry
    (isOpen_extChartAt_target (I := ComplexModel n) x)
    (L18Aux.metricSmooth_of_smoothMetric g x)
    (fun w hw => ne_of_gt (realMetricFn_posDef_of_mem_target g.form x hw).det_pos)
    hz (realVec a) i j

/-- The inverse-metric derivative is the negative action of the computed connection. -/
theorem inverseMetric_derivative_matrix_eq_connection (g : SmoothMetric M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
    (Matrix.of fun i j => rDeriv (fun w => (realMetricFn g.form x w)⁻¹ i j) z a) =
      -((realMetricFn g.form x z)⁻¹ * (christoffelMatrix g.form x z a).transpose) -
        christoffelMatrix g.form x z a * (realMetricFn g.form x z)⁻¹ := by
  let G := realMetricFn g.form x z
  let C := christoffelMatrix g.form x z a
  have hunit : IsUnit G.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (realMetricFn_posDef_of_mem_target g.form x hz).isUnit
  have h1 : G⁻¹ * (C.transpose * G) * G⁻¹ = G⁻¹ * C.transpose := by
    rw [← Matrix.mul_assoc G⁻¹ C.transpose G, Matrix.mul_nonsing_inv_cancel_right G _ hunit]
  have h2 : G⁻¹ * (G * C) * G⁻¹ = C * G⁻¹ := by
    rw [Matrix.nonsing_inv_mul_cancel_left G C hunit]
  rw [inverseMetric_derivative_matrix g x hz a,
    metricDerivativeMatrix_eq_connection g.form x hz a]
  change -(G⁻¹ * (C.transpose * G + G * C) * G⁻¹) =
    -(G⁻¹ * C.transpose) - C * G⁻¹
  rw [Matrix.mul_add, Matrix.add_mul, h1, h2, neg_add, sub_eq_add_neg]

/-- Zero covariant derivative of the inverse metric, in the root coordinate convention. -/
theorem realMetricFn_inverse_covariant_derivative (g : SmoothMetric M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a i j : RIdx n) :
    rDeriv (fun w => (realMetricFn g.form x w)⁻¹ i j) z a =
      -(∑ c, (realMetricFn g.form x z)⁻¹ i c * christoffel g.form x z j a c) -
        ∑ c, christoffel g.form x z i a c * (realMetricFn g.form x z)⁻¹ c j := by
  have h := congrArg (fun A : Matrix (RIdx n) (RIdx n) ℝ => A i j)
    (inverseMetric_derivative_matrix_eq_connection g x hz a)
  simpa only [Matrix.of_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply,
    Matrix.transpose_apply, christoffelMatrix] using h

theorem christoffel_symmetric_lower (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (c a b : RIdx n) :
    christoffel g x z c a b = christoffel g x z c b a := by
  simp only [christoffel]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [L18Aux.rDeriv_realMetricFn_symm g x z d a b]
  ring


/-- Exchange one tensor index with the additional contraction index. -/
def swapFunctionSlot {ι α : Type*} [DecidableEq ι] (r : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) where
  toFun p := (Function.update p.1 r p.2, p.1 r)
  invFun p := (Function.update p.1 r p.2, p.1 r)
  left_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i = r
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    · simp
  right_inv p := by
    apply Prod.ext
    · funext i
      by_cases hi : i = r
      · subst i
        simp
      · simp [Function.update_of_ne hi]
    · simp

theorem swapFunctionSlot_apply {ι α : Type*} [DecidableEq ι] (r : ι) (I : ι → α) (c : α) :
    swapFunctionSlot r (I, c) = (Function.update I r c, I r) := rfl

theorem sum_swapFunctionSlot {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (r : ι) (h : (ι → α) → α → ℝ) :
    (∑ I, ∑ c, h I c) = ∑ I, ∑ c, h (Function.update I r c) (I r) := by
  classical
  simpa only [Fintype.sum_prod_type, swapFunctionSlot_apply] using
    ((swapFunctionSlot (α := α) r).sum_comp (fun p => h p.1 p.2)).symm

theorem tensorProduct_update_left {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix α α ℝ) (I J : ι → α) (r : ι) (c : α) :
    (∏ s, B (Function.update I r c s) (J s)) =
      B c (J r) * ∏ s ∈ Finset.univ.erase r, B (I s) (J s) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun s => B (Function.update I r c s) (J s)) (Finset.mem_univ r)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]

/-- The finite index exchange for the left connection action in the tensor metric. -/
theorem tensorContraction_slot_left {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (B C : Matrix α α ℝ) (F H : (ι → α) → ℝ) (r : ι) :
    (∑ I, ∑ c, ∑ J, C c (I r) * F (Function.update I r c) * H J *
      ∏ s, B (I s) (J s)) =
    ∑ I, ∑ c, ∑ J, F I * H J * C (I r) c * B c (J r) *
      ∏ s ∈ Finset.univ.erase r, B (I s) (J s) := by
  classical
  rw [sum_swapFunctionSlot r (fun I c => ∑ J,
    C c (I r) * F (Function.update I r c) * H J * ∏ s, B (I s) (J s))]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro J _
  rw [tensorProduct_update_left]
  ring

/-- Directional product rule with the omitted factor retained, including zero factors. -/
theorem rDeriv_finsetProd_at {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (a : RIdx n) :
    rDeriv (fun w => ∏ i ∈ s, f i w) z a =
      ∑ i ∈ s, rDeriv (f i) z a * ∏ j ∈ s.erase i, f j z := by
  simp only [rDeriv, fderiv_finsetProd hf, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _


theorem tensorContraction_slot_right {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (B C : Matrix α α ℝ) (F H : (ι → α) → ℝ) (r : ι) :
    (∑ J, ∑ c, ∑ I, C c (J r) * F I * H (Function.update J r c) *
      ∏ s, B (I s) (J s)) =
    ∑ J, ∑ c, ∑ I, F I * H J * B (I r) c * C (J r) c *
      ∏ s ∈ Finset.univ.erase r, B (I s) (J s) := by
  classical
  rw [sum_swapFunctionSlot r (fun J c => ∑ I,
    C c (J r) * F I * H (Function.update J r c) * ∏ s, B (I s) (J s))]
  simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro I _
  have hprod : (∏ s, B (I s) (Function.update J r c s)) =
      B (I r) c * ∏ s ∈ Finset.univ.erase r, B (I s) (J s) :=
    tensorProduct_update_left B.transpose J I r c
  rw [hprod]
  ring

theorem rDeriv_finsetSum_at {ι : Type*} (s : Finset ι)
    (f : ι → ComplexVector n → ℝ) (z : ComplexVector n)
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) (a : RIdx n) :
    rDeriv (fun w => ∑ i ∈ s, f i w) z a = ∑ i ∈ s, rDeriv (f i) z a := by
  simp only [rDeriv, fderiv_fun_sum hf, ContinuousLinearMap.sum_apply]

/-- Derivative of the actual tensor-power inverse metric, without division by entries. -/
theorem tensorMatrix_inverseMetric_derivative (g : SmoothMetric M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n)
    (I J : Fin k → RIdx n) :
    rDeriv (fun w => tensorMatrix (realMetricFn g.form x w)⁻¹ k I J) z a =
      ∑ r, (-(∑ c, (realMetricFn g.form x z)⁻¹ (I r) c * christoffel g.form x z (J r) a c) -
          ∑ c, christoffel g.form x z (I r) a c * (realMetricFn g.form x z)⁻¹ c (J r)) *
        ∏ s ∈ Finset.univ.erase r, (realMetricFn g.form x z)⁻¹ (I s) (J s) := by
  have hd (r : Fin k) (_ : r ∈ Finset.univ) :
      DifferentiableAt ℝ (fun w => (realMetricFn g.form x w)⁻¹ (I r) (J r)) z :=
    ((L18Aux.realMetricFn_inverse_contDiffOn g x (I r) (J r)).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  change rDeriv (fun w => ∏ r, (realMetricFn g.form x w)⁻¹ (I r) (J r)) z a = _
  rw [rDeriv_finsetProd_at Finset.univ _ z hd]
  simp_rw [realMetricFn_inverse_covariant_derivative g x hz]


/-- The concrete finite coefficient pairing underlying the root form metric. -/
def tensorCoefficientPairing {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H : (ι → α) → ℝ) : ℝ :=
  ∑ I, ∑ J, F I * H J * ∏ r, B (I r) (J r)

/-- The actual connection action on all covariant tensor slots. -/
def tensorConnectionAction {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (C : Matrix α α ℝ) (F : (ι → α) → ℝ) (I : ι → α) : ℝ :=
  ∑ r, ∑ c, C c (I r) * F (Function.update I r c)

theorem tensorCoefficientPairing_transpose {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H : (ι → α) → ℝ) :
    tensorCoefficientPairing B F H = tensorCoefficientPairing B.transpose H F := by
  classical
  simp only [tensorCoefficientPairing, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem tensorCoefficientPairing_connection_left {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B C : Matrix α α ℝ) (F H : (ι → α) → ℝ) :
    tensorCoefficientPairing B (tensorConnectionAction C F) H =
      ∑ r, ∑ I, ∑ J, F I * H J * (∑ c, C (I r) c * B c (J r)) *
        ∏ s ∈ Finset.univ.erase r, B (I s) (J s) := by
  classical
  let T (I J : ι → α) (r : ι) (c : α) : ℝ :=
    C c (I r) * F (Function.update I r c) * H J * ∏ s, B (I s) (J s)
  have hL : tensorCoefficientPairing B (tensorConnectionAction C F) H =
      ∑ r, ∑ I, ∑ c, ∑ J, T I J r c := by
    simp only [tensorCoefficientPairing, tensorConnectionAction, Finset.sum_mul]
    change (∑ I, ∑ J, ∑ r, ∑ c, T I J r c) = _
    have hi (I : ι → α) : (∑ J, ∑ r, ∑ c, T I J r c) =
        ∑ r, ∑ c, ∑ J, T I J r c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    simp_rw [hi]
    rw [Finset.sum_comm]
  rw [hL]
  apply Finset.sum_congr rfl
  intro r _
  change (∑ I, ∑ c, ∑ J, C c (I r) * F (Function.update I r c) * H J *
    ∏ s, B (I s) (J s)) = _
  rw [tensorContraction_slot_left B C F H r]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem tensorCoefficientPairing_connection_right {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B C : Matrix α α ℝ) (F H : (ι → α) → ℝ) :
    tensorCoefficientPairing B F (tensorConnectionAction C H) =
      ∑ r, ∑ I, ∑ J, F I * H J * (∑ c, B (I r) c * C (J r) c) *
        ∏ s ∈ Finset.univ.erase r, B (I s) (J s) := by
  classical
  rw [tensorCoefficientPairing_transpose B F (tensorConnectionAction C H),
    tensorCoefficientPairing_connection_left B.transpose C H F]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  simp only [Matrix.transpose_apply]
  have hs : (∑ c, C (J r) c * B (I r) c) = ∑ c, B (I r) c * C (J r) c := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hs]
  ring


theorem tensorCoefficientPairing_sub_left {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H K : (ι → α) → ℝ) :
    tensorCoefficientPairing B (F - H) K =
      tensorCoefficientPairing B F K - tensorCoefficientPairing B H K := by
  simp only [tensorCoefficientPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem tensorCoefficientPairing_sub_right {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H K : (ι → α) → ℝ) :
    tensorCoefficientPairing B F (H - K) =
      tensorCoefficientPairing B F H - tensorCoefficientPairing B F K := by
  simp only [tensorCoefficientPairing, Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem sum_three_rotate {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (f : ι → κ → τ → ℝ) : (∑ i, ∑ j, ∑ l, f i j l) = ∑ j, ∑ l, ∑ i, f i j l := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- The directional product rule for the full coefficient pairing, with all
metric-factor derivatives exposed as finite sums. -/
theorem rDeriv_tensorCoefficientPairing_at {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : ComplexVector n → Matrix α α ℝ)
    (F H : ComplexVector n → (ι → α) → ℝ) (z : ComplexVector n)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) (a : RIdx n) :
    rDeriv (fun w => tensorCoefficientPairing (B w) (F w) (H w)) z a =
      ∑ I, ∑ J,
        ((rDeriv (fun w => F w I) z a * H z J + F z I * rDeriv (fun w => H w J) z a) *
          (∏ r, B z (I r) (J r)) +
        F z I * H z J * (∑ r, rDeriv (fun w => B w (I r) (J r)) z a *
          ∏ s ∈ Finset.univ.erase r, B z (I s) (J s))) := by
  classical
  have hprod (I J : ι → α) :
      DifferentiableAt ℝ (fun w => ∏ r, B w (I r) (J r)) z :=
    (HasFDerivAt.finsetProd (fun r _ => (hB (I r) (J r)).hasFDerivAt)).differentiableAt
  have hterm (I J : ι → α) : DifferentiableAt ℝ
      (fun w => F w I * H w J * ∏ r, B w (I r) (J r)) z :=
    ((hF I).mul (hH J)).mul (hprod I J)
  have hsum (I : ι → α) : DifferentiableAt ℝ
      (fun w => ∑ J, F w I * H w J * ∏ r, B w (I r) (J r)) z :=
    DifferentiableAt.fun_sum (fun J _ => hterm I J)
  change rDeriv (fun w => ∑ I, ∑ J, F w I * H w J * ∏ r, B w (I r) (J r)) z a = _
  rw [rDeriv_finsetSum_at Finset.univ _ z (fun I _ => hsum I) a]
  apply Finset.sum_congr rfl
  intro I _
  rw [rDeriv_finsetSum_at Finset.univ _ z (fun J _ => hterm I J) a]
  apply Finset.sum_congr rfl
  intro J _
  rw [rDeriv_mul_at (fun w => F w I * H w J) (fun w => ∏ r, B w (I r) (J r))
      z ((hF I).mul (hH J)) (hprod I J) a,
    rDeriv_mul_at (fun w => F w I) (fun w => H w J) z (hF I) (hH J) a,
    rDeriv_finsetProd_at Finset.univ (fun r w => B w (I r) (J r)) z
      (fun r _ => hB (I r) (J r)) a]
  ring


/-- The full tensor metric is preserved by the actual computed connection.
Only the first derivatives used in the displayed formula are required. -/
theorem tensorCoefficientPairing_covariant_derivative (g : SmoothMetric M) (x : M.Carrier)
    (F H : FormComponents n k) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) (a : RIdx n) :
    rDeriv (fun w => tensorCoefficientPairing (realMetricFn g.form x w)⁻¹ (F w) (H w)) z a =
      tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
        (fun I => covariantComponents g.form x F z a I) (H z) +
      tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
        (fun I => covariantComponents g.form x H z a I) := by
  classical
  let B := (realMetricFn g.form x z)⁻¹
  let C := christoffelMatrix g.form x z a
  let dF : (Fin k → RIdx n) → ℝ := fun I => rDeriv (fun w => F w I) z a
  let dH : (Fin k → RIdx n) → ℝ := fun I => rDeriv (fun w => H w I) z a
  have hB (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form x w)⁻¹ i j) z :=
    ((L18Aux.realMetricFn_inverse_contDiffOn g x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hmetric (i j : RIdx n) :
      rDeriv (fun w => (realMetricFn g.form x w)⁻¹ i j) z a =
        -(∑ c, B i c * C j c) - ∑ c, C i c * B c j :=
    realMetricFn_inverse_covariant_derivative g x hz a i j
  have hcF : (fun I => covariantComponents g.form x F z a I) =
      dF - tensorConnectionAction C (F z) := rfl
  have hcH : (fun I => covariantComponents g.form x H z a I) =
      dH - tensorConnectionAction C (H z) := rfl
  rw [rDeriv_tensorCoefficientPairing_at _ F H z hB hF hH a, hcF, hcH,
    tensorCoefficientPairing_sub_left, tensorCoefficientPairing_sub_right]
  change _ = tensorCoefficientPairing B dF (H z) -
    tensorCoefficientPairing B (tensorConnectionAction C (F z)) (H z) +
    (tensorCoefficientPairing B (F z) dH -
      tensorCoefficientPairing B (F z) (tensorConnectionAction C (H z)))
  rw [tensorCoefficientPairing_connection_left, tensorCoefficientPairing_connection_right]
  rw [sum_three_rotate (fun (r : Fin k) (I J : Fin k → RIdx n) =>
    F z I * H z J * (∑ c, C (I r) c * B c (J r)) *
      ∏ s ∈ Finset.univ.erase r, B (I s) (J s))]
  rw [sum_three_rotate (fun (r : Fin k) (I J : Fin k → RIdx n) =>
    F z I * H z J * (∑ c, B (I r) c * C (J r) c) *
      ∏ s ∈ Finset.univ.erase r, B (I s) (J s))]
  simp_rw [hmetric]
  simp only [tensorCoefficientPairing, dF, dH, sub_eq_add_neg, mul_add, add_mul,
    mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, mul_assoc]
  ring


theorem differentiableAt_tensorCoefficientPairing {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : ComplexVector n → Matrix α α ℝ)
    (F H : ComplexVector n → (ι → α) → ℝ) (z : ComplexVector n)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w => B w i j) z)
    (hF : ∀ I, DifferentiableAt ℝ (fun w => F w I) z)
    (hH : ∀ I, DifferentiableAt ℝ (fun w => H w I) z) :
    DifferentiableAt ℝ (fun w => tensorCoefficientPairing (B w) (F w) (H w)) z := by
  classical
  apply DifferentiableAt.fun_sum
  intro I _
  apply DifferentiableAt.fun_sum
  intro J _
  apply ((hF I).mul (hH J)).mul
  exact (HasFDerivAt.finsetProd (fun r _ => (hB (I r) (J r)).hasFDerivAt)).differentiableAt

theorem formInner_chartInv_eq_tensorPairing (g : HermitianField M) (A B : RealForm M k)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formInner g A B (chartInv x z) = (Nat.factorial k : ℝ)⁻¹ *
      tensorCoefficientPairing (realMetricFn g x z)⁻¹ (formComponents A x z) (formComponents B x z) := by
  have hy : chartInv x z ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hz
  have h := formInner_in_fixed_chart g A B x (chartInv x z) hy
  have hinv : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  simpa only [hinv, tensorCoefficientPairing] using h

/-- The actual root inner product in any fixed chart differentiates by the
computed covariant derivative, in every form degree. -/
theorem formInner_chart_covariant_derivative (g : SmoothMetric M) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (fun w => formInner g.form A B (chartInv x w)) z a =
      (Nat.factorial k : ℝ)⁻¹ *
        (tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
          (fun I => covariantComponents g.form x (formComponents A x) z a I)
          (formComponents B x z) +
        tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (formComponents A x z)
          (fun I => covariantComponents g.form x (formComponents B x) z a I)) := by
  have hF (I : Fin k → RIdx n) := smoothRealForm_coefficient_differentiableAt A hA x hz I
  have hH (I : Fin k → RIdx n) := smoothRealForm_coefficient_differentiableAt B hB x hz I
  have hi (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form x w)⁻¹ i j) z :=
    ((L18Aux.realMetricFn_inverse_contDiffOn g x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hp := differentiableAt_tensorCoefficientPairing
    (fun w => (realMetricFn g.form x w)⁻¹) (formComponents A x) (formComponents B x) z hi hF hH
  have hloc : (fun w => formInner g.form A B (chartInv x w)) =ᶠ[𝓝 z]
      (fun w => (Nat.factorial k : ℝ)⁻¹ * tensorCoefficientPairing
        (realMetricFn g.form x w)⁻¹ (formComponents A x w) (formComponents B x w)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact formInner_chartInv_eq_tensorPairing g.form A B x hw
  have hd := DFunLike.congr_fun (hloc.fderiv_eq (𝕜 := ℝ)) (realVec a)
  change rDeriv (fun w => formInner g.form A B (chartInv x w)) z a =
    rDeriv (fun w => (Nat.factorial k : ℝ)⁻¹ * tensorCoefficientPairing
      (realMetricFn g.form x w)⁻¹ (formComponents A x w) (formComponents B x w)) z a at hd
  rw [hd, rDeriv_const_mul_at _ _ z hp a,
    tensorCoefficientPairing_covariant_derivative g x _ _ hz hF hH a]


/-- Coefficients of an actual continuous alternating tensor in the fixed real model basis. -/
def modelFormCoefficientMap (n k : ℕ) :
    ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin k → RIdx n) → ℝ) where
  toFun P := fun I => P (fun r => realVec (I r))
  map_add' P Q := by funext I; simp
  map_smul' c P := by funext I; simp

theorem modelFormCoefficientMap_apply (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (I : Fin k → RIdx n) : modelFormCoefficientMap n k P I = P (fun r => realVec (I r)) := rfl

theorem modelFormCoefficientMap_injective (n k : ℕ) :
    Function.Injective (modelFormCoefficientMap n k) := by
  intro P Q h
  have hAlt : P.toAlternatingMap = Q.toAlternatingMap := by
    apply (realModelBasis n).ext_alternating
    intro I _
    have hc := congrFun h I
    change P (fun r => realVec (I r)) = Q (fun r => realVec (I r)) at hc
    simpa [realModelBasis_apply] using hc
  apply ContinuousAlternatingMap.ext
  intro v
  exact congrArg (fun f : (ComplexVector n) [⋀^Fin k]→ₗ[ℝ] ℝ => f v) hAlt

/-- A genuine continuous linear reconstruction; its left-inverse identity is proved below. -/
def modelFormReconstruction (n k : ℕ) :
    ((Fin k → RIdx n) → ℝ) →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (modelFormCoefficientMap n k).leftInverse.toContinuousLinearMap

theorem modelFormReconstruction_coefficient (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelFormReconstruction n k (modelFormCoefficientMap n k P) = P :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (modelFormCoefficientMap_injective n k)) P

/-- Coefficient smoothness is exactly smoothness of the actual model tensor field. -/
theorem modelForm_contDiffOn_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (s : Set E) :
    ContDiffOn ℝ ∞ F s ↔
      ∀ I : Fin k → RIdx n, ContDiffOn ℝ ∞ (fun z => F z (fun r => realVec (I r))) s := by
  constructor
  · intro h I
    exact (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).contDiff.comp_contDiffOn h
  · intro h
    have hc : ContDiffOn ℝ ∞ (fun z => modelFormCoefficientMap n k (F z)) s :=
      contDiffOn_pi.mpr h
    have hr := (modelFormReconstruction n k).contDiff.comp_contDiffOn hc
    apply hr.congr
    intro z _
    exact (modelFormReconstruction_coefficient (F z)).symm

def chartRealContinuousLinearMap (x y : M.Carrier) :
    ComplexVector n →L[ℝ] TangentVector M y :=
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x).symm
    (chartPt x y)).restrictScalars ℝ

theorem chartRealContinuousLinearMap_apply (x y : M.Carrier) (v : ComplexVector n) :
    chartRealContinuousLinearMap x y v = chartVec x y v := rfl

/-- The actual alternating tensor field in one fixed chart. -/
def chartForm (A : RealForm M k) (x : M.Carrier) :
    ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ :=
  fun z => (A (chartInv x z)).compContinuousLinearMap
    (chartRealContinuousLinearMap x (chartInv x z))

theorem chartForm_apply_basis (A : RealForm M k) (x : M.Carrier)
    (z : ComplexVector n) (I : Fin k → RIdx n) :
    chartForm A x z (fun r => realVec (I r)) = formComponents A x z I := rfl

theorem chartForm_contDiffOn (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (chartForm A x) (chartTarget x) := by
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I
  simpa only [chartForm_apply_basis] using hA x I

/-- Mathlib's actual exterior derivative has exactly the frozen omission/sign formula. -/
theorem chartForm_extDeriv_apply (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin (k + 1) → RIdx n) :
    extDeriv (chartForm A x) z (fun r => realVec (I r)) =
      exteriorComponents (formComponents A x) z I := by
  have hd := ((chartForm_contDiffOn A hA x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  rw [extDeriv_apply hd]
  simp only [exteriorComponents]
  apply Finset.sum_congr rfl
  intro r _
  have heq : (fun w => chartForm A x w (r.removeNth (fun s => realVec (I s)))) =
      (fun w => formComponents A x w (fun s => I (r.succAbove s))) := by
    funext w
    rfl
  rw [heq]
  simp [rDeriv, zsmul_eq_mul]


theorem chartForm_extDeriv_contDiffOn (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (extDeriv (chartForm A x)) (chartTarget x) := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ (chartForm A x)) (chartTarget x) :=
    (chartForm_contDiffOn A hA x).fderiv_of_isOpen
      (isOpen_extChartAt_target (I := ComplexModel n) x) (by simp)
  change ContDiffOn ℝ ∞
    (fun z => ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (ComplexVector n) ℝ
      (fderiv ℝ (chartForm A x) z)) (chartTarget x)
  simpa only [Function.comp_def] using
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (ComplexVector n) ℝ).contDiff.comp_contDiffOn hd

theorem exteriorComponents_contDiffOn (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier)
    (I : Fin (k + 1) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => exteriorComponents (formComponents A x) z I) (chartTarget x) := by
  have h := (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).contDiff.comp_contDiffOn (chartForm_extDeriv_contDiffOn A hA x)
  apply h.congr
  intro z hz
  exact (chartForm_extDeriv_apply A hA x hz I).symm


theorem chartTransition_real_fderiv (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (v : ComplexVector n) :
    fderiv ℝ (fun t => chartPt b (chartInv a t)) z v =
      tangentCoords b (chartInv a z) (chartVec a (chartInv a z) v) := by
  have hd : DifferentiableAt ℂ (fun t => chartPt b (chartInv a t)) z :=
    (L18Aux.chartTransition_contDiffAt a b hz hy).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  exact L18Aux.chartTransition_fderiv a b hz hy v

/-- The actual alternating field transforms by the actual real derivative of a chart change. -/
theorem chartForm_pullback (A : RealForm M k) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    chartForm A a z = (chartForm A b (chartPt b (chartInv a z))).compContinuousLinearMap
      (fderiv ℝ (fun t => chartPt b (chartInv a t)) z) := by
  have hinv : chartInv b (chartPt b (chartInv a z)) = chartInv a z :=
    (extChartAt (ComplexModel n) b).left_inv hy
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, chartRealContinuousLinearMap_apply]
  rw [hinv]
  congr 1
  funext i
  rw [chartTransition_real_fderiv a b hz hy (v i),
    L12Aux.chartVec_tangentCoords b (chartInv a z) hy]

theorem chartForm_pullback_eventuallyEq (A : RealForm M k) (a b : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    chartForm A a =ᶠ[𝓝 z] (fun t =>
      (chartForm A b (chartPt b (chartInv a t))).compContinuousLinearMap
        (fderiv ℝ (fun w => chartPt b (chartInv a w)) t)) := by
  have hi : ContinuousAt (chartInv a) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz,
    hi.tendsto.eventually ((isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hy)]
    with t ht hbt
  exact chartForm_pullback A a b ht hbt

/-- Exterior differentiation of the actual chart field is invariant under every chart change. -/
theorem chartForm_extDeriv_pullback (A : RealForm M k) (hA : SmoothRealForm A)
    (a b : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) :
    extDeriv (chartForm A a) z =
      (extDeriv (chartForm A b) (chartPt b (chartInv a z))).compContinuousLinearMap
        (fderiv ℝ (fun t => chartPt b (chartInv a t)) z) := by
  have htarget : chartPt b (chartInv a z) ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hy
  have hF : DifferentiableAt ℝ (chartForm A b) (chartPt b (chartInv a z)) :=
    ((chartForm_contDiffOn A hA b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) b).mem_nhds htarget)).differentiableAt (by simp)
  have hT : ContDiffAt ℝ ∞ (fun t => chartPt b (chartInv a t)) z :=
    (L18Aux.chartTransition_contDiffAt a b hz hy).restrict_scalars ℝ
  exact (chartForm_pullback_eventuallyEq A a b hz hy).extDeriv_eq.trans
    (extDeriv_pullback hF hT (by simp))


def tangentCoordsRealContinuousLinearMap (x y : M.Carrier) :
    TangentVector M y →L[ℝ] ComplexVector n :=
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) x) y).restrictScalars ℝ

theorem tangentCoordsRealContinuousLinearMap_apply (x y : M.Carrier) (v : TangentVector M y) :
    tangentCoordsRealContinuousLinearMap x y v = tangentCoords x y v := rfl

/-- The exterior derivative as an actual form on the original manifold. -/
def exteriorRealForm (A : RealForm M k) : RealForm M (k + 1) :=
  fun y => (extDeriv (chartForm A y) (chartPt y y)).compContinuousLinearMap
    (tangentCoordsRealContinuousLinearMap y y)

/-- The constructed derivative satisfies the frozen reconstruction relation on every chart target. -/
theorem exteriorRealForm_represents (A : RealForm M k) (hA : SmoothRealForm A) :
    RepresentsExterior A (exteriorRealForm A) := by
  intro x z hz I
  let y := chartInv x z
  have hy : y ∈ (extChartAt (ComplexModel n) y).source := mem_extChartAt_source y
  have hp := chartForm_extDeriv_pullback A hA x y hz hy
  calc
    formComponents (exteriorRealForm A) x z I =
      extDeriv (chartForm A y) (chartPt y y)
        (fun r => tangentCoords y y (chartVec x y (realVec (I r)))) := rfl
    _ = extDeriv (chartForm A x) z (fun r => realVec (I r)) := by
      rw [hp]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
      congr 1
      funext r
      exact (chartTransition_real_fderiv x y hz hy (realVec (I r))).symm
    _ = exteriorComponents (formComponents A x) z I := chartForm_extDeriv_apply A hA x hz I

theorem representsExterior_smooth {A : RealForm M k} {B : RealForm M (k + 1)}
    (hA : SmoothRealForm A) (hAB : RepresentsExterior A B) : SmoothRealForm B := by
  intro x I
  apply (exteriorComponents_contDiffOn A hA x I).congr
  intro z hz
  exact hAB x z hz I

theorem exteriorRealForm_smooth (A : RealForm M k) (hA : SmoothRealForm A) :
    SmoothRealForm (exteriorRealForm A) :=
  representsExterior_smooth hA (exteriorRealForm_represents A hA)

theorem representsExterior_chartForm {A : RealForm M k} {B : RealForm M (k + 1)}
    (hA : SmoothRealForm A) (hAB : RepresentsExterior A B) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm B x z = extDeriv (chartForm A x) z := by
  apply modelFormCoefficientMap_injective n (k + 1)
  funext I
  change chartForm B x z (fun r => realVec (I r)) =
    extDeriv (chartForm A x) z (fun r => realVec (I r))
  rw [chartForm_apply_basis, hAB x z hz I]
  exact (chartForm_extDeriv_apply A hA x hz I).symm

/-- The original closedness predicate follows from the actual twice-differentiated form. -/
theorem representsExterior_closed {A : RealForm M k} {B : RealForm M (k + 1)}
    (hA : SmoothRealForm A) (hAB : RepresentsExterior A B) : ClosedRealForm B := by
  intro x z hz I
  have hloc : chartForm B x =ᶠ[𝓝 z] extDeriv (chartForm A x) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact representsExterior_chartForm hA hAB x hw
  have hdd := extDeriv_extDeriv_apply ((chartForm_contDiffOn A hA x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)) (by simp)
  rw [← chartForm_extDeriv_apply B (representsExterior_smooth hA hAB) x hz I,
    hloc.extDeriv_eq, hdd]
  rfl

theorem exteriorRealForm_closed (A : RealForm M k) (hA : SmoothRealForm A) :
    ClosedRealForm (exteriorRealForm A) :=
  representsExterior_closed hA (exteriorRealForm_represents A hA)

theorem representsExterior_eq_zero_of_eventuallyEq_zero {A : RealForm M k}
    {B : RealForm M (k + 1)} (hAB : RepresentsExterior A B) (x : M.Carrier)
    (hA : ∀ᶠ y in 𝓝 x, A y = 0) : B x = 0 := by
  apply (formComponents_center_eq_zero_iff B x).mp
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hlocal : formComponents A x =ᶠ[𝓝 (chartPt x x)] 0 := by
    have hA' : ∀ᶠ y in 𝓝 (chartInv x (chartPt x x)), A y = (0 : RealForm M k) y := by
      simpa only [hx, Pi.zero_apply] using hA
    simpa only [formComponents_zero] using formComponents_eventuallyEq_of_eventuallyEq x ht hA'
  have hd := exteriorComponents_congr_nhds hlocal
  funext I
  rw [hAB x (chartPt x x) ht I]
  exact (congrFun hd I).trans (by rw [exteriorComponents_zero]; rfl)

theorem representsExterior_support_subset {A : RealForm M k} {B : RealForm M (k + 1)}
    (hAB : RepresentsExterior A B) : closure {x | B x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hA : ∀ᶠ y in 𝓝 x, A y = 0 := by
    filter_upwards [isClosed_closure.compl_mem_nhds h] with y hy
    by_contra hne
    exact hy (subset_closure hne)
  exact hx (representsExterior_eq_zero_of_eventuallyEq_zero hAB x hA)

theorem representsExterior_compactlySupported {A : RealForm M k} {B : RealForm M (k + 1)}
    (hAB : RepresentsExterior A B) (hA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm B :=
  hA.of_isClosed_subset isClosed_closure (representsExterior_support_subset hAB)

theorem exteriorRealForm_compactlySupported (A : RealForm M k) (hA : SmoothRealForm A)
    (hcA : CompactlySupportedRealForm A) : CompactlySupportedRealForm (exteriorRealForm A) :=
  representsExterior_compactlySupported (exteriorRealForm_represents A hA) hcA

theorem exteriorRealForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (hcA : CompactlySupportedRealForm A) : L2RealForm g.form μ (exteriorRealForm A) :=
  smooth_compactlySupported_l2RealForm g μ hμ (exteriorRealForm A)
    (exteriorRealForm_smooth A hA) (exteriorRealForm_compactlySupported A hA hcA)


theorem tensorCoefficientPairing_contDiffOn {E ι α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : E → Matrix α α ℝ) (F H : E → (ι → α) → ℝ) (O : Set E)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun z => B z i j) O)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) O)
    (hH : ∀ I, ContDiffOn ℝ ∞ (fun z => H z I) O) :
    ContDiffOn ℝ ∞ (fun z => tensorCoefficientPairing (B z) (F z) (H z)) O := by
  classical
  apply ContDiffOn.sum
  intro I _
  apply ContDiffOn.sum
  intro J _
  apply ((hF I).mul (hH J)).mul
  exact contDiffOn_prod (fun r _ => hB (I r) (J r))

/-- The actual density-weighted tensor pairing in one coordinate direction. -/
def tensorMetricFlux (g : HermitianField M) (x : M.Carrier) (F : FormComponents n k)
    (V : RIdx n → FormComponents n k) (a : RIdx n) (z : ComplexVector n) : ℝ :=
  Real.sqrt (realMetricFn g x z).det *
    tensorCoefficientPairing (realMetricFn g x z)⁻¹ (F z) (V a z)

/-- The complete computed connection term in tensor integration by parts. -/
def tensorCovariantGreenTerm (g : HermitianField M) (x : M.Carrier) (F : FormComponents n k)
    (V : RIdx n → FormComponents n k) (a : RIdx n) (z : ComplexVector n) : ℝ :=
  tensorCoefficientPairing (realMetricFn g x z)⁻¹
      (fun I => covariantComponents g x F z a I) (V a z) +
    tensorCoefficientPairing (realMetricFn g x z)⁻¹ (F z)
      (fun I => covariantComponents g x (V a) z a I) +
    (∑ b, christoffel g x z b a b) *
      tensorCoefficientPairing (realMetricFn g x z)⁻¹ (F z) (V a z)

theorem tensorMetricFlux_contDiffOn (g : SmoothMetric M) (x : M.Carrier) (F : FormComponents n k)
    (V : RIdx n → FormComponents n k)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (hV : ∀ a I, ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x)) (a : RIdx n) :
    ContDiffOn ℝ ∞ (tensorMetricFlux g.form x F V a) (chartTarget x) :=
  (L18Aux.volumeDensity_contDiffOn g x).mul
    (tensorCoefficientPairing_contDiffOn _ F (V a) (chartTarget x)
      (L18Aux.realMetricFn_inverse_contDiffOn g x) hF (hV a))

theorem tensorMetricFlux_derivative (g : SmoothMetric M) (x : M.Carrier) (F : FormComponents n k)
    (V : RIdx n → FormComponents n k)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (hV : ∀ a I, ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
    rDeriv (tensorMetricFlux g.form x F V a) z a =
      Real.sqrt (realMetricFn g.form x z).det * tensorCovariantGreenTerm g.form x F V a z := by
  have hFa (I : Fin k → RIdx n) : DifferentiableAt ℝ (fun w => F w I) z :=
    ((hF I).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hVa (I : Fin k → RIdx n) : DifferentiableAt ℝ (fun w => V a w I) z :=
    ((hV a I).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hi (i j : RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form x w)⁻¹ i j) z :=
    ((L18Aux.realMetricFn_inverse_contDiffOn g x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hp := differentiableAt_tensorCoefficientPairing
    (fun w => (realMetricFn g.form x w)⁻¹) F (V a) z hi hFa hVa
  have hρ : DifferentiableAt ℝ (fun w => Real.sqrt (realMetricFn g.form x w).det) z :=
    ((L18Aux.volumeDensity_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  unfold tensorMetricFlux
  rw [rDeriv_mul_at _ _ z hρ hp a,
    L18Aux.rDeriv_volumeDensity_eq_christoffel_trace g x hz a,
    tensorCoefficientPairing_covariant_derivative g x F (V a) hz hFa hVa a]
  dsimp only [tensorCovariantGreenTerm]
  ring

/-- Local tensor-flux integration by parts with the actual Lebesgue measure and density. -/
theorem integral_tensorMetricFlux (g : SmoothMetric M) (x : M.Carrier) (F : FormComponents n k)
    (V : RIdx n → FormComponents n k)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (hV : ∀ a I, ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x))
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * (∑ a, rDeriv (tensorMetricFlux g.form x F V a) z a) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x F V a z ∂lebesgueC n) := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  exact L18Aux.integral_compactTest_divergence_on (lebesgueC n)
    (isOpen_extChartAt_target (I := ComplexModel n) x) hφ hcφ hφO
    (tensorMetricFlux g.form x F V)
    (fun a => (tensorMetricFlux_contDiffOn g x F V hF hV a).of_le (by simp)) realVec

/-- The actual all-degree tensor Green identity in a fixed chart; support,
integrability, metric compatibility, and the volume derivative are internal. -/
theorem integral_tensor_covariant_derivative (g : SmoothMetric M) (x : M.Carrier)
    (F : FormComponents n k) (V : RIdx n → FormComponents n k)
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (hV : ∀ a I, ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x))
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x F V a z) ∂lebesgueC n =
      -(∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x F V a z ∂lebesgueC n) := by
  have heq (z : ComplexVector n) :
      φ z * (∑ a, rDeriv (tensorMetricFlux g.form x F V a) z a) =
        φ z * Real.sqrt (realMetricFn g.form x z).det *
          (∑ a, tensorCovariantGreenTerm g.form x F V a z) := by
    by_cases hz : z ∈ chartTarget x
    · simp only [tensorMetricFlux_derivative g x F V hF hV hz]
      rw [← Finset.mul_sum]
      ring
    · have hzero : φ z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hzero, zero_mul]
  calc
    _ = ∫ z, φ z * (∑ a, rDeriv (tensorMetricFlux g.form x F V a) z a) ∂lebesgueC n :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => (heq z).symm)
    _ = _ := integral_tensorMetricFlux g x F V hF hV hφ hcφ hφO


theorem sum_function_insertNth {α : Type*} [Fintype α] (r : Fin (k + 1))
    (f : (Fin (k + 1) → α) → ℝ) :
    (∑ I, f I) = ∑ a, ∑ J : Fin k → α, f (r.insertNth (α := fun _ => α) a J) := by
  classical
  have h := ((Fin.insertNthEquiv (fun _ : Fin (k + 1) => α) r).sum_comp f).symm
  simp only [Fintype.sum_prod_type] at h
  with_unfolding_all
    exact h

theorem tensorProduct_insertNth {α : Type*} (B : Matrix α α ℝ) (r : Fin (k + 1))
    (a b : α) (I J : Fin k → α) :
    (∏ s, B (r.insertNth (α := fun _ => α) a I s) (r.insertNth (α := fun _ => α) b J s)) =
      B a b * ∏ s, B (I s) (J s) := by
  rw [Fin.prod_univ_succAbove _ r]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem realVec_insertNth (r : Fin (k + 1)) (b : RIdx n) (J : Fin k → RIdx n) :
    (fun s => realVec (r.insertNth (α := fun _ => RIdx n) b J s)) =
      r.insertNth (α := fun _ => ComplexVector n) (realVec b) (fun s => realVec (J s)) := by
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp
  · funext s
    simp [Fin.removeNth]

theorem realVec_finCons (b : RIdx n) (J : Fin k → RIdx n) :
    (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) = Fin.cons (α := fun _ => ComplexVector n) (realVec b) (fun s => realVec (J s)) := by
  funext s
  cases s using Fin.cases <;> rfl

theorem modelForm_insertNth_sign (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (r : Fin (k + 1)) (b : RIdx n) (J : Fin k → RIdx n) :
    (-1 : ℝ) ^ r.val * H (fun s => realVec (r.insertNth (α := fun _ => RIdx n) b J s)) =
      H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) := by
  rw [realVec_insertNth, realVec_finCons]
  simpa [zsmul_eq_mul, Matrix.vecCons] using H.neg_one_pow_smul_map_insertNth r (realVec b) (fun s => realVec (J s))

/-- Every signed omission has the same contraction against an actual alternating form. -/
theorem omissionPairing_slot (B : Matrix (RIdx n) (RIdx n) ℝ)
    (D : RIdx n → (Fin k → RIdx n) → ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) (r : Fin (k + 1)) :
    (∑ I : Fin (k + 1) → RIdx n, ∑ J : Fin (k + 1) → RIdx n,
      (-1 : ℝ) ^ r.val * D (I r) (r.removeNth I) * H (fun s => realVec (J s)) *
        ∏ s, B (I s) (J s)) =
    ∑ a, ∑ b, B a b * tensorCoefficientPairing B (D a)
      (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s))) := by
  classical
  rw [sum_function_insertNth r]
  simp_rw [sum_function_insertNth r]
  simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth, tensorProduct_insertNth]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [tensorCoefficientPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  calc
    _ = B a b * D a I * ((-1 : ℝ) ^ r.val * H (fun s => realVec (r.insertNth (α := fun _ => RIdx n) b J s))) *
        ∏ s, B (I s) (J s) := by ring
    _ = _ := by rw [modelForm_insertNth_sign]; ring

/-- The factor `k+1` in the exterior-derivative contraction is proved by
finite reindexing, with the paper's exact signs and normalization. -/
theorem tensorCoefficientPairing_alternating_sum (B : Matrix (RIdx n) (RIdx n) ℝ)
    (D : RIdx n → (Fin k → RIdx n) → ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    tensorCoefficientPairing B
      (fun I : Fin (k + 1) → RIdx n => ∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val * D (I r) (r.removeNth I))
      (fun J => H (fun s => realVec (J s))) =
      (k + 1 : ℝ) * ∑ a, ∑ b, B a b * tensorCoefficientPairing B (D a)
        (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s))) := by
  classical
  let T (r : Fin (k + 1)) (I J : Fin (k + 1) → RIdx n) : ℝ :=
    (-1 : ℝ) ^ r.val * D (I r) (r.removeNth I) * H (fun s => realVec (J s)) *
      ∏ s, B (I s) (J s)
  have hL : tensorCoefficientPairing B
      (fun I : Fin (k + 1) → RIdx n => ∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val * D (I r) (r.removeNth I))
      (fun J => H (fun s => realVec (J s))) = ∑ r, ∑ I, ∑ J, T r I J := by
    simp only [tensorCoefficientPairing, Finset.sum_mul]
    change (∑ I, ∑ J, ∑ r, T r I J) = _
    exact (sum_three_rotate T).symm
  rw [hL]
  have hr (r : Fin (k + 1)) : (∑ I, ∑ J, T r I J) =
      ∑ a, ∑ b, B a b * tensorCoefficientPairing B (D a)
        (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s))) :=
    omissionPairing_slot B D H r
  simp_rw [hr]
  simp [nsmul_eq_mul]


theorem factorial_inv_mul_succ (k : ℕ) :
    (Nat.factorial (k + 1) : ℝ)⁻¹ * (k + 1 : ℝ) = (Nat.factorial k : ℝ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ (show (k + 1 : ℝ) ≠ 0 by positivity), mul_one]

/-- The actual exterior-form pairing reduces to its first-derivative contraction,
with exactly the frozen `1/k!` metric normalization. -/
theorem formInner_exterior_in_chart (g : HermitianField M) (A : RealForm M k)
    (dA B : RealForm M (k + 1)) (hAd : RepresentsExterior A dA) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formInner g dA B (chartInv x z) = (Nat.factorial k : ℝ)⁻¹ *
      ∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
        tensorCoefficientPairing (realMetricFn g x z)⁻¹
          (fun I : Fin k → RIdx n => rDeriv (fun w => formComponents A x w I) z a)
          (fun J : Fin k → RIdx n => formComponents B x z (Fin.cons b J)) := by
  let D (a : RIdx n) (I : Fin k → RIdx n) : ℝ :=
    rDeriv (fun w => formComponents A x w I) z a
  have hC : formComponents dA x z =
      (fun I : Fin (k + 1) → RIdx n => ∑ r : Fin (k + 1),
        (-1 : ℝ) ^ r.val * D (I r) (r.removeNth I)) := by
    funext I
    with_unfolding_all
      exact hAd x z hz I
  have hH : formComponents B x z =
      (fun J : Fin (k + 1) → RIdx n => chartForm B x z (fun r => realVec (J r))) := by
    funext J
    exact (chartForm_apply_basis B x z J).symm
  rw [formInner_chartInv_eq_tensorPairing g dA B x hz, hC, hH,
    tensorCoefficientPairing_alternating_sum]
  simp only [chartForm_apply_basis]
  dsimp only [D]
  rw [← mul_assoc, factorial_inv_mul_succ]


/-- The true model linear map whose basis images are the rows of a real matrix. -/
def modelMatrixRowMap (B : Matrix (RIdx n) (RIdx n) ℝ) : ComplexVector n →L[ℝ] ComplexVector n :=
  ((realModelBasis n).constr ℝ (fun a => ∑ b, B a b • realVec b)).toContinuousLinearMap

theorem modelMatrixRowMap_realVec (B : Matrix (RIdx n) (RIdx n) ℝ) (a : RIdx n) :
    modelMatrixRowMap B (realVec a) = ∑ b, B a b • realVec b := by
  change (realModelBasis n).constr ℝ (fun a => ∑ b, B a b • realVec b) (realVec a) = _
  rw [← realModelBasis_apply a, Basis.constr_basis]

/-- Raising every index is an actual alternating tensor, for every real matrix. -/
def raisedModelForm (B : Matrix (RIdx n) (RIdx n) ℝ)
    (H : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ :=
  H.compContinuousLinearMap (modelMatrixRowMap B)

theorem raisedModelForm_coeff (B : Matrix (RIdx n) (RIdx n) ℝ)
    (H : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (I : Fin k → RIdx n) :
    raisedModelForm B H (fun r => realVec (I r)) =
      ∑ J : Fin k → RIdx n, H (fun r => realVec (J r)) * ∏ r, B (I r) (J r) := by
  classical
  change H (fun r => modelMatrixRowMap B (realVec (I r))) = _
  simp only [modelMatrixRowMap_realVec]
  calc
    H (fun r => ∑ b, B (I r) b • realVec b) =
        ∑ J : Fin k → RIdx n, H (fun r => B (I r) (J r) • realVec (J r)) :=
      H.map_sum (fun r b => B (I r) b • realVec b)
    _ = ∑ J : Fin k → RIdx n, (∏ r, B (I r) (J r)) * H (fun r => realVec (J r)) := by
      apply Finset.sum_congr rfl
      intro J _
      exact H.map_smul_univ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro J _
      ring

theorem finCons_swap_zero_succ {α : Type*} (r : Fin k) (a : α) (I : Fin k → α) :
    (Fin.cons (I r) (Function.update I r a) : Fin (k + 1) → α) =
      (Fin.cons a I) ∘ Equiv.swap 0 r.succ := by
  funext s
  cases s using Fin.cases with
  | zero => simp [Function.comp_def]
  | succ s =>
    by_cases hs : s = r
    · subst s
      simp [Function.comp_def]
    · simp [Function.comp_def, Equiv.swap_apply_def, hs, Function.update_of_ne hs]

theorem modelForm_cons_swap (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (r : Fin k) (a : RIdx n) (I : Fin k → RIdx n) :
    H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) (I r) (Function.update I r a) s)) =
      -H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)) := by
  rw [finCons_swap_zero_succ r a I]
  change H ((fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)) ∘ Equiv.swap 0 r.succ) = _
  with_unfolding_all
    exact H.toAlternatingMap.map_swap _ (Ne.symm (Fin.succ_ne_zero r))

/-- A symmetric connection coefficient vanishes after contraction with the two
alternating slots. This is the finite torsion-free cancellation used by de Rham Green. -/
theorem symmetric_slot_contraction_eq_zero
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (F : (Fin k → RIdx n) → ℝ) (S : Matrix (RIdx n) (RIdx n) ℝ)
    (hS : S.IsSymm) (c : RIdx n) (r : Fin k) :
    (∑ I : Fin k → RIdx n, ∑ a, S a (I r) * F (Function.update I r c) *
      H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s))) = 0 := by
  classical
  let T (I : Fin k → RIdx n) (a : RIdx n) : ℝ :=
    S a (I r) * F (Function.update I r c) *
      H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s))
  have ht (I : Fin k → RIdx n) (a : RIdx n) :
      T (Function.update I r a) (I r) = -T I a := by
    dsimp only [T]
    simp only [Function.update_self, Function.update_idem]
    rw [hS.apply a (I r), modelForm_cons_swap H r a I]
    ring
  have hs : (∑ I, ∑ a, T I a) = -(∑ I, ∑ a, T I a) := by
    calc
      _ = ∑ I, ∑ a, T (Function.update I r a) (I r) := sum_swapFunctionSlot r T
      _ = ∑ I, ∑ a, -T I a := by
        apply Finset.sum_congr rfl
        intro I _
        apply Finset.sum_congr rfl
        intro a _
        exact ht I a
      _ = _ := by simp only [Finset.sum_neg_distrib]
  change (∑ I, ∑ a, T I a) = 0
  linarith



theorem sum_function_finCons {α : Type*} [Fintype α]
    (f : (Fin (k + 1) → α) → ℝ) :
    (∑ I, f I) = ∑ a, ∑ J : Fin k → α, f (Fin.cons a J) := by
  classical
  have h := ((Fin.consEquiv (fun _ : Fin (k + 1) => α)).sum_comp f).symm
  simp only [Fintype.sum_prod_type] at h
  with_unfolding_all
    exact h

theorem raisedModelForm_cons_coeff (B : Matrix (RIdx n) (RIdx n) ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) (a : RIdx n) (I : Fin k → RIdx n) :
    raisedModelForm B H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)) =
      ∑ b, ∑ J : Fin k → RIdx n, B a b *
        H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) * ∏ r, B (I r) (J r) := by
  classical
  rw [raisedModelForm_coeff, sum_function_finCons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem tensorPairing_raised_first_contraction (B : Matrix (RIdx n) (RIdx n) ℝ)
    (D : RIdx n → (Fin k → RIdx n) → ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (∑ a, ∑ b, B a b * tensorCoefficientPairing B (D a)
      (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)))) =
    ∑ I : Fin k → RIdx n, ∑ a, D a I *
      raisedModelForm B H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)) := by
  classical
  calc
    _ = ∑ a, ∑ b, ∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
        B a b * D a I * H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) *
          ∏ r, B (I r) (J r) := by
      simp only [tensorCoefficientPairing, Finset.mul_sum, mul_assoc]
    _ = ∑ I : Fin k → RIdx n, ∑ a, ∑ b, ∑ J : Fin k → RIdx n,
        B a b * D a I * H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) *
          ∏ r, B (I r) (J r) :=
      (sum_three_rotate (fun (I : Fin k → RIdx n) (a b : RIdx n) =>
        ∑ J : Fin k → RIdx n, B a b * D a I *
          H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) *
            ∏ r, B (I r) (J r))).symm
    _ = _ := by
      simp only [raisedModelForm_cons_coeff, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro J _
      ring

/-- The tensor connection term has zero pairing with a raised alternating form
when its two lower connection indices are symmetric. -/
theorem tensorConnectionAction_raised_contraction_eq_zero
    (B : Matrix (RIdx n) (RIdx n) ℝ) (S : RIdx n → Matrix (RIdx n) (RIdx n) ℝ)
    (hS : ∀ c, (S c).IsSymm) (F : (Fin k → RIdx n) → ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (∑ a, ∑ b, B a b * tensorCoefficientPairing B
      (tensorConnectionAction (fun c i => S c a i) F)
      (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)))) = 0 := by
  classical
  let K := raisedModelForm B H
  rw [tensorPairing_raised_first_contraction]
  change (∑ I : Fin k → RIdx n, ∑ a,
    (∑ r, ∑ c, S c a (I r) * F (Function.update I r c)) *
      K (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s))) = 0
  simp only [Finset.sum_mul]
  have hi (I : Fin k → RIdx n) :
      (∑ a, ∑ r : Fin k, ∑ c, S c a (I r) * F (Function.update I r c) *
        K (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s))) =
      ∑ r : Fin k, ∑ c, ∑ a, S c a (I r) * F (Function.update I r c) *
        K (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)) :=
    sum_three_rotate _
  simp_rw [hi]
  rw [sum_three_rotate (fun (I : Fin k → RIdx n) (r : Fin k) (c : RIdx n) =>
    ∑ a, S c a (I r) * F (Function.update I r c) *
      K (fun s => realVec (Fin.cons (α := fun _ => RIdx n) a I s)))]
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro c _
  exact symmetric_slot_contraction_eq_zero K F (S c) (hS c) c r

theorem christoffel_raised_contraction_eq_zero (g : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (F : (Fin k → RIdx n) → ℝ)
    (H : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b * tensorCoefficientPairing (realMetricFn g x z)⁻¹
      (tensorConnectionAction (christoffelMatrix g x z a) F)
      (fun J : Fin k → RIdx n => H (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)))) = 0 := by
  have hS (c : RIdx n) : Matrix.IsSymm (fun (a i : RIdx n) => christoffel g x z c a i) := by
    ext a i
    exact christoffel_symmetric_lower g x z c i a
  with_unfolding_all
    exact tensorConnectionAction_raised_contraction_eq_zero
      (realMetricFn g x z)⁻¹ (fun c a i => christoffel g x z c a i) hS F H

/-- The actual exterior-form metric pairing uses the computed covariant derivative;
the connection terms cancel by the true alternating/torsion-free identity. -/
theorem formInner_exterior_covariant_in_chart (g : HermitianField M) (A : RealForm M k)
    (dA V : RealForm M (k + 1)) (hAd : RepresentsExterior A dA) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formInner g dA V (chartInv x z) = (Nat.factorial k : ℝ)⁻¹ *
      ∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
        tensorCoefficientPairing (realMetricFn g x z)⁻¹
          (fun I : Fin k → RIdx n => covariantComponents g x (formComponents A x) z a I)
          (fun J : Fin k → RIdx n => formComponents V x z (Fin.cons b J)) := by
  have hzero : (∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
      tensorCoefficientPairing (realMetricFn g x z)⁻¹
        (tensorConnectionAction (christoffelMatrix g x z a) (formComponents A x z))
        (fun J : Fin k → RIdx n => formComponents V x z (Fin.cons b J))) = 0 := by
    simpa only [chartForm_apply_basis] using
      christoffel_raised_contraction_eq_zero g x z (formComponents A x z) (chartForm V x z)
  have hc (a : RIdx n) :
      (fun I => covariantComponents g x (formComponents A x) z a I) =
        (fun I => rDeriv (fun w => formComponents A x w I) z a) -
          tensorConnectionAction (christoffelMatrix g x z a) (formComponents A x z) := rfl
  rw [formInner_exterior_in_chart g A dA V hAd x hz]
  congr 1
  symm
  simp_rw [hc, tensorCoefficientPairing_sub_left, mul_sub, Finset.sum_sub_distrib]
  rw [hzero, sub_zero]


/-- Separate the connection action on the inserted first covariant slot. -/
theorem covariantComponents_first_slot (g : HermitianField M) (x : M.Carrier)
    (H : FormComponents n (k + 1)) (z : ComplexVector n) (a b : RIdx n)
    (I : Fin k → RIdx n) :
    covariantComponents g x H z a (Fin.cons b I) =
      covariantComponents g x (fun w J => H w (Fin.cons b J)) z a I -
        ∑ c, christoffel g x z c a b * H z (Fin.cons c I) := by
  simp only [covariantComponents, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.update_cons_zero, ← Fin.cons_update]
  ring

theorem covariantComponents_fintypeSum_at {ι : Type*} [Fintype ι]
    (g : HermitianField M) (x : M.Carrier) (T : ι → FormComponents n k) (z : ComplexVector n)
    (hT : ∀ i I, DifferentiableAt ℝ (fun w => T i w I) z) (a : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g x (fun w J => ∑ i, T i w J) z a I =
      ∑ i, covariantComponents g x (T i) z a I := by
  classical
  have hc : (∑ r, ∑ c, christoffel g x z c a (I r) * (∑ i, T i z (Function.update I r c))) =
      ∑ i, ∑ r, ∑ c, christoffel g x z c a (I r) * T i z (Function.update I r c) := by
    simp only [Finset.mul_sum]
    exact (sum_three_rotate (fun (i : ι) (r : Fin k) (c : RIdx n) =>
      christoffel g x z c a (I r) * T i z (Function.update I r c))).symm
  simp only [covariantComponents]
  rw [rDeriv_finsetSum_at Finset.univ (fun i w => T i w I) z (fun i _ => hT i I) a, hc]
  simp only [Finset.sum_sub_distrib]

theorem tensorCoefficientPairing_fintypeSum_left {ι α κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype κ]
    (B : Matrix α α ℝ) (F : κ → (ι → α) → ℝ) (H : (ι → α) → ℝ) :
    tensorCoefficientPairing B (fun I => ∑ t, F t I) H =
      ∑ t, tensorCoefficientPairing B (F t) H := by
  classical
  simp only [tensorCoefficientPairing, Finset.sum_mul]
  exact (sum_three_rotate (fun (t : κ) (I J : ι → α) =>
    F t I * H J * ∏ r, B (I r) (J r))).symm

theorem tensorCoefficientPairing_fintypeSum_right {ι α κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype κ]
    (B : Matrix α α ℝ) (F : (ι → α) → ℝ) (H : κ → (ι → α) → ℝ) :
    tensorCoefficientPairing B F (fun J => ∑ t, H t J) =
      ∑ t, tensorCoefficientPairing B F (H t) := by
  classical
  simp only [tensorCoefficientPairing, Finset.mul_sum, Finset.sum_mul]
  exact (sum_three_rotate (fun (t : κ) (I J : ι → α) =>
    F I * H t J * ∏ r, B (I r) (J r))).symm

theorem tensorCoefficientPairing_const_mul_right {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H : (ι → α) → ℝ) (c : ℝ) :
    tensorCoefficientPairing B F (fun J => c * H J) = c * tensorCoefficientPairing B F H := by
  classical
  simp only [tensorCoefficientPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

/-- The actual inverse metric raises the inserted first form index. -/
def raisedFirstComponents (g : HermitianField M) (x : M.Carrier)
    (H : FormComponents n (k + 1)) (p : RIdx n) : FormComponents n k :=
  fun z I => ∑ b, (realMetricFn g x z)⁻¹ p b * H z (Fin.cons b I)

theorem raisedFirstComponents_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (H : FormComponents n (k + 1))
    (hH : ∀ I, ContDiffOn ℝ ∞ (fun z => H z I) (chartTarget x))
    (p : RIdx n) (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => raisedFirstComponents g.form x H p z I) (chartTarget x) := by
  apply ContDiffOn.sum
  intro b _
  exact (L18Aux.realMetricFn_inverse_contDiffOn g x p b).mul (hH (Fin.cons b I))


/-- Raising the first index commutes with the actual computed covariant derivative,
including its contravariant connection term. -/
theorem covariantComponents_raisedFirst (g : SmoothMetric M) (x : M.Carrier)
    (H : FormComponents n (k + 1))
    (hH : ∀ J, ContDiffOn ℝ ∞ (fun z => H z J) (chartTarget x))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a p : RIdx n) (I : Fin k → RIdx n) :
    covariantComponents g.form x (raisedFirstComponents g.form x H p) z a I =
      (∑ b, (realMetricFn g.form x z)⁻¹ p b *
        covariantComponents g.form x H z a (Fin.cons b I)) -
      ∑ c, christoffel g.form x z p a c * raisedFirstComponents g.form x H c z I := by
  have hHd (J : Fin (k + 1) → RIdx n) : DifferentiableAt ℝ (fun w => H w J) z :=
    ((hH J).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hi (u v : RIdx n) : DifferentiableAt ℝ (fun w => (realMetricFn g.form x w)⁻¹ u v) z :=
    ((L18Aux.realMetricFn_inverse_contDiffOn g x u v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have ht (b : RIdx n) (J : Fin k → RIdx n) : DifferentiableAt ℝ
      (fun w => (realMetricFn g.form x w)⁻¹ p b * H w (Fin.cons b J)) z :=
    (hi p b).mul (hHd (Fin.cons b J))
  have hm (b : RIdx n) := covariantComponents_multiply_at g.form x
    (fun w => (realMetricFn g.form x w)⁻¹ p b) (fun w J => H w (Fin.cons b J)) z
    (hi p b) (fun J => hHd (Fin.cons b J)) a I
  have hs (b : RIdx n) :
      covariantComponents g.form x (fun w J => H w (Fin.cons b J)) z a I =
        covariantComponents g.form x H z a (Fin.cons b I) +
          ∑ c, christoffel g.form x z c a b * H z (Fin.cons c I) := by
    have h := covariantComponents_first_slot g.form x H z a b I
    linarith
  have hswap₁ :
      (∑ b, ∑ c, (realMetricFn g.form x z)⁻¹ p b * christoffel g.form x z c a b * H z (Fin.cons c I)) =
      ∑ b, ∑ c, (realMetricFn g.form x z)⁻¹ p c * christoffel g.form x z b a c * H z (Fin.cons b I) := by
    rw [Finset.sum_comm]
  have hswap₂ :
      (∑ b, ∑ c, christoffel g.form x z p a c * (realMetricFn g.form x z)⁻¹ c b * H z (Fin.cons b I)) =
      ∑ c, ∑ b, christoffel g.form x z p a c * (realMetricFn g.form x z)⁻¹ c b * H z (Fin.cons b I) :=
    Finset.sum_comm
  simp only [mul_assoc] at hswap₁ hswap₂
  unfold raisedFirstComponents
  rw [covariantComponents_fintypeSum_at g.form x
    (fun b w J => (realMetricFn g.form x w)⁻¹ p b * H w (Fin.cons b J)) z ht a I]
  simp_rw [hm, hs, realMetricFn_inverse_covariant_derivative g x hz]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, mul_assoc]
  rw [hswap₁, hswap₂]
  ring

/-- The density-corrected divergence of the raised form index is exactly minus
 the frozen codifferential calculator, on every actual chart target. -/
theorem raisedFirstComponents_divergence (g : SmoothMetric M) (x : M.Carrier)
    (H : FormComponents n (k + 1))
    (hH : ∀ J, ContDiffOn ℝ ∞ (fun z => H z J) (chartTarget x))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin k → RIdx n) :
    (∑ a, (covariantComponents g.form x (raisedFirstComponents g.form x H a) z a I +
      (∑ b, christoffel g.form x z b a b) * raisedFirstComponents g.form x H a z I)) =
      -codifferentialComponents g.form x H z I := by
  have ht :
      (∑ a, ∑ c, christoffel g.form x z a a c * raisedFirstComponents g.form x H c z I) =
      ∑ a, (∑ b, christoffel g.form x z b a b) * raisedFirstComponents g.form x H a z I := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [christoffel_symmetric_lower g.form x z b b a]
  simp_rw [covariantComponents_raisedFirst g x H hH hz]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, codifferentialComponents, neg_neg]
  rw [ht]
  ring


theorem tensorCoefficientPairing_add_right {ι α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α]
    (B : Matrix α α ℝ) (F H K : (ι → α) → ℝ) :
    tensorCoefficientPairing B F (fun J => H J + K J) =
      tensorCoefficientPairing B F H + tensorCoefficientPairing B F K := by
  simp only [tensorCoefficientPairing, mul_add, add_mul, Finset.sum_add_distrib]

/-- The tensor Green terms become the exterior/codifferential contraction
when the vector index is the actual raised first form index. -/
theorem tensorCovariantGreenTerm_raisedFirst (g : SmoothMetric M) (x : M.Carrier)
    (F : FormComponents n k) (H : FormComponents n (k + 1))
    (hH : ∀ J, ContDiffOn ℝ ∞ (fun z => H z J) (chartTarget x))
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (∑ a, tensorCovariantGreenTerm g.form x F (raisedFirstComponents g.form x H) a z) =
      (∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
        tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
          (fun I => covariantComponents g.form x F z a I) (fun J => H z (Fin.cons b J))) -
      tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
        (codifferentialComponents g.form x H z) := by
  classical
  have hleft (a : RIdx n) :
      tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
        (fun I => covariantComponents g.form x F z a I)
        (raisedFirstComponents g.form x H a z) =
      ∑ b, (realMetricFn g.form x z)⁻¹ a b * tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
        (fun I => covariantComponents g.form x F z a I) (fun J => H z (Fin.cons b J)) := by
    change tensorCoefficientPairing (realMetricFn g.form x z)⁻¹
      (fun I => covariantComponents g.form x F z a I)
      (fun J => ∑ b, (realMetricFn g.form x z)⁻¹ a b * H z (Fin.cons b J)) = _
    rw [tensorCoefficientPairing_fintypeSum_right]
    apply Finset.sum_congr rfl
    intro b _
    exact tensorCoefficientPairing_const_mul_right _ _ _ _
  have hdiv :
      (fun I => ∑ a, (covariantComponents g.form x (raisedFirstComponents g.form x H a) z a I +
        (∑ b, christoffel g.form x z b a b) * raisedFirstComponents g.form x H a z I)) =
      (fun I => -codifferentialComponents g.form x H z I) := by
    funext I
    exact raisedFirstComponents_divergence g x H hH hz I
  have hm : tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
      (fun I => ∑ a, (covariantComponents g.form x (raisedFirstComponents g.form x H a) z a I +
        (∑ b, christoffel g.form x z b a b) * raisedFirstComponents g.form x H a z I)) =
      ∑ a, (tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
        (fun I => covariantComponents g.form x (raisedFirstComponents g.form x H a) z a I) +
        (∑ b, christoffel g.form x z b a b) *
          tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
            (raisedFirstComponents g.form x H a z)) := by
    rw [tensorCoefficientPairing_fintypeSum_right]
    apply Finset.sum_congr rfl
    intro a _
    rw [tensorCoefficientPairing_add_right, tensorCoefficientPairing_const_mul_right]
  have hright :
      (∑ a, (tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
        (fun I => covariantComponents g.form x (raisedFirstComponents g.form x H a) z a I) +
        (∑ b, christoffel g.form x z b a b) *
          tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
            (raisedFirstComponents g.form x H a z))) =
      -tensorCoefficientPairing (realMetricFn g.form x z)⁻¹ (F z)
        (codifferentialComponents g.form x H z) := by
    rw [← hm, hdiv]
    simpa only [neg_one_mul] using tensorCoefficientPairing_const_mul_right
      (realMetricFn g.form x z)⁻¹ (F z) (codifferentialComponents g.form x H z) (-1)
  simp only [tensorCovariantGreenTerm, Finset.sum_add_distrib]
  simp_rw [hleft]
  simp only [Finset.sum_add_distrib] at hright
  linarith [hright]

/-- The exact pointwise divergence term in the original form metric. -/
theorem tensorCovariantGreenTerm_forms (g : SmoothMetric M) (A : RealForm M k)
    (dA H : RealForm M (k + 1)) (deltaH : RealForm M k) (hH : SmoothRealForm H)
    (hAd : RepresentsExterior A dA) (hHdelta : RepresentsCodifferential g.form H deltaH)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (Nat.factorial k : ℝ)⁻¹ *
      (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x)
        (raisedFirstComponents g.form x (formComponents H x)) a z) =
      formInner g.form dA H (chartInv x z) - formInner g.form A deltaH (chartInv x z) := by
  have hdelta : formComponents deltaH x z =
      codifferentialComponents g.form x (formComponents H x) z := by
    funext I
    exact hHdelta x z hz I
  rw [tensorCovariantGreenTerm_raisedFirst g x (formComponents A x) (formComponents H x) (hH x) hz,
    formInner_exterior_covariant_in_chart g.form A dA H hAd x hz,
    formInner_chartInv_eq_tensorPairing g.form A deltaH x hz, hdelta]
  ring

/-- Local Green identity for the actual exterior derivative and the actual frozen
codifferential relation, in every form degree with the exact paper normalization. -/
theorem integral_exterior_codifferential_in_chart (g : SmoothMetric M) (A : RealForm M k)
    (dA H : RealForm M (k + 1)) (deltaH : RealForm M k)
    (hA : SmoothRealForm A) (hH : SmoothRealForm H) (hAd : RepresentsExterior A dA)
    (hHdelta : RepresentsCodifferential g.form H deltaH) (x : M.Carrier)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * Real.sqrt (realMetricFn g.form x z).det *
        (formInner g.form dA H (chartInv x z) - formInner g.form A deltaH (chartInv x z)) ∂lebesgueC n =
      -(Nat.factorial k : ℝ)⁻¹ *
        (∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x (formComponents A x)
          (raisedFirstComponents g.form x (formComponents H x)) a z ∂lebesgueC n) := by
  let V := raisedFirstComponents g.form x (formComponents H x)
  let c : ℝ := (Nat.factorial k : ℝ)⁻¹
  have hV (a : RIdx n) (I : Fin k → RIdx n) :
      ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x) :=
    raisedFirstComponents_contDiffOn g x (formComponents H x) (hH x) a I
  have heq (z : ComplexVector n) :
      φ z * Real.sqrt (realMetricFn g.form x z).det *
        (formInner g.form dA H (chartInv x z) - formInner g.form A deltaH (chartInv x z)) =
      c * (φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z)) := by
    by_cases hz : z ∈ chartTarget x
    · have hp : c * (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z) =
          formInner g.form dA H (chartInv x z) - formInner g.form A deltaH (chartInv x z) :=
        tensorCovariantGreenTerm_forms g A dA H deltaH hH hAd hHdelta x hz
      rw [← hp]
      ring
    · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hzero, zero_mul, mul_zero]
  calc
    _ = ∫ z, c * (φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z)) ∂lebesgueC n :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = c * (∫ z, φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z) ∂lebesgueC n) :=
      integral_const_mul c _
    _ = c * (-(∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x (formComponents A x) V a z
        ∂lebesgueC n)) := by
      rw [integral_tensor_covariant_derivative g x (formComponents A x) V (hA x) hV hφ hcφ hφO]
    _ = _ := by
      dsimp only [c, V]
      ring


theorem covariantComponents_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (F : FormComponents n k) (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (a : RIdx n) (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => covariantComponents g.form x F z a I) (chartTarget x) := by
  apply (L18Aux.rDeriv_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x) (hF I) a).sub
  apply ContDiffOn.sum
  intro r _
  apply ContDiffOn.sum
  intro c _
  exact (L18Aux.christoffel_contDiffOn g x c a (I r)).mul (hF (Function.update I r c))

theorem exteriorComponents_contDiffOn_of_coefficients (x : M.Carrier)
    (F : FormComponents n k) (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (I : Fin (k + 1) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => exteriorComponents F z I) (chartTarget x) := by
  apply ContDiffOn.sum
  intro r _
  exact contDiffOn_const.mul (L18Aux.rDeriv_contDiffOn
    (isOpen_extChartAt_target (I := ComplexModel n) x) (hF (fun s => I (r.succAbove s))) (I r))

theorem codifferentialComponents_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (F : FormComponents n (k + 1))
    (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x)) (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => codifferentialComponents g.form x F z I) (chartTarget x) := by
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact (L18Aux.realMetricFn_inverse_contDiffOn g x a b).mul
    (covariantComponents_contDiffOn g x F hF a (Fin.cons b I))

theorem hodgeComponents_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (F : FormComponents n k) (hF : ∀ I, ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x))
    (I : Fin k → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => hodgeComponents g.form x k F z I) (chartTarget x) := by
  cases k with
  | zero =>
    exact codifferentialComponents_contDiffOn g x (exteriorComponents F)
      (exteriorComponents_contDiffOn_of_coefficients x F hF) I
  | succ k =>
    exact (exteriorComponents_contDiffOn_of_coefficients x (codifferentialComponents g.form x F)
      (codifferentialComponents_contDiffOn g x F hF) I).add
      (codifferentialComponents_contDiffOn g x (exteriorComponents F)
        (exteriorComponents_contDiffOn_of_coefficients x F hF) I)

theorem representsCodifferential_smooth (g : SmoothMetric M)
    {A : RealForm M (k + 1)} {B : RealForm M k}
    (hA : SmoothRealForm A) (hAB : RepresentsCodifferential g.form A B) : SmoothRealForm B := by
  intro x I
  apply (codifferentialComponents_contDiffOn g x (formComponents A x) (hA x) I).congr
  intro z hz
  exact hAB x z hz I

theorem representsHodge_smooth (g : SmoothMetric M) {A W : RealForm M k}
    (hA : SmoothRealForm A) (hAW : RepresentsHodge g.form A W) : SmoothRealForm W := by
  intro x I
  apply (hodgeComponents_contDiffOn g x (formComponents A x) (hA x) I).congr
  intro z hz
  exact hAW x z hz I

/-- All output regularity and both L² conditions in the actual Hodge core follow
from smooth compact input and its frozen full-chart representation relation. -/
theorem hodgeCorePair_iff_input (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k) :
    OperatorCandidates.HodgeCorePair g.form μ A W ↔
      SmoothRealForm A ∧ CompactlySupportedRealForm A ∧ RepresentsHodge g.form A W := by
  rw [hodgeCorePair_iff g μ hμ A W]
  constructor
  · rintro ⟨hA, hcA, _, hAW⟩
    exact ⟨hA, hcA, hAW⟩
  · rintro ⟨hA, hcA, hAW⟩
    exact ⟨hA, hcA, representsHodge_smooth g hA hAW, hAW⟩


/-- The connection action is an actual alternating tensor, not merely an index array. -/
theorem modelForm_connectionAction_coeff (C : Matrix (RIdx n) (RIdx n) ℝ)
    (H : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (I : Fin k → RIdx n) :
    H.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ (ComplexVector n))
      (modelMatrixRowMap C.transpose) (fun r => realVec (I r)) =
      tensorConnectionAction C (fun J => H (fun r => realVec (J r))) I := by
  classical
  rw [ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply]
  unfold tensorConnectionAction
  apply Finset.sum_congr rfl
  intro r _
  have hvec :
      (fun j => Function.update (fun _ : Fin k => ContinuousLinearMap.id ℝ (ComplexVector n))
        r (modelMatrixRowMap C.transpose) j (realVec (I j))) =
      Function.update (fun j => realVec (I j)) r (modelMatrixRowMap C.transpose (realVec (I r))) := by
    funext j
    by_cases hj : j = r
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  rw [hvec, modelMatrixRowMap_realVec]
  simp only [Matrix.transpose_apply]
  change H.toMultilinearMap
    (Function.update (fun j => realVec (I j)) r (∑ c, C c (I r) • realVec c)) = _
  rw [H.toMultilinearMap.map_update_sum Finset.univ r
    (fun c => C c (I r) • realVec c) (fun j => realVec (I j))]
  apply Finset.sum_congr rfl
  intro c _
  rw [MultilinearMap.map_update_smul]
  have hb : Function.update (fun j => realVec (I j)) r (realVec c) =
      (fun j => realVec (Function.update I r c j)) := by
    funext j
    by_cases hj : j = r
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  rw [hb]
  rfl

theorem chartForm_fderiv_apply_basis (A : RealForm M k) (hA : SmoothRealForm A) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) (I : Fin k → RIdx n) :
    fderiv ℝ (chartForm A x) z (realVec a) (fun r => realVec (I r)) =
      rDeriv (fun w => formComponents A x w I) z a := by
  have hd := ((chartForm_contDiffOn A hA x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : (fun w => chartForm A x w (fun r => realVec (I r))) =
      (fun w => formComponents A x w I) := by
    funext w
    exact chartForm_apply_basis A x w I
  have h := fderiv_continuousAlternatingMap_apply_const_apply hd
    (fun r => realVec (I r)) (realVec a)
  rw [heq] at h
  exact h.symm

/-- The actual alternating covariant derivative in a fixed chart. -/
def covariantChartForm (g : HermitianField M) (A : RealForm M k) (x : M.Carrier)
    (z : ComplexVector n) (a : RIdx n) : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ :=
  fderiv ℝ (chartForm A x) z (realVec a) -
    (chartForm A x z).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ (ComplexVector n))
      (modelMatrixRowMap (christoffelMatrix g x z a).transpose)

theorem covariantChartForm_coeff (g : HermitianField M) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n)
    (I : Fin k → RIdx n) :
    covariantChartForm g A x z a (fun r => realVec (I r)) =
      covariantComponents g x (formComponents A x) z a I := by
  simp only [covariantChartForm, ContinuousAlternatingMap.sub_apply]
  rw [chartForm_fderiv_apply_basis A hA x hz a I,
    modelForm_connectionAction_coeff (christoffelMatrix g x z a) (chartForm A x z) I]
  simp only [tensorConnectionAction, chartForm_apply_basis, christoffelMatrix, covariantComponents]

theorem covariantChartForm_contDiffOn (g : SmoothMetric M) (A : RealForm M k)
    (hA : SmoothRealForm A) (x : M.Carrier) (a : RIdx n) :
    ContDiffOn ℝ ∞ (fun z => covariantChartForm g.form A x z a) (chartTarget x) := by
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I
  apply (covariantComponents_contDiffOn g x (formComponents A x) (hA x) a I).congr
  intro z hz
  exact covariantChartForm_coeff g.form A hA x hz a I


/-- Contract the first two covariant indices to obtain the actual local codifferential form. -/
def codifferentialChartForm (g : HermitianField M) (A : RealForm M (k + 1)) (x : M.Carrier)
    (z : ComplexVector n) : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ :=
  -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b • (covariantChartForm g A x z a).curryLeft (realVec b)

theorem codifferentialChartForm_coeff (g : HermitianField M) (A : RealForm M (k + 1))
    (hA : SmoothRealForm A) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (I : Fin k → RIdx n) :
    codifferentialChartForm g A x z (fun r => realVec (I r)) =
      codifferentialComponents g x (formComponents A x) z I := by
  simp only [codifferentialChartForm, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, ContinuousAlternatingMap.curryLeft_apply_apply]
  unfold codifferentialComponents
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have ht : Matrix.vecCons (realVec b) (fun r => realVec (I r)) =
      (fun r => realVec (Fin.cons (α := fun _ => RIdx n) b I r)) := by
    funext r
    cases r using Fin.cases <;> rfl
  rw [ht, covariantChartForm_coeff g A hA x hz a (Fin.cons b I)]

theorem codifferentialChartForm_contDiffOn (g : SmoothMetric M) (A : RealForm M (k + 1))
    (hA : SmoothRealForm A) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (codifferentialChartForm g.form A x) (chartTarget x) := by
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I
  apply (codifferentialComponents_contDiffOn g x (formComponents A x) (hA x) I).congr
  intro z hz
  exact codifferentialChartForm_coeff g.form A hA x hz I


/-- Smooth evaluation of an actual variable alternating field on actual variable vectors. -/
theorem contDiffAt_alternatingField_apply {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    (F : D → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (V : Fin k → D → ComplexVector n) (z : D)
    (hF : ContDiffAt ℝ ∞ F z) (hV : ∀ i, ContDiffAt ℝ ∞ (V i) z) :
    ContDiffAt ℝ ∞ (fun y => F y (fun i => V i y)) z := by
  classical
  have heval : (fun y => F y (fun i => V i y)) =
      (fun y => ∑ I : Fin k → RIdx n,
        (∏ r, (realModelBasis n).repr (V r y) (I r)) * F y (fun r => realVec (I r))) := by
    funext y
    calc
      F y (fun i => V i y) =
          F y (fun r => ∑ i, (realModelBasis n).repr (V r y) i • realVec i) := by
        congr 1
        funext r
        simpa only [realModelBasis_apply] using ((realModelBasis n).sum_repr (V r y)).symm
      _ = ∑ I : Fin k → RIdx n,
          F y (fun r => (realModelBasis n).repr (V r y) (I r) • realVec (I r)) :=
        (F y).map_sum (fun r i => (realModelBasis n).repr (V r y) i • realVec i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro I _
        exact (F y).map_smul_univ _ _
  rw [heval]
  apply ContDiffAt.sum
  intro I _
  have hcoord (r : Fin k) : ContDiffAt ℝ ∞
      (fun y => (realModelBasis n).repr (V r y) (I r)) z := by
    with_unfolding_all
      exact ((realModelBasis n).coord (I r)).toContinuousLinearMap.contDiff.contDiffAt.comp z (hV r)
  have hcoeff : ContDiffAt ℝ ∞ (fun y => F y (fun r => realVec (I r))) z := by
    with_unfolding_all
      exact (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).contDiff.contDiffAt.comp z hF
  exact (contDiffAt_prod (fun r _ => hcoord r)).mul hcoeff

/-- Transport a genuine model alternating test to the actual tangent fibres;
the scalar zero extension is the already verified upstream construction. -/
def chartFormPushforward (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) : RealForm M k :=
  fun y => (L18Aux.chartPushforwardZero x P y).compContinuousLinearMap
    (tangentCoordsRealContinuousLinearMap x y)

theorem chartFormPushforward_to_chart (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (chartFormPushforward x P) x z = P z := by
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [chartForm, chartFormPushforward, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, chartRealContinuousLinearMap_apply, tangentCoordsRealContinuousLinearMap_apply]
  rw [L18Aux.chartPushforwardZero_chartInv x P hz]
  congr 1
  funext r
  exact L12Aux.tangentCoords_chartVec x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz) (v r)

theorem chartFormPushforward_support_subset (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    closure {y | chartFormPushforward x P y ≠ 0} ⊆ tsupport (L18Aux.chartPushforwardZero x P) := by
  apply closure_mono
  intro y hy
  change L18Aux.chartPushforwardZero x P y ≠ 0
  intro hzero
  exact hy (by
    apply ContinuousAlternatingMap.ext
    intro v
    change (L18Aux.chartPushforwardZero x P y) ((tangentCoordsRealContinuousLinearMap x y) ∘ v) = 0
    rw [hzero]
    rfl)

theorem chartFormPushforward_compactlySupported (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x) :
    CompactlySupportedRealForm (chartFormPushforward x P) :=
  (L18Aux.chartPushforwardZero_properties x hP hcP hPO).1.of_isClosed_subset
    isClosed_closure (chartFormPushforward_support_subset x P)

theorem chartFormPushforward_source_support (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x) :
    closure {y | chartFormPushforward x P y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source :=
  (chartFormPushforward_support_subset x P).trans
    (L18Aux.chartPushforwardZero_properties x hP hcP hPO).2.2


/-- The dependent tangent-fibre reconstruction of a genuine compact model
alternating test is smooth in every chart, including across its zero extension. -/
theorem chartFormPushforward_smooth (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x) :
    SmoothRealForm (chartFormPushforward x P) := by
  let Ξ := L18Aux.chartPushforwardZero x P
  have hsupp : tsupport Ξ ⊆ (extChartAt (ComplexModel n) x).source :=
    (L18Aux.chartPushforwardZero_properties x hP hcP hPO).2.2
  intro b I z hz
  have hi : ContinuousAt (chartInv b) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  by_cases hy : chartInv b z ∈ (extChartAt (ComplexModel n) x).source
  · have hT : ContDiffAt ℝ ∞ (fun t => chartPt x (chartInv b t)) z :=
      (L18Aux.chartTransition_contDiffAt b x hz hy).restrict_scalars ℝ
    have hfield : ContDiffAt ℝ ∞ (fun t => P (chartPt x (chartInv b t))) z :=
      hP.contDiffAt.comp z hT
    have hderiv : ContDiffAt ℝ ∞ (fderiv ℝ (fun t => chartPt x (chartInv b t))) z :=
      hT.fderiv_right (m := ∞) (by simp)
    have hvec (i : Fin k) : ContDiffAt ℝ ∞
        (fun t => fderiv ℝ (fun w => chartPt x (chartInv b w)) t (realVec (I i))) z :=
      hderiv.clm_apply contDiffAt_const
    have heval := contDiffAt_alternatingField_apply
      (fun t => P (chartPt x (chartInv b t)))
      (fun i t => fderiv ℝ (fun w => chartPt x (chartInv b w)) t (realVec (I i))) z hfield hvec
    have heq : (fun t => formComponents (chartFormPushforward x P) b t I) =ᶠ[𝓝 z]
        (fun t => P (chartPt x (chartInv b t))
          (fun i => fderiv ℝ (fun w => chartPt x (chartInv b w)) t (realVec (I i)))) := by
      filter_upwards [chartForm_pullback_eventuallyEq (chartFormPushforward x P) b x hz hy,
        hi.tendsto.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hy)]
        with t ht hyt
      have hrec : chartForm (chartFormPushforward x P) x (chartPt x (chartInv b t)) =
          P (chartPt x (chartInv b t)) :=
        chartFormPushforward_to_chart x P ((extChartAt (ComplexModel n) x).map_source hyt)
      rw [← chartForm_apply_basis (chartFormPushforward x P) b t I, ht, hrec]
      rfl
    exact (heval.congr_of_eventuallyEq heq).contDiffWithinAt
  · have hy' : chartInv b z ∉ tsupport Ξ := fun h => hy (hsupp h)
    have hzero : ∀ᶠ y in 𝓝 (chartInv b z), Ξ y = 0 := by
      filter_upwards [(isClosed_tsupport Ξ).compl_mem_nhds hy'] with y hy0
      exact image_eq_zero_of_notMem_tsupport hy0
    have heq : (fun t => formComponents (chartFormPushforward x P) b t I) =ᶠ[𝓝 z]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hi.tendsto.eventually hzero] with t ht
      change (Ξ (chartInv b t)) ((tangentCoordsRealContinuousLinearMap x (chartInv b t)) ∘
        (fun r => chartVec b (chartInv b t) (realVec (I r)))) = 0
      rw [ht]
      rfl
    have hconst : ContDiffAt ℝ ∞ (fun _ : ComplexVector n => (0 : ℝ)) z := contDiffAt_const
    exact (hconst.congr_of_eventuallyEq heq).contDiffWithinAt

theorem chartFormPushforward_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x) :
    L2RealForm g.form μ (chartFormPushforward x P) :=
  smooth_compactlySupported_l2RealForm g μ hμ (chartFormPushforward x P)
    (chartFormPushforward_smooth x P hP hcP hPO)
    (chartFormPushforward_compactlySupported x P hP hcP hPO)


/-- The actual codifferential form computed in one fixed chart; its global
chart independence is a separate theorem target. -/
def chartCodifferentialRealForm (g : HermitianField M) (A : RealForm M (k + 1)) (x : M.Carrier) :
    RealForm M k :=
  fun y => (codifferentialChartForm g A x (chartPt x y)).compContinuousLinearMap
    (tangentCoordsRealContinuousLinearMap x y)

theorem chartCodifferentialRealForm_to_chart (g : HermitianField M) (A : RealForm M (k + 1))
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (chartCodifferentialRealForm g A x) x z = codifferentialChartForm g A x z := by
  have hp : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [chartForm, chartCodifferentialRealForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, chartRealContinuousLinearMap_apply, tangentCoordsRealContinuousLinearMap_apply]
  rw [hp]
  congr 1
  funext r
  exact L12Aux.tangentCoords_chartVec x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz) (v r)

theorem chartCodifferentialRealForm_coeff (g : HermitianField M) (A : RealForm M (k + 1))
    (hA : SmoothRealForm A) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (I : Fin k → RIdx n) :
    formComponents (chartCodifferentialRealForm g A x) x z I =
      codifferentialComponents g x (formComponents A x) z I := by
  rw [← chartForm_apply_basis (chartCodifferentialRealForm g A x) x z I,
    chartCodifferentialRealForm_to_chart g A x hz, codifferentialChartForm_coeff g A hA x hz I]

/-- A local form Green identity for computed operators, without assuming a
full-chart `RepresentsCodifferential` relation for the local candidate. -/
theorem integral_exterior_chartCodifferential (g : SmoothMetric M) (A : RealForm M k)
    (H : RealForm M (k + 1)) (hA : SmoothRealForm A) (hH : SmoothRealForm H) (x : M.Carrier)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ∫ z, φ z * Real.sqrt (realMetricFn g.form x z).det *
      (formInner g.form (exteriorRealForm A) H (chartInv x z) -
        formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z)) ∂lebesgueC n =
      -(Nat.factorial k : ℝ)⁻¹ *
        (∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x (formComponents A x)
          (raisedFirstComponents g.form x (formComponents H x)) a z ∂lebesgueC n) := by
  let V := raisedFirstComponents g.form x (formComponents H x)
  let c : ℝ := (Nat.factorial k : ℝ)⁻¹
  have hV (a : RIdx n) (I : Fin k → RIdx n) :
      ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x) :=
    raisedFirstComponents_contDiffOn g x (formComponents H x) (hH x) a I
  have hpoint {z : ComplexVector n} (hz : z ∈ chartTarget x) :
      c * (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z) =
      formInner g.form (exteriorRealForm A) H (chartInv x z) -
        formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z) := by
    have hdelta : formComponents (chartCodifferentialRealForm g.form H x) x z =
        codifferentialComponents g.form x (formComponents H x) z := by
      funext I
      exact chartCodifferentialRealForm_coeff g.form H hH x hz I
    dsimp only [c, V]
    rw [tensorCovariantGreenTerm_raisedFirst g x (formComponents A x) (formComponents H x) (hH x) hz,
      formInner_exterior_covariant_in_chart g.form A (exteriorRealForm A) H
        (exteriorRealForm_represents A hA) x hz,
      formInner_chartInv_eq_tensorPairing g.form A (chartCodifferentialRealForm g.form H x) x hz, hdelta]
    ring
  have heq (z : ComplexVector n) :
      φ z * Real.sqrt (realMetricFn g.form x z).det *
        (formInner g.form (exteriorRealForm A) H (chartInv x z) -
          formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z)) =
      c * (φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z)) := by
    by_cases hz : z ∈ chartTarget x
    · rw [← hpoint hz]
      ring
    · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      simp only [hzero, zero_mul, mul_zero]
  calc
    _ = ∫ z, c * (φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z)) ∂lebesgueC n :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = c * (∫ z, φ z * Real.sqrt (realMetricFn g.form x z).det *
        (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z) ∂lebesgueC n) :=
      integral_const_mul c _
    _ = c * (-(∫ z, ∑ a, rDeriv φ z a * tensorMetricFlux g.form x (formComponents A x) V a z
        ∂lebesgueC n)) := by
      rw [integral_tensor_covariant_derivative g x (formComponents A x) V (hA x) hV hφ hcφ hφO]
    _ = _ := by
      dsimp only [c, V]
      ring

/-- Only coefficients in the chosen chart are needed for local smoothness of
the actual metric pairing. -/
theorem formInner_chart_contDiffOn_of_components (g : SmoothMetric M) (A B : RealForm M k)
    (x : M.Carrier)
    (hA : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents A x z I) (chartTarget x))
    (hB : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents B x z I) (chartTarget x)) :
    ContDiffOn ℝ ∞ (fun z => formInner g.form A B (chartInv x z)) (chartTarget x) := by
  apply (contDiffOn_const.mul (tensorCoefficientPairing_contDiffOn
    (fun z => (realMetricFn g.form x z)⁻¹) (formComponents A x) (formComponents B x)
    (chartTarget x) (L18Aux.realMetricFn_inverse_contDiffOn g x) hA hB)).congr
  intro z hz
  exact formInner_chartInv_eq_tensorPairing g.form A B x hz

theorem formInner_continuousOn_chart_of_components (g : SmoothMetric M) (A B : RealForm M k)
    (x : M.Carrier)
    (hA : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents A x z I) (chartTarget x))
    (hB : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents B x z I) (chartTarget x)) :
    ContinuousOn (formInner g.form A B) (extChartAt (ComplexModel n) x).source := by
  have hc := (formInner_chart_contDiffOn_of_components g A B x hA hB).continuousOn
  have hpt : ContinuousOn (chartPt x) (extChartAt (ComplexModel n) x).source := by
    simpa only [extChartAt_source] using chartPt_continuousOn x
  apply (hc.comp hpt (fun y hy => (extChartAt (ComplexModel n) x).map_source hy)).congr
  intro y hy
  change formInner g.form A B y = formInner g.form A B (chartInv x (chartPt x y))
  have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  rw [hi]

theorem formInner_eq_zero_of_left_eq_zero (g : HermitianField M) (A B : RealForm M k)
    (y : M.Carrier) (hy : A y = 0) : formInner g A B y = 0 := by
  have hc := (formComponents_center_eq_zero_iff A y).mpr hy
  simp only [formInner, hc, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

theorem formInner_support_subset_left (g : HermitianField M) (A B : RealForm M k) :
    tsupport (formInner g A B) ⊆ closure {y | A y ≠ 0} := by
  apply closure_mono
  intro y hy
  exact fun hzero => hy (formInner_eq_zero_of_left_eq_zero g A B y hzero)

theorem formInner_hasCompactSupport_left (g : HermitianField M) (A B : RealForm M k)
    (hcA : CompactlySupportedRealForm A) : HasCompactSupport (formInner g A B) :=
  hcA.of_isClosed_subset isClosed_closure (formInner_support_subset_left g A B)

/-- Compact support of the first factor makes pairing with a smooth local
codifferential a globally continuous scalar function. -/
theorem formInner_chartCodifferential_continuous (g : SmoothMetric M) (A : RealForm M k)
    (H : RealForm M (k + 1)) (hA : SmoothRealForm A) (hH : SmoothRealForm H)
    (x : M.Carrier) (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    Continuous (formInner g.form A (chartCodifferentialRealForm g.form H x)) := by
  have hlocal : ContinuousOn (formInner g.form A (chartCodifferentialRealForm g.form H x))
      (extChartAt (ComplexModel n) x).source := by
    apply formInner_continuousOn_chart_of_components g A _ x (hA x)
    intro I
    apply (codifferentialComponents_contDiffOn g x (formComponents H x) (hH x) I).congr
    intro z hz
    exact chartCodifferentialRealForm_coeff g.form H hH x hz I
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y ∈ closure {y | A y ≠ 0}
  · exact hlocal.continuousAt ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (hAx hy))
  · have heq : formInner g.form A (chartCodifferentialRealForm g.form H x) =ᶠ[𝓝 y]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [isClosed_closure.compl_mem_nhds hy] with t ht
      exact formInner_eq_zero_of_left_eq_zero g.form A _ t (by
        by_contra hneq
        exact ht (subset_closure hneq))
    exact continuousAt_const.congr heq.symm

theorem formInner_chartCodifferential_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (H : RealForm M (k + 1))
    (hA : SmoothRealForm A) (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A)
    (x : M.Carrier) (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    Integrable (formInner g.form A (chartCodifferentialRealForm g.form H x)) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  exact (formInner_chartCodifferential_continuous g A H hA hH x hAx).integrable_of_hasCompactSupport
    (formInner_hasCompactSupport_left g.form A _ hcA)

theorem smooth_compact_formInner_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcA : CompactlySupportedRealForm A) :
    Integrable (formInner g.form A B) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  exact (formInner_continuous g A B hA hB).integrable_of_hasCompactSupport
    (formInner_hasCompactSupport_left g.form A B hcA)

/-- A compactly supported C¹ scalar function has zero integral of every
directional derivative, for the actual Haar measure. -/
theorem integral_compact_fderiv_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) (v : E) :
    (∫ z, fderiv ℝ f z v ∂ν) = 0 := by
  have hdi : Integrable (fun z => fderiv ℝ f z v) ν :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcf.fderiv_apply ℝ v)
  have hi : Integrable f ν := hf.continuous.integrable_of_hasCompactSupport hcf
  have hp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := ν) (f := fun _ : E => (1 : ℝ)) (g := f) (v := v)
    (by simpa using (integrable_zero E ℝ ν)) (by simpa using hdi) (by simpa using hi)
    (fun _ _ => differentiableAt_const (c := (1 : ℝ)))
    (fun z _ => hf.differentiable one_ne_zero z)
  simpa only [one_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul,
    integral_zero, neg_zero] using hp

/-- Flux against a genuine compact model alternating test is itself a
globally smooth compactly supported scalar function. -/
theorem tensorMetricFlux_modelTest_properties (g : SmoothMetric M) (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x)
    (V : RIdx n → FormComponents n k)
    (hV : ∀ a I, ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x)) (a : RIdx n) :
    ContDiff ℝ ∞ (tensorMetricFlux g.form x (fun z I => P z (fun r => realVec (I r))) V a) ∧
      HasCompactSupport (tensorMetricFlux g.form x (fun z I => P z (fun r => realVec (I r))) V a) ∧
      tsupport (tensorMetricFlux g.form x (fun z I => P z (fun r => realVec (I r))) V a) ⊆ tsupport P := by
  let F : FormComponents n k := fun z I => P z (fun r => realVec (I r))
  have hF (I : Fin k → RIdx n) : ContDiffOn ℝ ∞ (fun z => F z I) (chartTarget x) := by
    exact ((ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
      (fun r => realVec (I r))).contDiff.comp hP).contDiffOn
  have hzero {z : ComplexVector n} (hz : z ∉ tsupport P) :
      tensorMetricFlux g.form x F V a z = 0 := by
    have hp := image_eq_zero_of_notMem_tsupport hz
    simp [tensorMetricFlux, tensorCoefficientPairing, F, hp]
  have hs : tsupport (tensorMetricFlux g.form x F V a) ⊆ tsupport P := by
    apply closure_minimal _ (isClosed_tsupport P)
    intro z hz
    by_contra hp
    exact hz (hzero hp)
  refine ⟨?_, hcP.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport P
  · exact (tensorMetricFlux_contDiffOn g x F V hF hV a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (hPO hz))
  · have heq : tensorMetricFlux g.form x F V a =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport P).compl_mem_nhds hz] with t ht
      exact hzero ht
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The computed local Green difference is exactly the actual coordinate
divergence of the metric flux. -/
theorem exterior_chartCodifferential_divergence (g : SmoothMetric M) (A : RealForm M k)
    (H : RealForm M (k + 1)) (hA : SmoothRealForm A) (hH : SmoothRealForm H) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    Real.sqrt (realMetricFn g.form x z).det *
      (formInner g.form (exteriorRealForm A) H (chartInv x z) -
        formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z)) =
      (Nat.factorial k : ℝ)⁻¹ * ∑ a, rDeriv
        (tensorMetricFlux g.form x (formComponents A x)
          (raisedFirstComponents g.form x (formComponents H x)) a) z a := by
  let V := raisedFirstComponents g.form x (formComponents H x)
  have hV (a : RIdx n) (I : Fin k → RIdx n) :
      ContDiffOn ℝ ∞ (fun w => V a w I) (chartTarget x) :=
    raisedFirstComponents_contDiffOn g x (formComponents H x) (hH x) a I
  have hdelta : formComponents (chartCodifferentialRealForm g.form H x) x z =
      codifferentialComponents g.form x (formComponents H x) z := by
    funext I
    exact chartCodifferentialRealForm_coeff g.form H hH x hz I
  have hp : (Nat.factorial k : ℝ)⁻¹ *
      (∑ a, tensorCovariantGreenTerm g.form x (formComponents A x) V a z) =
      formInner g.form (exteriorRealForm A) H (chartInv x z) -
        formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z) := by
    dsimp only [V]
    rw [tensorCovariantGreenTerm_raisedFirst g x (formComponents A x) (formComponents H x) (hH x) hz,
      formInner_exterior_covariant_in_chart g.form A (exteriorRealForm A) H
        (exteriorRealForm_represents A hA) x hz,
      formInner_chartInv_eq_tensorPairing g.form A (chartCodifferentialRealForm g.form H x) x hz,
      hdelta]
    ring
  change _ = (Nat.factorial k : ℝ)⁻¹ *
    ∑ a, rDeriv (tensorMetricFlux g.form x (formComponents A x) V a) z a
  rw [← hp]
  simp_rw [tensorMetricFlux_derivative g x (formComponents A x) V (hA x) hV hz]
  rw [← Finset.mul_sum]
  ring

/-- A genuine compact model form test satisfies the local Green identity
without any additional scalar test or boundary term. -/
theorem integral_modelTest_exterior_chartCodifferential (g : SmoothMetric M) (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ContDiff ℝ ∞ P) (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) :
    (∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
      (formInner g.form (exteriorRealForm (chartFormPushforward x P)) H (chartInv x z) -
        formInner g.form (chartFormPushforward x P)
          (chartCodifferentialRealForm g.form H x) (chartInv x z)) ∂lebesgueC n) = 0 := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let A := chartFormPushforward x P
  let F : FormComponents n k := fun z I => P z (fun r => realVec (I r))
  let V := raisedFirstComponents g.form x (formComponents H x)
  let Q := tensorMetricFlux g.form x F V
  have hA : SmoothRealForm A := chartFormPushforward_smooth x P hP hcP hPO
  have hV (a : RIdx n) (I : Fin k → RIdx n) :
      ContDiffOn ℝ ∞ (fun z => V a z I) (chartTarget x) :=
    raisedFirstComponents_contDiffOn g x (formComponents H x) (hH x) a I
  have hQ (a : RIdx n) : ContDiff ℝ ∞ (Q a) ∧ HasCompactSupport (Q a) ∧
      tsupport (Q a) ⊆ tsupport P :=
    tensorMetricFlux_modelTest_properties g x P hP hcP hPO V hV a
  have hcoeff {z : ComplexVector n} (hz : z ∈ chartTarget x) : formComponents A x z = F z := by
    funext I
    rw [← chartForm_apply_basis A x z I, chartFormPushforward_to_chart x P hz]
  have hd {z : ComplexVector n} (hz : z ∈ chartTarget x) (a : RIdx n) :
      rDeriv (tensorMetricFlux g.form x (formComponents A x) V a) z a = rDeriv (Q a) z a := by
    have heq : tensorMetricFlux g.form x (formComponents A x) V a =ᶠ[𝓝 z] Q a := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
      simp only [tensorMetricFlux, hcoeff ht, Q]
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec a)) heq.fderiv_eq
  have hpoint {z : ComplexVector n} (hz : z ∈ chartTarget x) :
      Real.sqrt (realMetricFn g.form x z).det *
        (formInner g.form (exteriorRealForm A) H (chartInv x z) -
          formInner g.form A (chartCodifferentialRealForm g.form H x) (chartInv x z)) =
        (Nat.factorial k : ℝ)⁻¹ * ∑ a, rDeriv (Q a) z a := by
    rw [exterior_chartCodifferential_divergence g A H hA hH x hz]
    congr 1
    exact Finset.sum_congr rfl (fun a _ => hd hz a)
  have hqi (a : RIdx n) : Integrable (fun z => rDeriv (Q a) z a) (lebesgueC n) :=
    ((((hQ a).1.of_le (by simp) : ContDiff ℝ 1 (Q a)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport ((hQ a).2.1.fderiv_apply ℝ (realVec a))
  have hzero : (∫ z in chartTarget x, ∑ a, rDeriv (Q a) z a ∂lebesgueC n) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · rw [integral_finsetSum Finset.univ (fun a _ => hqi a)]
      apply Finset.sum_eq_zero
      intro a _
      exact integral_compact_fderiv_eq_zero (lebesgueC n) ((hQ a).1.of_le (by simp))
        (hQ a).2.1 (realVec a)
    · apply Finset.sum_eq_zero
      intro a _
      have hn : z ∉ tsupport (Q a) := fun h => hz (hPO ((hQ a).2.2 h))
      simp only [rDeriv, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]
  calc
    _ = ∫ z in chartTarget x, (Nat.factorial k : ℝ)⁻¹ * ∑ a, rDeriv (Q a) z a ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      exact hpoint hz
    _ = (Nat.factorial k : ℝ)⁻¹ *
        (∫ z in chartTarget x, ∑ a, rDeriv (Q a) z a ∂lebesgueC n) := integral_const_mul _ _
    _ = 0 := by rw [hzero, mul_zero]

/-- The actual chart tensor of a dependent form, extended by zero outside
the chart target. -/
def chartFormPullbackZero (x : M.Carrier) (A : RealForm M k) (z : ComplexVector n) :
    (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ :=
  @ite _ (z ∈ chartTarget x) (Classical.propDecidable _) (chartForm A x z) 0

theorem chartFormPullbackZero_chartPt (x : M.Carrier) (A : RealForm M k)
    {y : M.Carrier} (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    chartFormPullbackZero x A (chartPt x y) = chartForm A x (chartPt x y) := by
  have hyt : chartPt x y ∈ chartTarget x := (extChartAt (ComplexModel n) x).map_source hy
  simp only [chartFormPullbackZero, if_pos hyt]

/-- A genuine compact smooth dependent form supported in one chart yields
an actual compact smooth alternating model test, with the precise image
support needed on chart overlaps. -/
theorem chartFormPullbackZero_properties (x : M.Carrier) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    ContDiff ℝ ∞ (chartFormPullbackZero x A) ∧ HasCompactSupport (chartFormPullbackZero x A) ∧
      tsupport (chartFormPullbackZero x A) ⊆ chartTarget x ∧
      tsupport (chartFormPullbackZero x A) ⊆ chartPt x '' closure {y | A y ≠ 0} := by
  let K := chartPt x '' closure {y | A y ≠ 0}
  have hc : IsCompact K := hcA.image_of_continuousOn (by
    have hpt : ContinuousOn (chartPt x) (extChartAt (ComplexModel n) x).source := by
      simpa only [extChartAt_source] using chartPt_continuousOn x
    exact hpt.mono hAx)
  have hKt : K ⊆ chartTarget x := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) x).map_source (hAx hy)
  have hs : Function.support (chartFormPullbackZero x A) ⊆ K := by
    intro z hz
    by_cases hzt : z ∈ chartTarget x
    · have hn : A (chartInv x z) ≠ 0 := by
        intro hzero
        have hcz : chartForm A x z = 0 := by
          apply ContinuousAlternatingMap.ext
          intro v
          simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hzero]
          rfl
        exact hz (by simp only [chartFormPullbackZero, if_pos hzt, hcz])
      exact ⟨chartInv x z, subset_closure hn, (extChartAt (ComplexModel n) x).right_inv hzt⟩
    · exact False.elim (hz (by simp only [chartFormPullbackZero, if_neg hzt]))
  have hts : tsupport (chartFormPullbackZero x A) ⊆ K := closure_minimal hs hc.isClosed
  refine ⟨?_, hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKt, hts⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ K
  · have hzt := hKt hz
    have heq : chartFormPullbackZero x A =ᶠ[𝓝 z] chartForm A x := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hzt] with t ht
      have htt : t ∈ chartTarget x := ht
      simp only [chartFormPullbackZero, if_pos htt]
    exact ((chartForm_contDiffOn A hA x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hzt)).congr_of_eventuallyEq heq
  · have heq : chartFormPullbackZero x A =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hc.isClosed.compl_mem_nhds hz] with t ht
      exact image_eq_zero_of_notMem_tsupport (fun h => ht (hts h))
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Reconstructing the zero pullback recovers the original dependent form
everywhere, using the stated support condition. -/
theorem chartFormPushforward_pullbackZero (x : M.Carrier) (A : RealForm M k)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    chartFormPushforward x (chartFormPullbackZero x A) = A := by
  funext y
  by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
  · apply ContinuousAlternatingMap.ext
    intro v
    have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_pos hy,
      chartFormPullbackZero_chartPt x A hy, chartForm,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      chartRealContinuousLinearMap_apply, tangentCoordsRealContinuousLinearMap_apply]
    change A (chartInv x (chartPt x y))
      (fun i => chartVec x (chartInv x (chartPt x y)) (tangentCoords x y (v i))) = A y v
    rw [hi]
    congr 1
    funext i
    exact L12Aux.chartVec_tangentCoords x y hy (v i)
  · have hzero : A y = 0 := by
      by_contra hneq
      exact hy (hAx (subset_closure hneq))
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, hzero]
    rfl

/-- A fixed-chart codifferential candidate is smoothly represented in every
other chart on the actual chart overlap. -/
theorem chartCodifferentialRealForm_coeff_contDiffAt (g : SmoothMetric M)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget b)
    (hy : chartInv b z ∈ (extChartAt (ComplexModel n) a).source) (I : Fin k → RIdx n) :
    ContDiffAt ℝ ∞ (fun t => formComponents (chartCodifferentialRealForm g.form H a) b t I) z := by
  have hi : ContinuousAt (chartInv b) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz
  have hT : ContDiffAt ℝ ∞ (fun t => chartPt a (chartInv b t)) z :=
    (L18Aux.chartTransition_contDiffAt b a hz hy).restrict_scalars ℝ
  have hc : ContDiffAt ℝ ∞ (codifferentialChartForm g.form H a) (chartPt a (chartInv b z)) :=
    (codifferentialChartForm_contDiffOn g H hH a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds
        ((extChartAt (ComplexModel n) a).map_source hy))
  have hfield : ContDiffAt ℝ ∞
      (fun t => codifferentialChartForm g.form H a (chartPt a (chartInv b t))) z := by
    exact ContDiffAt.comp (f := fun t => chartPt a (chartInv b t))
      (g := codifferentialChartForm g.form H a) z hc hT
  have hderiv : ContDiffAt ℝ ∞ (fderiv ℝ (fun t => chartPt a (chartInv b t))) z :=
    hT.fderiv_right (m := ∞) (by simp)
  have heval := contDiffAt_alternatingField_apply
    (fun t => codifferentialChartForm g.form H a (chartPt a (chartInv b t)))
    (fun i t => fderiv ℝ (fun w => chartPt a (chartInv b w)) t (realVec (I i))) z hfield
    (fun _ => hderiv.clm_apply contDiffAt_const)
  have heq : (fun t => formComponents (chartCodifferentialRealForm g.form H a) b t I) =ᶠ[𝓝 z]
      (fun t => codifferentialChartForm g.form H a (chartPt a (chartInv b t))
        (fun i => fderiv ℝ (fun w => chartPt a (chartInv b w)) t (realVec (I i)))) := by
    filter_upwards [chartForm_pullback_eventuallyEq (chartCodifferentialRealForm g.form H a) b a hz hy,
      hi.tendsto.eventually ((isOpen_extChartAt_source (I := ComplexModel n) a).mem_nhds hy)]
      with t ht hyt
    have hrec : chartForm (chartCodifferentialRealForm g.form H a) a (chartPt a (chartInv b t)) =
        codifferentialChartForm g.form H a (chartPt a (chartInv b t)) :=
      chartCodifferentialRealForm_to_chart g.form H a ((extChartAt (ComplexModel n) a).map_source hyt)
    rw [← chartForm_apply_basis (chartCodifferentialRealForm g.form H a) b t I, ht, hrec]
    rfl
  exact heval.congr_of_eventuallyEq heq

/-- Local form Green transported to the original Riemannian measure, for
every actual compact smooth form supported in the chosen chart. -/
theorem integral_compact_exterior_chartCodifferential (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (H : RealForm M (k + 1)) (hA : SmoothRealForm A)
    (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, formInner g.form (exteriorRealForm A) H y -
      formInner g.form A (chartCodifferentialRealForm g.form H x) y ∂μ) = 0 := by
  let f := fun y => formInner g.form (exteriorRealForm A) H y -
    formInner g.form A (chartCodifferentialRealForm g.form H x) y
  have hf : Continuous f :=
    (formInner_continuous g (exteriorRealForm A) H (exteriorRealForm_smooth A hA) hH).sub
      (formInner_chartCodifferential_continuous g A H hA hH x hAx)
  have hs₁ : tsupport (formInner g.form (exteriorRealForm A) H) ⊆
      (extChartAt (ComplexModel n) x).source :=
    (formInner_support_subset_left g.form _ _).trans
      ((representsExterior_support_subset (exteriorRealForm_represents A hA)).trans hAx)
  have hs₂ : tsupport (formInner g.form A (chartCodifferentialRealForm g.form H x)) ⊆
      (extChartAt (ComplexModel n) x).source :=
    (formInner_support_subset_left g.form _ _).trans hAx
  have hfzero (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) : f y = 0 := by
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs₁ h)),
      image_eq_zero_of_notMem_tsupport (fun h => hy (hs₂ h)), sub_self]
  have hp := chartFormPullbackZero_properties x A hA hcA hAx
  have hlocal := integral_modelTest_exterior_chartCodifferential g x (chartFormPullbackZero x A)
    hp.1 hp.2.1 hp.2.2.1 H hH
  rw [chartFormPushforward_pullbackZero x A hAx] at hlocal
  calc
    _ = ∫ y in (extChartAt (ComplexModel n) x).source, f y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hfzero).symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * f (chartInv x z)
        ∂lebesgueC n := L18Aux.integral_chart_volume g μ hμ x f hf.measurable
    _ = 0 := hlocal

theorem integral_exterior_eq_chartCodifferential (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (H : RealForm M (k + 1)) (hA : SmoothRealForm A)
    (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, formInner g.form (exteriorRealForm A) H y ∂μ) =
      ∫ y, formInner g.form A (chartCodifferentialRealForm g.form H x) y ∂μ := by
  have hi₁ := smooth_compact_formInner_integrable g μ hμ (exteriorRealForm A) H
    (exteriorRealForm_smooth A hA) hH (exteriorRealForm_compactlySupported A hA hcA)
  have hi₂ := formInner_chartCodifferential_integrable g μ hμ A H hA hH hcA x hAx
  have hzero := integral_compact_exterior_chartCodifferential g μ hμ A H hA hH hcA x hAx
  rw [integral_sub hi₁ hi₂] at hzero
  exact sub_eq_zero.mp hzero

/-- Two chart codifferential candidates have zero pairing against every
actual compact smooth form test supported in their overlap. -/
theorem integral_chartCodifferential_sub_eq_zero (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (H : RealForm M (k + 1)) (hA : SmoothRealForm A)
    (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A) (a b : M.Carrier)
    (hAa : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) a).source)
    (hAb : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) b).source) :
    (∫ y, formInner g.form A
      (chartCodifferentialRealForm g.form H a - chartCodifferentialRealForm g.form H b) y ∂μ) = 0 := by
  rw [formInner_sub_right]
  simp only [Pi.sub_apply]
  rw [integral_sub
    (formInner_chartCodifferential_integrable g μ hμ A H hA hH hcA a hAa)
    (formInner_chartCodifferential_integrable g μ hμ A H hA hH hcA b hAb),
    ← integral_exterior_eq_chartCodifferential g μ hμ A H hA hH hcA a hAa,
    ← integral_exterior_eq_chartCodifferential g μ hμ A H hA hH hcA b hAb, sub_self]

/-- The exact support image for dependent alternating chart tests. -/
theorem chartFormPushforward_image_support (x : M.Carrier)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hcP : HasCompactSupport P) (hPO : tsupport P ⊆ chartTarget x) :
    closure {y | chartFormPushforward x P y ≠ 0} ⊆ chartInv x '' tsupport P := by
  have hc : IsCompact (chartInv x '' tsupport P) := hcP.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hPO)
  apply closure_minimal _ hc.isClosed
  intro y hy
  by_cases hys : y ∈ (extChartAt (ComplexModel n) x).source
  · have hn : P (chartPt x y) ≠ 0 := by
      intro hzero
      apply hy
      apply ContinuousAlternatingMap.ext
      intro v
      simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_pos hys,
        ContinuousAlternatingMap.compContinuousLinearMap_apply, hzero]
      rfl
    exact ⟨chartPt x y, subset_closure hn, (extChartAt (ComplexModel n) x).left_inv hys⟩
  · apply False.elim
    apply hy
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hys,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rfl

/-- Multiplying a locally smooth actual alternating model field by a
compact scalar cutoff produces a genuine global compact smooth test. -/
theorem modelForm_cutoff_properties {O : Set (ComplexVector n)} (hO : IsOpen O)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O)
    (F : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (hF : ContDiffOn ℝ ∞ F O) :
    ContDiff ℝ ∞ (fun z => φ z • F z) ∧ HasCompactSupport (fun z => φ z • F z) ∧
      tsupport (fun z => φ z • F z) ⊆ tsupport φ := by
  have hs : tsupport (fun z => φ z • F z) ⊆ tsupport φ := by
    apply closure_mono
    intro z hz
    intro hzero
    exact hz (by change φ z • F z = 0; rw [hzero, zero_smul])
  refine ⟨?_, hcφ.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport φ
  · exact hφ.contDiffAt.smul (hF.contDiffAt (hO.mem_nhds (hφO hz)))
  · have heq : (fun t => φ t • F t) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport φ).compl_mem_nhds hz] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Scalar multiplication of a chart tensor reconstructs the actual scalar
multiple of the original form, including the zero extension. -/
theorem chartFormPushforward_scalar_chartForm (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (A : RealForm M k) :
    chartFormPushforward x (fun z => φ z • chartForm A x z) =
      multiplyRealForm (L18Aux.chartPushforwardZero x φ) A := by
  funext y
  apply ContinuousAlternatingMap.ext
  intro v
  by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
  · have hi : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
    simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_pos hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply,
      multiplyRealForm, smul_eq_mul]
    change φ (chartPt x y) * A (chartInv x (chartPt x y))
      (fun i => chartVec x (chartInv x (chartPt x y)) (tangentCoords x y (v i))) =
      φ (chartPt x y) * A y v
    rw [hi]
    congr 2
    funext i
    exact L12Aux.chartVec_tangentCoords x y hy (v i)
  · simp only [chartFormPushforward, L18Aux.chartPushforwardZero, if_neg hy,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, multiplyRealForm, zero_smul]
    rfl

theorem formInner_multiplyRealForm_left (g : HermitianField M) (η : M.Carrier → ℝ)
    (A B : RealForm M k) (y : M.Carrier) :
    formInner g (multiplyRealForm η A) B y = η y * formInner g A B y := by
  have hy : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hc : formComponents (multiplyRealForm η A) y (chartPt y y) =
      formComponents ((η y) • A) y (chartPt y y) := by
    funext I
    simp only [formComponents_multiplyRealForm, formComponents_smul, Pi.smul_apply,
      smul_eq_mul, inChart, hy]
  calc
    _ = formInner g ((η y) • A) B y := by simp only [formInner, hc]
    _ = _ := congrFun (formInner_smul_left g (η y) A B) y

/-- The genuine overlap of two charts expressed in the first model. -/
def formChartOverlap (a b : M.Carrier) : Set (ComplexVector n) :=
  {z | z ∈ chartTarget a ∧ chartInv a z ∈ (extChartAt (ComplexModel n) b).source}

theorem formChartOverlap_isOpen (a b : M.Carrier) : IsOpen (formChartOverlap a b) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hi : ContinuousAt (chartInv a) z := by
    with_unfolding_all
      exact continuousAt_extChartAt_symm'' (I := ComplexModel n) hz.1
  exact inter_mem ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz.1)
    (hi.tendsto.eventually ((isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hz.2))

theorem chartCodifferential_difference_contDiffOn (g : SmoothMetric M)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (a b : M.Carrier) :
    ContDiffOn ℝ ∞ (chartForm
      (chartCodifferentialRealForm g.form H a - chartCodifferentialRealForm g.form H b) a)
      (formChartOverlap a b) := by
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I z hz
  have ha := chartCodifferentialRealForm_coeff_contDiffAt g H hH a a hz.1
    ((extChartAt (ComplexModel n) a).map_target hz.1) I
  have hb := chartCodifferentialRealForm_coeff_contDiffAt g H hH b a hz.1 hz.2 I
  change ContDiffWithinAt ℝ ∞ (fun t =>
    formComponents (chartCodifferentialRealForm g.form H a) a t I -
      formComponents (chartCodifferentialRealForm g.form H b) a t I) (formChartOverlap a b) z
  exact (ha.sub hb).contDiffWithinAt

theorem formInner_chart_contDiffOn_subset (g : SmoothMetric M) (A B : RealForm M k)
    (x : M.Carrier) {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x)
    (hA : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents A x z I) O)
    (hB : ∀ I, ContDiffOn ℝ ∞ (fun z => formComponents B x z I) O) :
    ContDiffOn ℝ ∞ (fun z => formInner g.form A B (chartInv x z)) O := by
  apply (contDiffOn_const.mul (tensorCoefficientPairing_contDiffOn
    (fun z => (realMetricFn g.form x z)⁻¹) (formComponents A x) (formComponents B x) O
    (fun i j => (L18Aux.realMetricFn_inverse_contDiffOn g x i j).mono hOt) hA hB)).congr
  intro z hz
  exact formInner_chartInv_eq_tensorPairing g.form A B x (hOt hz)

/-- The computed codifferential is independent of the chart on actual
overlaps. The proof tests the difference against its own nonnegative compact
cutoff, using the original Riemannian measure and the positive tensor metric. -/
theorem chartCodifferentialRealForm_eq_on_overlap (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (a b y : M.Carrier)
    (hya : y ∈ (extChartAt (ComplexModel n) a).source)
    (hyb : y ∈ (extChartAt (ComplexModel n) b).source) :
    chartCodifferentialRealForm g.form H a y = chartCodifferentialRealForm g.form H b y := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let O := formChartOverlap a b
  let D := chartCodifferentialRealForm g.form H a - chartCodifferentialRealForm g.form H b
  let z₀ := chartPt a y
  have hO : IsOpen O := formChartOverlap_isOpen a b
  have hOt : O ⊆ chartTarget a := fun _ hz => hz.1
  have hinv : chartInv a z₀ = y := (extChartAt (ComplexModel n) a).left_inv hya
  have hz₀ : z₀ ∈ O := ⟨(extChartAt (ComplexModel n) a).map_source hya, by simpa only [hinv] using hyb⟩
  obtain ⟨φ, hφO, hcφ, hφ, hφrange, hφ₀⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hO.mem_nhds hz₀)
  have hφnonneg (z : ComplexVector n) : 0 ≤ φ z := (hφrange ⟨z, rfl⟩).1
  have hD : ContDiffOn ℝ ∞ (chartForm D a) O := chartCodifferential_difference_contDiffOn g H hH a b
  let P := fun z => φ z • chartForm D a z
  let C := chartFormPushforward a P
  let η := L18Aux.chartPushforwardZero a φ
  have hP := modelForm_cutoff_properties hO hφ hcφ hφO (chartForm D a) hD
  have hPt : tsupport P ⊆ chartTarget a := hP.2.2.trans (hφO.trans hOt)
  have hC : SmoothRealForm C := chartFormPushforward_smooth a P hP.1 hP.2.1 hPt
  have hcC : CompactlySupportedRealForm C := chartFormPushforward_compactlySupported a P hP.1 hP.2.1 hPt
  have hCa : closure {t | C t ≠ 0} ⊆ (extChartAt (ComplexModel n) a).source :=
    chartFormPushforward_source_support a P hP.1 hP.2.1 hPt
  have hCb : closure {t | C t ≠ 0} ⊆ (extChartAt (ComplexModel n) b).source := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := chartFormPushforward_image_support a P hP.2.1 hPt ht
    exact (hφO (hP.2.2 hz)).2
  have hCeq : C = multiplyRealForm η D := chartFormPushforward_scalar_chartForm a φ D
  have hpair (t : M.Carrier) : formInner g.form C D t = η t * formNormSq g.form D t := by
    rw [hCeq]
    exact formInner_multiplyRealForm_left g.form η D D t
  have hzero : (∫ t, formInner g.form C D t ∂μ) = 0 :=
    integral_chartCodifferential_sub_eq_zero g μ hμ C H hC hH hcC a b hCa hCb
  have hfc : Continuous (formInner g.form C D) := by
    change Continuous (formInner g.form C
      (chartCodifferentialRealForm g.form H a - chartCodifferentialRealForm g.form H b))
    rw [formInner_sub_right]
    exact (formInner_chartCodifferential_continuous g C H hC hH a hCa).sub
      (formInner_chartCodifferential_continuous g C H hC hH b hCb)
  have hfsource : tsupport (formInner g.form C D) ⊆ (extChartAt (ComplexModel n) a).source :=
    (formInner_support_subset_left g.form C D).trans hCa
  have hmodel : (∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det *
      formInner g.form C D (chartInv a z) ∂lebesgueC n) = 0 := by
    calc
      _ = ∫ t in (extChartAt (ComplexModel n) a).source, formInner g.form C D t ∂μ :=
        (L18Aux.integral_chart_volume g μ hμ a _ hfc.measurable).symm
      _ = ∫ t, formInner g.form C D t ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht =>
          image_eq_zero_of_notMem_tsupport (fun h => ht (hfsource h)))
      _ = 0 := hzero
  let q := fun z => Real.sqrt (realMetricFn g.form a z).det * φ z * formNormSq g.form D (chartInv a z)
  have hqzero : (∫ z, q z ∂lebesgueC n) = 0 := by
    calc
      _ = ∫ z in chartTarget a, q z ∂lebesgueC n :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
          have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hOt (hφO h)))
          simp only [q, hφz, mul_zero, zero_mul])).symm
      _ = ∫ z in chartTarget a, Real.sqrt (realMetricFn g.form a z).det *
          formInner g.form C D (chartInv a z) ∂lebesgueC n := by
        apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) a).measurableSet
        intro z hz
        have hη : η (chartInv a z) = φ z := L18Aux.chartPushforwardZero_chartInv a φ hz
        change Real.sqrt (realMetricFn g.form a z).det * φ z * formNormSq g.form D (chartInv a z) =
          Real.sqrt (realMetricFn g.form a z).det * formInner g.form C D (chartInv a z)
        rw [hpair, hη]
        ring
      _ = 0 := hmodel
  have hDI (I : Fin k → RIdx n) : ContDiffOn ℝ ∞ (fun z => formComponents D a z I) O :=
    (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).contDiff.comp_contDiffOn hD
  have hN : ContinuousOn (fun z => formNormSq g.form D (chartInv a z)) O :=
    (formInner_chart_contDiffOn_subset g D D a hOt hDI hDI).continuousOn
  have hρ : ContinuousOn (fun z => Real.sqrt (realMetricFn g.form a z).det) O :=
    (L18Aux.volumeDensity_contDiffOn g a).continuousOn.mono hOt
  have hqi : Integrable q (lebesgueC n) := by
    have hi := L18Aux.integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO (hρ.mul hN)
    convert hi using 1
    funext z
    dsimp only [q, Pi.mul_apply]
    ring
  have hqnonneg (z : ComplexVector n) : 0 ≤ q z :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hφnonneg z)) (formNormSq_nonneg g.form D _)
  have hqae : q =ᵐ[lebesgueC n] 0 := (integral_eq_zero_iff_of_nonneg hqnonneg hqi).mp hqzero
  have hqc : ContinuousOn q O := (hρ.mul hφ.continuous.continuousOn).mul hN
  have hq₀ : q z₀ = 0 := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hqae) hO hqc
    continuousOn_const hz₀
  have hρpos : 0 < Real.sqrt (realMetricFn g.form a z₀).det :=
    Real.sqrt_pos.mpr (realMetricFn_posDef_of_mem_target g.form a hz₀.1).det_pos
  change Real.sqrt (realMetricFn g.form a z₀).det * φ z₀ * formNormSq g.form D (chartInv a z₀) = 0 at hq₀
  rw [hφ₀, mul_one, hinv] at hq₀
  have hNzero : formNormSq g.form D y = 0 := (mul_eq_zero.mp hq₀).resolve_left (ne_of_gt hρpos)
  have hDy := (formNormSq_eq_zero_iff g.form D y).mp hNzero
  exact sub_eq_zero.mp hDy

/-- The actual global codifferential, evaluated using the chart at each point.
Its full-chart reconstruction is proved below from chart independence. -/
def codifferentialRealForm (g : HermitianField M) (H : RealForm M (k + 1)) : RealForm M k :=
  fun y => chartCodifferentialRealForm g H y y

theorem codifferentialRealForm_eq_chart (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) :
    codifferentialRealForm g.form H y = chartCodifferentialRealForm g.form H x y :=
  chartCodifferentialRealForm_eq_on_overlap g μ hμ H hH y x y (mem_extChartAt_source y) hy

/-- The constructed global codifferential satisfies exactly the frozen
reconstruction relation on the complete target of every chart. -/
theorem codifferentialRealForm_represents (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) :
    RepresentsCodifferential g.form H (codifferentialRealForm g.form H) := by
  intro x z hz I
  have hv := codifferentialRealForm_eq_chart g μ hμ H hH x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz)
  have hc : formComponents (codifferentialRealForm g.form H) x z I =
      formComponents (chartCodifferentialRealForm g.form H x) x z I := by
    unfold formComponents
    rw [hv]
  exact hc.trans (chartCodifferentialRealForm_coeff g.form H hH x hz I)

theorem codifferentialRealForm_smooth (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) :
    SmoothRealForm (codifferentialRealForm g.form H) :=
  representsCodifferential_smooth g hH (codifferentialRealForm_represents g μ hμ H hH)

theorem representsCodifferential_eq_zero_of_eventuallyEq_zero (g : HermitianField M)
    {A : RealForm M (k + 1)} {B : RealForm M k} (hAB : RepresentsCodifferential g A B)
    (x : M.Carrier) (hA : ∀ᶠ y in 𝓝 x, A y = 0) : B x = 0 := by
  apply (formComponents_center_eq_zero_iff B x).mp
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hlocal : formComponents A x =ᶠ[𝓝 (chartPt x x)] 0 := by
    have hA' : ∀ᶠ y in 𝓝 (chartInv x (chartPt x x)), A y = (0 : RealForm M (k + 1)) y := by
      simpa only [hx, Pi.zero_apply] using hA
    simpa only [formComponents_zero] using formComponents_eventuallyEq_of_eventuallyEq x ht hA'
  have hd := codifferentialComponents_congr_nhds g x hlocal
  funext I
  rw [hAB x (chartPt x x) ht I]
  exact (congrFun hd I).trans (by rw [codifferentialComponents_zero]; rfl)

theorem representsCodifferential_support_subset (g : HermitianField M)
    {A : RealForm M (k + 1)} {B : RealForm M k} (hAB : RepresentsCodifferential g A B) :
    closure {x | B x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra h
  have hA : ∀ᶠ y in 𝓝 x, A y = 0 := by
    filter_upwards [isClosed_closure.compl_mem_nhds h] with y hy
    by_contra hne
    exact hy (subset_closure hne)
  exact hx (representsCodifferential_eq_zero_of_eventuallyEq_zero g hAB x hA)

theorem codifferentialRealForm_support_subset (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) :
    closure {y | codifferentialRealForm g.form H y ≠ 0} ⊆ closure {y | H y ≠ 0} :=
  representsCodifferential_support_subset g.form (codifferentialRealForm_represents g μ hμ H hH)

theorem codifferentialRealForm_compactlySupported (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (hcH : CompactlySupportedRealForm H) :
    CompactlySupportedRealForm (codifferentialRealForm g.form H) :=
  hcH.of_isClosed_subset isClosed_closure (codifferentialRealForm_support_subset g μ hμ H hH)

theorem codifferentialRealForm_l2 (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (H : RealForm M (k + 1)) (hH : SmoothRealForm H) (hcH : CompactlySupportedRealForm H) :
    L2RealForm g.form μ (codifferentialRealForm g.form H) :=
  smooth_compactlySupported_l2RealForm g μ hμ _ (codifferentialRealForm_smooth g μ hμ H hH)
    (codifferentialRealForm_compactlySupported g μ hμ H hH hcH)

/-- Green with the actual global codifferential and the original measure,
for every compact smooth test supported in one chart. -/
theorem integral_exterior_codifferential_chartSupport (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (H : RealForm M (k + 1)) (hA : SmoothRealForm A)
    (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, formInner g.form (exteriorRealForm A) H y ∂μ) =
      ∫ y, formInner g.form A (codifferentialRealForm g.form H) y ∂μ := by
  rw [integral_exterior_eq_chartCodifferential g μ hμ A H hA hH hcA x hAx]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    by_cases hy : y ∈ (extChartAt (ComplexModel n) x).source
    · have hv := codifferentialRealForm_eq_chart g μ hμ H hH x y hy
      have hc : formComponents (codifferentialRealForm g.form H) y (chartPt y y) =
          formComponents (chartCodifferentialRealForm g.form H x) y (chartPt y y) := by
        funext I
        rw [formComponents_center_apply, formComponents_center_apply, hv]
      simp only [formInner, hc]
    · have hz : A y = 0 := by
        by_contra hneq
        exact hy (hAx (subset_closure hneq))
      rw [formInner_eq_zero_of_left_eq_zero g.form A _ y hz,
        formInner_eq_zero_of_left_eq_zero g.form A _ y hz]

theorem representsExterior_components_eventuallyEq {A : RealForm M k}
    {B : RealForm M (k + 1)} (hAB : RepresentsExterior A B) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formComponents B x =ᶠ[𝓝 z] exteriorComponents (formComponents A x) := by
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
  funext I
  exact hAB x w hw I

theorem representsCodifferential_components_eventuallyEq (g : HermitianField M)
    {A : RealForm M (k + 1)} {B : RealForm M k} (hAB : RepresentsCodifferential g A B)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formComponents B x =ᶠ[𝓝 z] codifferentialComponents g x (formComponents A x) := by
  filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
  funext I
  exact hAB x w hw I

/-- The actual Hodge expression on dependent forms, with exactly the frozen
degree-zero convention and the genuine constructed exterior/codifferential. -/
def hodgeRealForm (g : HermitianField M) : (j : ℕ) → RealForm M j → RealForm M j
  | 0, A => codifferentialRealForm g (exteriorRealForm A)
  | j + 1, A => exteriorRealForm (codifferentialRealForm g A) +
      codifferentialRealForm g (exteriorRealForm A)

/-- The constructed Hodge expression represents the exact frozen calculator
on the entire target of every chart, in every degree. -/
theorem hodgeRealForm_represents (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    RepresentsHodge g.form A (hodgeRealForm g.form k A) := by
  cases k with
  | zero =>
      have hAd := exteriorRealForm_represents A hA
      have hδd := codifferentialRealForm_represents g μ hμ (exteriorRealForm A)
        (exteriorRealForm_smooth A hA)
      intro x z hz I
      change formComponents (codifferentialRealForm g.form (exteriorRealForm A)) x z I =
        codifferentialComponents g.form x (exteriorComponents (formComponents A x)) z I
      rw [hδd x z hz I]
      exact congrFun (codifferentialComponents_congr_nhds g.form x
        (representsExterior_components_eventuallyEq hAd x hz)) I
  | succ j =>
      have hδA := codifferentialRealForm_represents g μ hμ A hA
      have hdA := exteriorRealForm_represents A hA
      have hdδ := exteriorRealForm_represents (codifferentialRealForm g.form A)
        (codifferentialRealForm_smooth g μ hμ A hA)
      have hδd := codifferentialRealForm_represents g μ hμ (exteriorRealForm A)
        (exteriorRealForm_smooth A hA)
      intro x z hz I
      change formComponents (exteriorRealForm (codifferentialRealForm g.form A) +
        codifferentialRealForm g.form (exteriorRealForm A)) x z I =
        exteriorComponents (codifferentialComponents g.form x (formComponents A x)) z I +
          codifferentialComponents g.form x (exteriorComponents (formComponents A x)) z I
      simp only [formComponents_add, Pi.add_apply]
      rw [hdδ x z hz I, hδd x z hz I]
      rw [congrFun (exteriorComponents_congr_nhds
        (representsCodifferential_components_eventuallyEq g.form hδA x hz)) I,
        congrFun (codifferentialComponents_congr_nhds g.form x
          (representsExterior_components_eventuallyEq hdA x hz)) I]

theorem hodgeRealForm_smooth (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) : SmoothRealForm (hodgeRealForm g.form k A) :=
  representsHodge_smooth g hA (hodgeRealForm_represents g μ hμ A hA)

theorem hodgeRealForm_support_subset (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) :
    closure {y | hodgeRealForm g.form k A y ≠ 0} ⊆ closure {y | A y ≠ 0} :=
  representsHodge_support_subset g.form (hodgeRealForm_represents g μ hμ A hA)

theorem hodgeRealForm_compactlySupported (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    CompactlySupportedRealForm (hodgeRealForm g.form k A) :=
  representsHodge_compactlySupported g.form (hodgeRealForm_represents g μ hμ A hA) hcA

theorem hodgeRealForm_l2 (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    L2RealForm g.form μ (hodgeRealForm g.form k A) :=
  smooth_compactlySupported_l2RealForm g μ hμ _ (hodgeRealForm_smooth g μ hμ A hA)
    (hodgeRealForm_compactlySupported g μ hμ A hA hcA)

/-- Every genuine compact smooth form now supplies an actual frozen Hodge
core pair, with the computed expression as its output. -/
theorem hodgeRealForm_corePair (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    OperatorCandidates.HodgeCorePair g.form μ A (hodgeRealForm g.form k A) :=
  (hodgeCorePair_iff_input g μ hμ A _).mpr ⟨hA, hcA, hodgeRealForm_represents g μ hμ A hA⟩

theorem realForm_eq_of_center_components (A B : RealForm M k)
    (h : ∀ x I, formComponents A x (chartPt x x) I = formComponents B x (chartPt x x) I) :
    A = B := by
  funext x
  have hz : (A - B) x = 0 := by
    apply (formComponents_center_eq_zero_iff (A - B) x).mp
    funext I
    change formComponents A x (chartPt x x) I - formComponents B x (chartPt x x) I = 0
    rw [h x I, sub_self]
  exact sub_eq_zero.mp hz

theorem representsCodifferential_unique (g : HermitianField M) {A : RealForm M (k + 1)}
    {B C : RealForm M k} (hB : RepresentsCodifferential g A B) (hC : RepresentsCodifferential g A C) :
    B = C := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  exact (hB x (chartPt x x) ht I).trans (hC x (chartPt x x) ht I).symm

theorem representsHodge_unique (g : HermitianField M) {A B C : RealForm M k}
    (hB : RepresentsHodge g A B) (hC : RepresentsHodge g A C) : B = C := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  exact (hB x (chartPt x x) ht I).trans (hC x (chartPt x x) ht I).symm

theorem hodgeCorePair_iff_computed (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k) :
    OperatorCandidates.HodgeCorePair g.form μ A W ↔
      SmoothRealForm A ∧ CompactlySupportedRealForm A ∧ W = hodgeRealForm g.form k A := by
  rw [hodgeCorePair_iff_input g μ hμ A W]
  constructor
  · rintro ⟨hA, hcA, hAW⟩
    exact ⟨hA, hcA, representsHodge_unique g.form hAW (hodgeRealForm_represents g μ hμ A hA)⟩
  · rintro ⟨hA, hcA, rfl⟩
    exact ⟨hA, hcA, hodgeRealForm_represents g μ hμ A hA⟩

theorem gradedL2_of_smooth_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (hcA : ∀ j, CompactlySupportedRealForm (A j)) :
    OperatorCandidates.GradedL2 g.form μ A := by
  refine ⟨?_, fun j => smooth_compactlySupported_l2RealForm g μ hμ (A j) (hA j) (hcA j)⟩
  intro j hj
  exact realForm_eq_zero_of_degree_gt (A j) hj

/-- The actual full exterior-algebra Dirac expression d+δ. -/
def diracRealForm (g : HermitianField M) (A : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.GradedRealForm M
  | 0 => codifferentialRealForm g (A 1)
  | j + 1 => exteriorRealForm (A j) + codifferentialRealForm g (A (j + 2))

theorem diracRealForm_smooth (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) : ∀ j, SmoothRealForm (diracRealForm g.form A j) := by
  intro j
  cases j with
  | zero => exact codifferentialRealForm_smooth g μ hμ (A 1) (hA 1)
  | succ j =>
      exact smoothRealForm_add _ _ (exteriorRealForm_smooth (A j) (hA j))
        (codifferentialRealForm_smooth g μ hμ (A (j + 2)) (hA (j + 2)))

theorem diracRealForm_compactlySupported (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (hcA : ∀ j, CompactlySupportedRealForm (A j)) :
    ∀ j, CompactlySupportedRealForm (diracRealForm g.form A j) := by
  intro j
  cases j with
  | zero => exact codifferentialRealForm_compactlySupported g μ hμ (A 1) (hA 1) (hcA 1)
  | succ j =>
      exact compactlySupportedRealForm_add _ _ (exteriorRealForm_compactlySupported (A j) (hA j) (hcA j))
        (codifferentialRealForm_compactlySupported g μ hμ (A (j + 2)) (hA (j + 2)) (hcA (j + 2)))

theorem diracRealForm_represents (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) :
    ∀ x z, z ∈ chartTarget x → ∀ j I,
      formComponents (diracRealForm g.form A j) x z I = OperatorCandidates.diracComponents g.form x A j z I := by
  intro x z hz j I
  cases j with
  | zero => exact codifferentialRealForm_represents g μ hμ (A 1) (hA 1) x z hz I
  | succ j =>
      change formComponents (exteriorRealForm (A j) + codifferentialRealForm g.form (A (j + 2))) x z I =
        exteriorComponents (formComponents (A j) x) z I +
          codifferentialComponents g.form x (formComponents (A (j + 2)) x) z I
      simp only [formComponents_add, Pi.add_apply]
      rw [exteriorRealForm_represents (A j) (hA j) x z hz I,
        codifferentialRealForm_represents g μ hμ (A (j + 2)) (hA (j + 2)) x z hz I]

/-- Every actual smooth compact graded form supplies the complete frozen
Dirac core pair, including all degree bounds and both graded L² conditions. -/
theorem diracRealForm_corePair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (hcA : ∀ j, CompactlySupportedRealForm (A j)) :
    OperatorCandidates.DiracCorePair g.form μ A (diracRealForm g.form A) :=
  ⟨gradedL2_of_smooth_compact g μ hμ A hA hcA,
    gradedL2_of_smooth_compact g μ hμ (diracRealForm g.form A)
      (diracRealForm_smooth g μ hμ A hA) (diracRealForm_compactlySupported g μ hμ A hA hcA),
    (fun j => ⟨hA j, hcA j, diracRealForm_smooth g μ hμ A hA j⟩),
    diracRealForm_represents g μ hμ A hA⟩

/-- Smoothness defines an actual linear subspace of the raw dependent forms. -/
def smoothFormSubmodule (j : ℕ) : Submodule ℝ (RealForm M j) where
  carrier := {A | SmoothRealForm A}
  zero_mem' := smoothRealForm_zero
  add_mem' hA hB := smoothRealForm_add _ _ hA hB
  smul_mem' c _ hA := smoothRealForm_smul c _ hA

theorem exteriorRealForm_add (A B : RealForm M k) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    exteriorRealForm (A + B) = exteriorRealForm A + exteriorRealForm B := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  rw [exteriorRealForm_represents (A + B) (smoothRealForm_add A B hA hB) x (chartPt x x) ht I]
  simp only [formComponents_add, Pi.add_apply]
  rw [exteriorRealForm_represents A hA x (chartPt x x) ht I,
    exteriorRealForm_represents B hB x (chartPt x x) ht I]
  exact exteriorComponents_add_at (formComponents A x) (formComponents B x) (chartPt x x)
    (smoothRealForm_coefficient_differentiableAt A hA x ht)
    (smoothRealForm_coefficient_differentiableAt B hB x ht) I

theorem exteriorRealForm_smul (c : ℝ) (A : RealForm M k) (hA : SmoothRealForm A) :
    exteriorRealForm (c • A) = c • exteriorRealForm A := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  rw [exteriorRealForm_represents (c • A) (smoothRealForm_smul c A hA) x (chartPt x x) ht I]
  simp only [formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [exteriorRealForm_represents A hA x (chartPt x x) ht I]
  exact exteriorComponents_smul_at c (formComponents A x) (chartPt x x)
    (smoothRealForm_coefficient_differentiableAt A hA x ht) I

def exteriorSmoothLinear (j : ℕ) :
    smoothFormSubmodule (M := M) j →ₗ[ℝ] RealForm M (j + 1) where
  toFun A := exteriorRealForm A.val
  map_add' A B := exteriorRealForm_add A.val B.val A.property B.property
  map_smul' c A := exteriorRealForm_smul c A.val A.property

theorem smoothRealForm_fintypeSum {ι : Type*} [Fintype ι] (A : ι → RealForm M k)
    (hA : ∀ i, SmoothRealForm (A i)) : SmoothRealForm (∑ i, A i) :=
  (smoothFormSubmodule (M := M) k).sum_mem (fun i _ => hA i)

theorem exteriorRealForm_fintypeSum {ι : Type*} [Fintype ι] (A : ι → RealForm M k)
    (hA : ∀ i, SmoothRealForm (A i)) : exteriorRealForm (∑ i, A i) = ∑ i, exteriorRealForm (A i) := by
  let U : ι → smoothFormSubmodule (M := M) k := fun i => ⟨A i, hA i⟩
  have h := map_sum (exteriorSmoothLinear (M := M) k) U Finset.univ
  change exteriorRealForm ((∑ i, U i).val : RealForm M k) =
    ∑ i, exteriorRealForm ((U i).val : RealForm M k) at h
  simpa only [Submodule.coe_sum, U] using h

theorem multiplyRealForm_support_subset_scalar (η : M.Carrier → ℝ) (A : RealForm M k) :
    closure {y | multiplyRealForm η A y ≠ 0} ⊆ tsupport η := by
  apply closure_mono
  intro y hy
  change η y ≠ 0
  intro hzero
  exact hy (by simp only [multiplyRealForm, hzero, zero_smul])

def formInnerLinearLeft (g : HermitianField M) (B : RealForm M k) :
    RealForm M k →ₗ[ℝ] (M.Carrier → ℝ) where
  toFun A := formInner g A B
  map_add' A C := formInner_add_left g A C B
  map_smul' c A := formInner_smul_left g c A B

theorem formInner_fintypeSum_left {ι : Type*} [Fintype ι] (g : HermitianField M)
    (A : ι → RealForm M k) (B : RealForm M k) (y : M.Carrier) :
    formInner g (∑ i, A i) B y = ∑ i, formInner g (A i) B y := by
  have h := congrFun (map_sum (formInnerLinearLeft g B) A Finset.univ) y
  have h' : formInner g (∑ i, A i) B y = (∑ i, formInner g (A i) B) y := by
    with_unfolding_all
      exact h
  simpa only [Finset.sum_apply] using h'

/-- Smooth sections that agree almost everywhere for the actual volume
measure agree as genuine dependent forms. Full support is proved by the
accepted chart-volume construction. -/
theorem smoothRealForm_eq_of_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hAB : ∀ᵐ y ∂μ, A y = B y) : A = B := by
  letI : μ.IsOpenPosMeasure := L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  have hD : SmoothRealForm (A - B) := (smoothFormSubmodule (M := M) k).sub_mem hA hB
  have hn : formNormSq g.form (A - B) =ᵐ[μ] 0 := by
    filter_upwards [hAB] with y hy
    exact (formNormSq_eq_zero_iff g.form (A - B) y).mpr (sub_eq_zero.mpr hy)
  have heq : formNormSq g.form (A - B) = 0 :=
    Measure.eq_of_ae_eq hn (formNormSq_continuous g (A - B) hD) continuous_const
  funext y
  exact sub_eq_zero.mp ((formNormSq_eq_zero_iff g.form (A - B) y).mp (congrFun heq y))

/-- Global form Green for the original Riemannian volume and the actual
constructed d and δ. The compact input is decomposed by the accepted finite
smooth chart partition; every local form, integral and sum is internal. -/
theorem integral_exterior_codifferential (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (H : RealForm M (k + 1))
    (hA : SmoothRealForm A) (hH : SmoothRealForm H) (hcA : CompactlySupportedRealForm A) :
    (∫ y, formInner g.form (exteriorRealForm A) H y ∂μ) =
      ∫ y, formInner g.form A (codifferentialRealForm g.form H) y ∂μ := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ := L18Aux.exists_finite_smooth_partition hcA
  let As : s → RealForm M k := fun i => multiplyRealForm (p i) A
  have hAs (i : s) : SmoothRealForm (As i) := smoothRealForm_multiply (p i) A (hp i) hA
  have hcAs (i : s) : CompactlySupportedRealForm (As i) :=
    compactlySupportedRealForm_multiply (p i) A hcA
  have hAss (i : s) : closure {y | As i y ≠ 0} ⊆
      (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
    (multiplyRealForm_support_subset_scalar (p i) A).trans (hps i)
  have hsumA : (∑ i, As i) = A := by
    funext y
    simp only [Finset.sum_apply, As, multiplyRealForm]
    rw [← Finset.sum_smul]
    by_cases hy : A y = 0
    · simp only [hy, smul_zero]
    · rw [hsum y (subset_closure hy), one_smul]
  have hsumd : exteriorRealForm A = ∑ i, exteriorRealForm (As i) := by
    exact (congrArg exteriorRealForm hsumA).symm.trans (exteriorRealForm_fintypeSum As hAs)
  have hdAs (i : s) : Integrable (formInner g.form (exteriorRealForm (As i)) H) μ :=
    smooth_compact_formInner_integrable g μ hμ _ H (exteriorRealForm_smooth (As i) (hAs i)) hH
      (exteriorRealForm_compactlySupported (As i) (hAs i) (hcAs i))
  have hδH : SmoothRealForm (codifferentialRealForm g.form H) :=
    codifferentialRealForm_smooth g μ hμ H hH
  have hiAs (i : s) : Integrable (formInner g.form (As i) (codifferentialRealForm g.form H)) μ :=
    smooth_compact_formInner_integrable g μ hμ _ _ (hAs i) hδH (hcAs i)
  have hpieces (i : s) : Integrable (fun y => p i y •
      formInner g.form A (codifferentialRealForm g.form H) y) μ := by
    convert hiAs i using 1
    funext y
    simp only [As, formInner_multiplyRealForm_left, smul_eq_mul]
  have hsumI : ∀ y ∈ Function.support (formInner g.form A (codifferentialRealForm g.form H)),
      ∑ i, p i y = 1 := by
    intro y hy
    have hn : A y ≠ 0 := fun hzero =>
      hy (formInner_eq_zero_of_left_eq_zero g.form A _ y hzero)
    exact hsum y (subset_closure hn)
  have hpartition := L18Aux.integral_finite_partition μ p
    (formInner g.form A (codifferentialRealForm g.form H)) hpieces hsumI
  calc
    _ = ∫ y, ∑ i, formInner g.form (exteriorRealForm (As i)) H y ∂μ := by
      rw [hsumd]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => formInner_fintypeSum_left g.form
        (fun i => exteriorRealForm (As i)) H y
    _ = ∑ i, ∫ y, formInner g.form (exteriorRealForm (As i)) H y ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => hdAs i)
    _ = ∑ i, ∫ y, formInner g.form (As i) (codifferentialRealForm g.form H) y ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_exterior_codifferential_chartSupport g μ hμ (As i) H (hAs i) hH (hcAs i)
        (i : M.Carrier) (hAss i)
    _ = ∑ i, ∫ y, p i y • formInner g.form A (codifferentialRealForm g.form H) y ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [As, formInner_multiplyRealForm_left, smul_eq_mul]
    _ = _ := hpartition.2.symm


theorem integral_hodgeRealForm_zero_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 0)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form (hodgeRealForm g.form 0 A) B y ∂μ) =
      ∫ y, formInner g.form (exteriorRealForm A) (exteriorRealForm B) y ∂μ := by
  change (∫ y, formInner g.form (codifferentialRealForm g.form (exteriorRealForm A)) B y ∂μ) = _
  rw [formInner_symm g.form (codifferentialRealForm g.form (exteriorRealForm A)) B,
    ← integral_exterior_codifferential g μ hμ B (exteriorRealForm A) hB (exteriorRealForm_smooth A hA) hcB,
    formInner_symm g.form (exteriorRealForm B) (exteriorRealForm A)]

theorem integral_hodgeRealForm_succ_energy (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M (k + 1))
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form (hodgeRealForm g.form (k + 1) A) B y ∂μ) =
      (∫ y, formInner g.form (codifferentialRealForm g.form A) (codifferentialRealForm g.form B) y ∂μ) +
        ∫ y, formInner g.form (exteriorRealForm A) (exteriorRealForm B) y ∂μ := by
  let U := codifferentialRealForm g.form A
  have hU : SmoothRealForm U := codifferentialRealForm_smooth g μ hμ A hA
  have hcU : CompactlySupportedRealForm U := codifferentialRealForm_compactlySupported g μ hμ A hA hcA
  have hdi : Integrable (formInner g.form (exteriorRealForm U) B) μ :=
    smooth_compact_formInner_integrable g μ hμ _ B (exteriorRealForm_smooth U hU) hB
      (exteriorRealForm_compactlySupported U hU hcU)
  have hδi : Integrable (formInner g.form (codifferentialRealForm g.form (exteriorRealForm A)) B) μ :=
    smooth_compact_formInner_integrable g μ hμ _ B
      (codifferentialRealForm_smooth g μ hμ (exteriorRealForm A) (exteriorRealForm_smooth A hA)) hB
      (codifferentialRealForm_compactlySupported g μ hμ (exteriorRealForm A)
        (exteriorRealForm_smooth A hA) (exteriorRealForm_compactlySupported A hA hcA))
  have hd := integral_exterior_codifferential g μ hμ U B hU hB hcU
  have hδ : (∫ y, formInner g.form (codifferentialRealForm g.form (exteriorRealForm A)) B y ∂μ) =
      ∫ y, formInner g.form (exteriorRealForm A) (exteriorRealForm B) y ∂μ := by
    rw [formInner_symm g.form (codifferentialRealForm g.form (exteriorRealForm A)) B,
      ← integral_exterior_codifferential g μ hμ B (exteriorRealForm A) hB (exteriorRealForm_smooth A hA) hcB,
      formInner_symm g.form (exteriorRealForm B) (exteriorRealForm A)]
  change (∫ y, formInner g.form (exteriorRealForm U + codifferentialRealForm g.form (exteriorRealForm A)) B y ∂μ) = _
  rw [formInner_add_left]
  simp only [Pi.add_apply]
  rw [integral_add hdi hδi, hd, hδ]

theorem hodgeRealForm_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B)
    (hcA : CompactlySupportedRealForm A) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form (hodgeRealForm g.form k A) B y ∂μ) =
      ∫ y, formInner g.form (hodgeRealForm g.form k B) A y ∂μ := by
  cases k with
  | zero =>
      rw [integral_hodgeRealForm_zero_energy g μ hμ A B hA hB hcB,
        integral_hodgeRealForm_zero_energy g μ hμ B A hB hA hcA,
        formInner_symm g.form (exteriorRealForm A) (exteriorRealForm B)]
  | succ j =>
      rw [integral_hodgeRealForm_succ_energy g μ hμ A B hA hB hcA hcB,
        integral_hodgeRealForm_succ_energy g μ hμ B A hB hA hcB hcA,
        formInner_symm g.form (codifferentialRealForm g.form A) (codifferentialRealForm g.form B),
        formInner_symm g.form (exteriorRealForm A) (exteriorRealForm B)]

theorem hodgeRealForm_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    0 ≤ ∫ y, formInner g.form (hodgeRealForm g.form k A) A y ∂μ := by
  cases k with
  | zero =>
      rw [integral_hodgeRealForm_zero_energy g μ hμ A A hA hA hcA]
      exact integral_nonneg (fun y => formNormSq_nonneg g.form (exteriorRealForm A) y)
  | succ j =>
      rw [integral_hodgeRealForm_succ_energy g μ hμ A A hA hA hcA hcA]
      exact add_nonneg (integral_nonneg (fun y => formNormSq_nonneg g.form (codifferentialRealForm g.form A) y))
        (integral_nonneg (fun y => formNormSq_nonneg g.form (exteriorRealForm A) y))

theorem hodgeCorePair_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W B Z : RealForm M k}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W)
    (hBZ : OperatorCandidates.HodgeCorePair g.form μ B Z) :
    (∫ y, formInner g.form W B y ∂μ) = ∫ y, formInner g.form A Z y ∂μ := by
  obtain ⟨hA, hcA, hW⟩ := (hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  obtain ⟨hB, hcB, hZ⟩ := (hodgeCorePair_iff_computed g μ hμ B Z).mp hBZ
  rw [hW, hZ, formInner_symm g.form A (hodgeRealForm g.form k B)]
  exact hodgeRealForm_symmetric g μ hμ A B hA hB hcA hcB

theorem hodgeCorePair_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W : RealForm M k}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W) :
    0 ≤ ∫ y, formInner g.form A W y ∂μ := by
  obtain ⟨hA, hcA, hW⟩ := (hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  rw [hW, formInner_symm g.form A (hodgeRealForm g.form k A)]
  exact hodgeRealForm_nonnegative g μ hμ A hA hcA


/-- The entire original minimal Hodge graph lies in the original weak maximal
graph. This follows from actual core symmetry and the already proved Hilbert
graph closure identification; completeness is not needed for this direction. -/
theorem hodgeMinimalGraph_implies_maximal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W : RealForm M k}
    (hAW : OperatorCandidates.HodgeMinimalGraph g.form μ A W) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W := by
  have hcl := (hodgeMinimalGraph_iff_core_closure g μ A W hAW.1 hAW.2.1).mp hAW
  apply (hodgeMaximalGraph_iff_core_pairing g μ A W hAW.1 hAW.2.1).mpr
  intro p hp
  have hc : IsClosed {q : L2FormHilbert g μ k × L2FormHilbert g μ k |
      inner ℝ q.1 p.2 = inner ℝ q.2 p.1} :=
    isClosed_eq (continuous_fst.inner continuous_const) (continuous_snd.inner continuous_const)
  have hs : hodgeCoreRealizedGraph g μ k ⊆
      {q | inner ℝ q.1 p.2 = inner ℝ q.2 p.1} := by
    intro q hq
    obtain ⟨U, V, hUV, rfl⟩ := hq
    obtain ⟨B, Z, hBZ, rfl⟩ := hp
    simpa only [Set.mem_setOf_eq, Prod.fst, Prod.snd, realizeL2Form_inner, L2FormSpace.toSection_ofSection] using
      (hodgeCorePair_symmetric g μ hμ hUV hBZ).symm
  exact (closure_minimal hs hc) hcl

theorem hodgeMinimalGraph_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W : RealForm M k}
    (hAW : OperatorCandidates.HodgeMinimalGraph g.form μ A W) :
    0 ≤ ∫ y, formInner g.form A W y ∂μ := by
  have hcl := (hodgeMinimalGraph_iff_core_closure g μ A W hAW.1 hAW.2.1).mp hAW
  have hc : IsClosed {q : L2FormHilbert g μ k × L2FormHilbert g μ k | 0 ≤ inner ℝ q.1 q.2} :=
    isClosed_le continuous_const (continuous_fst.inner continuous_snd)
  have hs : hodgeCoreRealizedGraph g μ k ⊆ {q | 0 ≤ inner ℝ q.1 q.2} := by
    rintro q ⟨U, V, hUV, rfl⟩
    simpa only [Set.mem_setOf_eq, Prod.fst, Prod.snd, realizeL2Form_inner, L2FormSpace.toSection_ofSection] using
      hodgeCorePair_nonnegative g μ hμ hUV
  have hpos := (closure_minimal hs hc) hcl
  simpa only [Set.mem_setOf_eq, Prod.fst, Prod.snd, realizeL2Form_inner, L2FormSpace.toSection_ofSection] using hpos


/-- Finite coordinate evaluation is bounded by the dual diagonal and the
actual positive matrix quadratic form. -/
theorem matrix_coordinate_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : T.PosDef) (v : ι → ℝ) (i : ι) :
    (v i) ^ 2 ≤ T⁻¹ i i * dotProduct (star v) (T.mulVec v) := by
  let e : ι → ℝ := Pi.single i 1
  let w := T⁻¹.mulVec e
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp hT.isUnit
  have hw : T.mulVec w = e := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hdet, Matrix.one_mulVec]
  have hwi : w i = T⁻¹ i i := by
    simp only [w, e, Matrix.mulVec_single_one, Matrix.col_apply]
  have h := hT.star_dotProduct_mulVec_mul_le v w
  simp only [star_trivial, hw, e, dotProduct_single_one] at h
  simpa only [star_trivial, pow_two, hwi, mul_comm] using h

theorem tensorCoefficientPairing_fin_eq_matrix {α : Type*} [Fintype α]
    (B : Matrix α α ℝ) (F H : (Fin k → α) → ℝ) :
    tensorCoefficientPairing B F H = dotProduct F ((tensorMatrix B k).mulVec H) := by
  classical
  simp only [tensorCoefficientPairing, dotProduct, Matrix.mulVec, Finset.mul_sum, tensorMatrix]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  ring

/-- Every actual chart coefficient is controlled by the true metric form
norm, with the explicit covariant-metric dual factor and the exact k! convention. -/
theorem formComponents_sq_le_metric (g : HermitianField M) (A : RealForm M k)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin k → RIdx n) :
    (formComponents A x z I) ^ 2 ≤ (Nat.factorial k : ℝ) *
      (∏ r, realMetricFn g x z (I r) (I r)) * formNormSq g A (chartInv x z) := by
  let G := realMetricFn g x z
  let T := tensorMatrix G⁻¹ k
  let v := formComponents A x z
  have hG : G.PosDef := realMetricFn_posDef_of_mem_target g x hz
  have hT : T.PosDef := matrixPiProd_posDef G⁻¹ hG.inv k
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hTi : T⁻¹ = tensorMatrix G k := by
    apply Matrix.inv_eq_left_inv
    change tensorMatrix G k * tensorMatrix G⁻¹ k = 1
    rw [← tensorMatrix_mul, Matrix.mul_nonsing_inv G hGdet, tensorMatrix_one]
  have hn : formNormSq g A (chartInv x z) = (Nat.factorial k : ℝ)⁻¹ * dotProduct v (T.mulVec v) := by
    simpa only [formNormSq, tensorCoefficientPairing_fin_eq_matrix] using
      formInner_chartInv_eq_tensorPairing g A A x hz
  have hf : (Nat.factorial k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hq : dotProduct (star v) (T.mulVec v) =
      (Nat.factorial k : ℝ) * formNormSq g A (chartInv x z) := by
    rw [star_trivial, hn, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]
  have hb := matrix_coordinate_sq_le T hT v I
  rw [hTi, hq] at hb
  calc
    _ ≤ tensorMatrix G k I I * ((Nat.factorial k : ℝ) * formNormSq g A (chartInv x z)) := hb
    _ = _ := by dsimp only [tensorMatrix, G]; ring

/-- Uniform local L² coefficient control on a genuine compact subset of a
chart target. The constant is independent of the raw form being estimated. -/
theorem formComponents_sq_le_on_compact (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKt : K ⊆ chartTarget x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) z, z ∈ K → ∀ (I : Fin k → RIdx n),
      (formComponents A x z I) ^ 2 ≤ C * formNormSq g.form A (chartInv x z) := by
  classical
  have hb (I : Fin k → RIdx n) : ∃ c : ℝ, ∀ z ∈ K,
      (Nat.factorial k : ℝ) * (∏ r, realMetricFn g.form x z (I r) (I r)) ≤ c := by
    have hf : ContinuousOn (fun z => (Nat.factorial k : ℝ) *
        (∏ r, realMetricFn g.form x z (I r) (I r))) K :=
      continuousOn_const.mul (continuousOn_finsetProd Finset.univ (fun r _ =>
        (L18Aux.metricSmooth_of_smoothMetric g x (I r) (I r)).continuousOn.mono hKt))
    obtain ⟨c, hc⟩ := hcK.bddAbove_image hf
    exact ⟨c, fun z hz => hc ⟨z, hz, rfl⟩⟩
  choose c hc using hb
  let C := 1 + ∑ I, max (c I) 0
  have hs : 0 ≤ ∑ I, max (c I) 0 := Finset.sum_nonneg (fun I _ => le_max_right (c I) 0)
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro A z hz I
  have hI : c I ≤ C := by
    have hi : max (c I) 0 ≤ ∑ J, max (c J) 0 :=
      Finset.single_le_sum (fun J _ => le_max_right (c J) 0) (Finset.mem_univ I)
    dsimp only [C]
    linarith [le_max_left (c I) 0]
  exact (formComponents_sq_le_metric g.form A x (hKt hz) I).trans
    (mul_le_mul_of_nonneg_right ((hc I z hz).trans hI) (formNormSq_nonneg g.form A _))


theorem matrix_quadratic_le_sum_abs_mul_sum_sq {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (v : ι → ℝ) :
    dotProduct v (T.mulVec v) ≤ (∑ i, ∑ j, |T i j|) * ∑ i, (v i) ^ 2 := by
  classical
  let S := ∑ i, (v i) ^ 2
  have hv (i : ι) : (v i) ^ 2 ≤ S :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hab (i j : ι) : |v i * v j| ≤ S := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j), hv i, hv j]
  have ht (i j : ι) : v i * (T i j * v j) ≤ |T i j| * S := by
    calc
      _ ≤ |v i * (T i j * v j)| := le_abs_self _
      _ = |T i j| * |v i * v j| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hab i j) (abs_nonneg _)
  calc
    _ = ∑ i, ∑ j, v i * (T i j * v j) := by simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |T i j| * S := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = _ := by simp only [Finset.sum_mul, S]

theorem formNormSq_le_chart_coefficients (g : HermitianField M) (A : RealForm M k)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    formNormSq g A (chartInv x z) ≤ (Nat.factorial k : ℝ)⁻¹ *
      (∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
        |∏ r, (realMetricFn g x z)⁻¹ (I r) (J r)|) * ∑ I, (formComponents A x z I) ^ 2 := by
  have hn : formNormSq g A (chartInv x z) = (Nat.factorial k : ℝ)⁻¹ *
      dotProduct (formComponents A x z) ((tensorMatrix (realMetricFn g x z)⁻¹ k).mulVec (formComponents A x z)) := by
    simpa only [formNormSq, tensorCoefficientPairing_fin_eq_matrix] using
      formInner_chartInv_eq_tensorPairing g A A x hz
  rw [hn]
  have hh := mul_le_mul_of_nonneg_left
    (matrix_quadratic_le_sum_abs_mul_sum_sq (tensorMatrix (realMetricFn g x z)⁻¹ k) (formComponents A x z))
    (inv_nonneg.mpr (Nat.cast_nonneg (Nat.factorial k) : (0 : ℝ) ≤ _))
  calc
    _ ≤ (Nat.factorial k : ℝ)⁻¹ *
        ((∑ I, ∑ J, |tensorMatrix (realMetricFn g x z)⁻¹ k I J|) * ∑ I, (formComponents A x z I) ^ 2) := hh
    _ = _ := by dsimp only [tensorMatrix]; ring

/-- On every compact chart region the exact volume-weighted metric norm
and the finite actual coefficient squares control each other, uniformly over
all raw forms. No global coordinate bound is assumed. -/
theorem formNormSq_chart_weighted_comparison (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKt : K ⊆ chartTarget x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : RealForm M k) z, z ∈ K →
      (∀ I, (formComponents A x z I) ^ 2 ≤ C *
        (Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z))) ∧
      Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z) ≤
        C * ∑ I, (formComponents A x z I) ^ 2 := by
  classical
  let ρ := fun z => Real.sqrt (realMetricFn g.form x z).det
  have hρc : ContinuousOn ρ K := (L18Aux.volumeDensity_contDiffOn g x).continuousOn.mono hKt
  have hρpos {z : ComplexVector n} (hz : z ∈ K) : 0 < ρ z :=
    Real.sqrt_pos.mpr (realMetricFn_posDef_of_mem_target g.form x (hKt hz)).det_pos
  have hb (I : Fin k → RIdx n) : ∃ c : ℝ, ∀ z ∈ K,
      ((Nat.factorial k : ℝ) * ∏ r, realMetricFn g.form x z (I r) (I r)) / ρ z ≤ c := by
    have hf : ContinuousOn (fun z => ((Nat.factorial k : ℝ) *
        ∏ r, realMetricFn g.form x z (I r) (I r)) / ρ z) K :=
      (continuousOn_const.mul (continuousOn_finsetProd Finset.univ (fun r _ =>
        (L18Aux.metricSmooth_of_smoothMetric g x (I r) (I r)).continuousOn.mono hKt))).div hρc
          (fun z hz => ne_of_gt (hρpos hz))
    obtain ⟨c, hc⟩ := hcK.bddAbove_image hf
    exact ⟨c, fun z hz => hc ⟨z, hz, rfl⟩⟩
  choose c hc using hb
  let L := 1 + ∑ I, max (c I) 0
  have hLpos : 0 < L := by
    have hs : 0 ≤ ∑ I, max (c I) 0 := Finset.sum_nonneg (fun I _ => le_max_right (c I) 0)
    dsimp only [L]
    linarith
  have hIL (I : Fin k → RIdx n) : c I ≤ L := by
    have hi : max (c I) 0 ≤ ∑ J, max (c J) 0 :=
      Finset.single_le_sum (fun J _ => le_max_right (c J) 0) (Finset.mem_univ I)
    dsimp only [L]
    linarith [le_max_left (c I) 0]
  let U := fun z => ρ z * (Nat.factorial k : ℝ)⁻¹ *
    (∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
      |∏ r, (realMetricFn g.form x z)⁻¹ (I r) (J r)|)
  have hUc : ContinuousOn U K :=
    (hρc.mul continuousOn_const).mul
      (continuousOn_finsetSum Finset.univ (fun I _ => continuousOn_finsetSum Finset.univ (fun J _ =>
        (continuousOn_finsetProd Finset.univ (fun r _ =>
          (L18Aux.realMetricFn_inverse_contDiffOn g x (I r) (J r)).continuousOn.mono hKt)).abs)))
  obtain ⟨u, hu⟩ := hcK.bddAbove_image hUc
  let C := max L (1 + max u 0)
  have hLC : L ≤ C := le_max_left _ _
  have huC : u ≤ C := by
    dsimp only [C]
    linarith [le_max_left u 0, le_max_right L (1 + max u 0)]
  refine ⟨C, lt_of_lt_of_le hLpos hLC, ?_⟩
  intro A z hz
  constructor
  · intro I
    have hfC : ((Nat.factorial k : ℝ) * ∏ r, realMetricFn g.form x z (I r) (I r)) / ρ z ≤ C :=
      ((hc I z hz).trans (hIL I)).trans hLC
    have hW : 0 ≤ ρ z * formNormSq g.form A (chartInv x z) :=
      mul_nonneg (le_of_lt (hρpos hz)) (formNormSq_nonneg g.form A _)
    calc
      _ ≤ (Nat.factorial k : ℝ) * (∏ r, realMetricFn g.form x z (I r) (I r)) *
          formNormSq g.form A (chartInv x z) := formComponents_sq_le_metric g.form A x (hKt hz) I
      _ = (((Nat.factorial k : ℝ) * ∏ r, realMetricFn g.form x z (I r) (I r)) / ρ z) *
          (ρ z * formNormSq g.form A (chartInv x z)) := by
        field_simp [ne_of_gt (hρpos hz)] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfC hW
  · calc
      _ ≤ ρ z * ((Nat.factorial k : ℝ)⁻¹ *
          (∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
            |∏ r, (realMetricFn g.form x z)⁻¹ (I r) (J r)|) * ∑ I, (formComponents A x z I) ^ 2) :=
        mul_le_mul_of_nonneg_left (formNormSq_le_chart_coefficients g.form A x (hKt hz))
          (le_of_lt (hρpos hz))
      _ = U z * ∑ I, (formComponents A x z I) ^ 2 := by dsimp only [U]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((hu ⟨z, hz, rfl⟩).trans huC)
        (Finset.sum_nonneg (fun I _ => sq_nonneg (formComponents A x z I)))


/-- A raw model L² field supported compactly inside an open chart region
can be approximated by genuine C∞ compact fields supported inside that same
region. The smooth cutoff and the Lp approximation are constructed internally. -/
theorem smooth_compact_L2_approx_in_open {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    {f : E → F} (hf : MemLp f 2 ν) (hcf : HasCompactSupport f)
    {O : Set E} (hO : IsOpen O) (hfO : tsupport f ⊆ O) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ O ∧ tsupport f ⊆ K ∧
      ∀ ε : ℝ, 0 < ε → ∃ P : E → F, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ K ∧
        eLpNorm (f - P) 2 ν ≤ ENNReal.ofReal ε := by
  obtain ⟨V, hV, hfV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure hcf hO hfO
  obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV (isClosed_tsupport f) hfV
  have hcχ : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    simpa only [tsupport, hχsupport] using hcV
  have hχO : tsupport χ ⊆ O := by simpa only [tsupport, hχsupport] using hVO
  have hfχ : tsupport f ⊆ tsupport χ := by
    intro z hz
    apply subset_tsupport χ
    change χ z ≠ 0
    rw [(hχone z).mp hz]
    exact one_ne_zero
  have hχf (z : E) : χ z • f z = f z := by
    by_cases hz : f z = 0
    · simp only [hz, smul_zero]
    · rw [(hχone z).mp (subset_closure hz), one_smul]
  refine ⟨tsupport χ, hcχ, hχO, hfχ, ?_⟩
  intro ε hε
  obtain ⟨g, _, hg, hfg⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
  let P := fun z => χ z • g z
  have hP : ContDiff ℝ ∞ P := hχ.smul hg
  have hsP : tsupport P ⊆ tsupport χ := tsupport_smul_subset_left χ g
  have hcP : HasCompactSupport P := hcχ.of_isClosed_subset (isClosed_tsupport _) hsP
  have hPm : MemLp P 2 ν := hP.continuous.memLp_of_hasCompactSupport hcP
  have hnorm (z : E) : ‖f z - P z‖ ≤ ‖f z - g z‖ := by
    have he : f z - P z = χ z • (f z - g z) := by
      dsimp only [P]
      rw [smul_sub, hχf z]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχrange ⟨z, rfl⟩).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχrange ⟨z, rfl⟩).2
  refine ⟨P, hP, hcP, hsP, ?_⟩
  exact (eLpNorm_mono_ae ((hf.sub hPm).aestronglyMeasurable)
    (Filter.Eventually.of_forall hnorm)).trans hfg


theorem multiplyRealForm_sub_normSq (g : HermitianField M) (η : M.Carrier → ℝ)
    (A : RealForm M k) (x : M.Carrier) :
    formNormSq g (multiplyRealForm η A - A) x = (η x - 1) ^ 2 * formNormSq g A x := by
  have hv : (multiplyRealForm η A - A) x = ((η x - 1) • A) x := by
    apply ContinuousAlternatingMap.ext
    intro v
    change η x * A x v - A x v = (η x - 1) * A x v
    ring
  exact (formNormSq_congr_at g hv).trans (formNormSq_smul_eq g (η x - 1) A x)

/-- Bounded smooth multipliers converging pointwise to one converge strongly
on every genuine raw L² form. This is actual dominated convergence for the
frozen extended-real squared L² distance. -/
theorem multiplyRealForm_l2_distance_tendsto (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (η : ℕ → M.Carrier → ℝ)
    (hη : ∀ j, SmoothFn (η j)) (hηrange : ∀ j x, η j x ∈ Set.Icc (0 : ℝ) 1)
    (ht : ∀ x, Tendsto (fun j => η j x) atTop (𝓝 1)) :
    Tendsto (fun j => formL2DistanceSq g.form μ (multiplyRealForm (η j) A) A) atTop (𝓝 0) := by
  have hAj (j : ℕ) : L2RealForm g.form μ (multiplyRealForm (η j) A) :=
    l2RealForm_multiply_bounded g μ (η j) (L18Aux.continuous_of_smoothFn (hη j)).aestronglyMeasurable
      1 zero_le_one (fun x => by rw [abs_of_nonneg (hηrange j x).1]; exact (hηrange j x).2) A hA
  have hDj (j : ℕ) : L2RealForm g.form μ (multiplyRealForm (η j) A - A) :=
    l2RealForm_sub g μ _ A (hAj j) hA
  have hm (j : ℕ) : AEMeasurable (fun x => ENNReal.ofReal
      (formNormSq g.form (multiplyRealForm (η j) A - A) x)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable (formNormSq_aestronglyMeasurable g μ _ (hDj j)).aemeasurable
  have hb (j : ℕ) : (fun x => ENNReal.ofReal (formNormSq g.form (multiplyRealForm (η j) A - A) x)) ≤ᵐ[μ]
      (fun x => ENNReal.ofReal (formNormSq g.form A x)) := by
    exact Filter.Eventually.of_forall fun x => by
      apply ENNReal.ofReal_le_ofReal
      rw [multiplyRealForm_sub_normSq]
      have hs : (η j x - 1) ^ 2 ≤ 1 := by nlinarith [(hηrange j x).1, (hηrange j x).2]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (formNormSq_nonneg g.form A x)
  have hl (x : M.Carrier) : Tendsto (fun j => ENNReal.ofReal
      (formNormSq g.form (multiplyRealForm (η j) A - A) x)) atTop (𝓝 (0 : ENNReal)) := by
    have hc : Continuous (fun t : ℝ => (t - 1) ^ 2 * formNormSq g.form A x) := by fun_prop
    have hr : Tendsto (fun j => (η j x - 1) ^ 2 * formNormSq g.form A x) atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using (hc.tendsto 1).comp (ht x)
    simp_rw [multiplyRealForm_sub_normSq]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hr
  have hd := tendsto_lintegral_of_dominated_convergence'
    (fun x => ENNReal.ofReal (formNormSq g.form A x)) hm hb (ne_of_lt hA.2)
    (Filter.Eventually.of_forall hl)
  simpa only [formL2DistanceSq, lintegral_zero] using hd

theorem compactlySupportedRealForm_multiply_scalar (η : M.Carrier → ℝ)
    (hcη : HasCompactSupport η) (A : RealForm M k) :
    CompactlySupportedRealForm (multiplyRealForm η A) :=
  hcη.of_isClosed_subset isClosed_closure (multiplyRealForm_support_subset_scalar η A)

theorem exists_smooth_compact_cutoff_sequence (g : SmoothMetric M) (x : M.Carrier) :
    ∃ η : ℕ → M.Carrier → ℝ, (∀ j, SmoothFn (η j)) ∧ (∀ j, HasCompactSupport (η j)) ∧
      (∀ j y, η j y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ y, Tendsto (fun j => η j y) atTop (𝓝 1)) := by
  have h (j : ℕ) := L18Aux.exists_smooth_compact_cutoff g x
    (r := (j : ℝ) + 1) (R := (j : ℝ) + 2) (by positivity) (by linarith)
  choose η hη using h
  refine ⟨η, (fun j => (hη j).1), (fun j => (hη j).2.1), (fun j => (hη j).2.2.1), ?_⟩
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (inducedDistance g.form x y)
  have heq : (fun j => η j y) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with j hj
    apply (hη j).2.2.2.1 y
    have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  exact (tendsto_congr' heq).mpr tendsto_const_nhds

/-- Actual compact rough L² sections approximate every raw L² section. The
remaining smooth-core density step is local, rather than an unproved
assumption in the Hilbert completion. -/
theorem exists_compact_l2_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (x : M.Carrier) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ∃ As : ℕ → RealForm M k, (∀ j, L2RealForm g.form μ (As j) ∧ CompactlySupportedRealForm (As j)) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
  obtain ⟨η, hη, hcη, hηrange, ht⟩ := exists_smooth_compact_cutoff_sequence g x
  refine ⟨fun j => multiplyRealForm (η j) A, ?_, multiplyRealForm_l2_distance_tendsto g μ A hA η hη hηrange ht⟩
  intro j
  refine ⟨?_, compactlySupportedRealForm_multiply_scalar (η j) (hcη j) A⟩
  exact l2RealForm_multiply_bounded g μ (η j) (L18Aux.continuous_of_smoothFn (hη j)).aestronglyMeasurable
    1 zero_le_one (fun y => by rw [abs_of_nonneg (hηrange j y).1]; exact (hηrange j y).2) A hA


/-- Strong AE measurability of an actual alternating model field is
equivalent to strong AE measurability of its finite genuine coefficients. -/
theorem modelForm_aestronglyMeasurable_iff {D : Type*} [MeasurableSpace D]
    (ν : Measure D) (F : D → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    AEStronglyMeasurable F ν ↔
      ∀ I : Fin k → RIdx n, AEStronglyMeasurable (fun z => F z (fun r => realVec (I r))) ν := by
  classical
  constructor
  · intro h I
    simpa only [Function.comp_def, ContinuousAlternatingMap.apply_apply] using
      (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).continuous.comp_aestronglyMeasurable h
  · intro h
    have heq : (fun z => fun I : Fin k → RIdx n => F z (fun r => realVec (I r))) =
        (fun z => ∑ I : Fin k → RIdx n, Pi.single I (F z (fun r => realVec (I r)))) := by
      funext z J
      simp
    have hv : AEStronglyMeasurable (fun z => fun I : Fin k → RIdx n => F z (fun r => realVec (I r))) ν := by
      rw [heq]
      apply Finset.aestronglyMeasurable_fun_sum
      intro I _
      simpa only [Function.comp_def] using (Isometry.single I).continuous.comp_aestronglyMeasurable (h I)
    have hr := (modelFormReconstruction n k).continuous.comp_aestronglyMeasurable hv
    have hr' : AEStronglyMeasurable
        (fun z => modelFormReconstruction n k (fun I => F z (fun r => realVec (I r)))) ν := by
      simpa only [Function.comp_def] using hr
    exact hr'.congr (Filter.Eventually.of_forall fun z => modelFormReconstruction_coefficient (F z))

theorem modelForm_memLp_iff {D : Type*} [MeasurableSpace D] (ν : Measure D)
    (p : ENNReal) (F : D → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    MemLp F p ν ↔ ∀ I : Fin k → RIdx n, MemLp (fun z => F z (fun r => realVec (I r))) p ν := by
  constructor
  · intro h I
    simpa only [Function.comp_def, ContinuousAlternatingMap.apply_apply] using
      (ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).comp_memLp' h
  · intro h
    have hv : MemLp (fun z => fun I : Fin k → RIdx n => F z (fun r => realVec (I r))) p ν := MemLp.of_eval h
    have hr := (modelFormReconstruction n k).comp_memLp' hv
    have hr' : MemLp (fun z => modelFormReconstruction n k (fun I => F z (fun r => realVec (I r)))) p ν := by
      simpa only [Function.comp_def] using hr
    exact hr'.ae_eq (Filter.Eventually.of_forall fun z => modelFormReconstruction_coefficient (F z))

/-- Support and compactness of the actual model zero pullback do not require
the input form to be smooth. This is the raw L² chart-localization interface. -/
theorem chartFormPullbackZero_support_properties (x : M.Carrier) (A : RealForm M k)
    (hcA : CompactlySupportedRealForm A)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    HasCompactSupport (chartFormPullbackZero x A) ∧
      tsupport (chartFormPullbackZero x A) ⊆ chartTarget x ∧
      tsupport (chartFormPullbackZero x A) ⊆ chartPt x '' closure {y | A y ≠ 0} := by
  let K := chartPt x '' closure {y | A y ≠ 0}
  have hc : IsCompact K := hcA.image_of_continuousOn (by
    have hpt : ContinuousOn (chartPt x) (extChartAt (ComplexModel n) x).source := by
      simpa only [extChartAt_source] using chartPt_continuousOn x
    exact hpt.mono hAx)
  have hKt : K ⊆ chartTarget x := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) x).map_source (hAx hy)
  have hs : Function.support (chartFormPullbackZero x A) ⊆ K := by
    intro z hz
    by_cases hzt : z ∈ chartTarget x
    · have hn : A (chartInv x z) ≠ 0 := by
        intro hzero
        have hcz : chartForm A x z = 0 := by
          apply ContinuousAlternatingMap.ext
          intro v
          simp only [chartForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hzero]
          rfl
        exact hz (by simp only [chartFormPullbackZero, if_pos hzt, hcz])
      exact ⟨chartInv x z, subset_closure hn, (extChartAt (ComplexModel n) x).right_inv hzt⟩
    · exact False.elim (hz (by simp only [chartFormPullbackZero, if_neg hzt]))
  have hts : tsupport (chartFormPullbackZero x A) ⊆ K := closure_minimal hs hc.isClosed
  exact ⟨hc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKt, hts⟩

/-- Multipliers need only be bounded on the actual support of the input.
This permits finite chart localization of raw L² forms without inserting a
global bound on arbitrary partition weights. -/
theorem l2RealForm_multiply_bound_on_support (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ) (C : ℝ) (hC : 0 ≤ C)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hη : ∀ x, A x ≠ 0 → |η x| ≤ C) :
    L2RealForm g.form μ (multiplyRealForm η A) := by
  have hc (x : M.Carrier) (I : Fin k → RIdx n) : AEStronglyMeasurable
      (fun y => multiplyRealForm η A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    have hηr := hηm.mono_measure (Measure.restrict_le_self :
      μ.restrict (chartAt (ComplexVector n) x).source ≤ μ)
    simpa [multiplyRealForm, Pi.mul_def] using hηr.mul (hA.1 x I)
  have hm : AEStronglyMeasurable (formNormSq g.form (multiplyRealForm η A)) μ :=
    formInner_aestronglyMeasurable_of_coefficients g μ _ _ hc hc
  have hn : Integrable (formNormSq g.form (multiplyRealForm η A)) μ := by
    apply ((formNormSq_integrable g μ A hA).const_mul (C ^ 2)).mono_nonneg hm
      (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : A x = 0
      · rw [multiplyRealForm_normSq, (formNormSq_eq_zero_iff g.form A x).mpr hx, mul_zero, mul_zero]
      · rw [multiplyRealForm_normSq]
        have hh := (sq_le_sq₀ (abs_nonneg (η x)) hC).mpr (hη x hx)
        apply mul_le_mul_of_nonneg_right _ (formNormSq_nonneg g.form A x)
        simpa only [sq_abs] using hh
  refine ⟨hc, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => formNormSq_nonneg g.form _ x)).mp hn.2

theorem exists_finite_l2_chart_decomposition (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) (hcA : CompactlySupportedRealForm A) :
    ∃ s : Finset M.Carrier, ∃ As : s → RealForm M k,
      (∀ i, L2RealForm g.form μ (As i) ∧ CompactlySupportedRealForm (As i) ∧
        closure {y | As i y ≠ 0} ⊆ (extChartAt (ComplexModel n) (i : M.Carrier)).source) ∧
      (∑ i, As i) = A := by
  classical
  obtain ⟨s, p, hp, _, hps, hsum⟩ := L18Aux.exists_finite_smooth_partition hcA
  let As : s → RealForm M k := fun i => multiplyRealForm (p i) A
  have hAs (i : s) : L2RealForm g.form μ (As i) := by
    obtain ⟨c, hc⟩ := hcA.bddAbove_image ((L18Aux.continuous_of_smoothFn (hp i)).abs.continuousOn)
    apply l2RealForm_multiply_bound_on_support g μ (p i)
      (L18Aux.continuous_of_smoothFn (hp i)).aestronglyMeasurable (max c 0) (le_max_right _ _) A hA
    intro y hy
    exact (hc ⟨y, subset_closure hy, rfl⟩).trans (le_max_left _ _)
  refine ⟨s, As, (fun i => ⟨hAs i, compactlySupportedRealForm_multiply (p i) A hcA,
    (multiplyRealForm_support_subset_scalar (p i) A).trans (hps i)⟩), ?_⟩
  funext y
  simp only [Finset.sum_apply, As, multiplyRealForm]
  rw [← Finset.sum_smul]
  by_cases hy : A y = 0
  · simp only [hy, smul_zero]
  · rw [hsum y (subset_closure hy), one_smul]


theorem chartFormPullbackZero_apply_basis (x : M.Carrier) (A : RealForm M k)
    (z : ComplexVector n) (I : Fin k → RIdx n) :
    chartFormPullbackZero x A z (fun r => realVec (I r)) =
      (chartTarget x).indicator (fun w => formComponents A x w I) z := by
  classical
  by_cases hz : z ∈ chartTarget x
  · simp [chartFormPullbackZero, hz, chartForm_apply_basis]
  · simp [chartFormPullbackZero, hz]

theorem chartFormPullbackZero_aestronglyMeasurable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (x : M.Carrier) : AEStronglyMeasurable (chartFormPullbackZero x A) (lebesgueC n) := by
  apply (modelForm_aestronglyMeasurable_iff (lebesgueC n) (chartFormPullbackZero x A)).mpr
  intro I
  have hs : AEStronglyMeasurable (fun y => A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (extChartAt (ComplexModel n) x).source) := by
    simpa only [extChartAt_source] using hA.1 x I
  have ht : AEStronglyMeasurable (fun z => formComponents A x z I)
      ((lebesgueC n).restrict (chartTarget x)) :=
    L18Aux.aestronglyMeasurable_chartInv_of_volume g μ hμ x hs
  have hi := (aestronglyMeasurable_indicator_iff
    (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet).mpr ht
  exact hi.congr (Filter.Eventually.of_forall fun z => (chartFormPullbackZero_apply_basis x A z I).symm)

/-- The raw L² zero pullback is an actual standard model `MemLp` field. The
only measure transport used is the accepted AE chart law, and the metric
comparison constant is obtained on its genuine compact support. -/
theorem chartFormPullbackZero_memLp (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    MemLp (chartFormPullbackZero x A) 2 (lebesgueC n) := by
  let Φ := chartFormPullbackZero x A
  have ht : MeasurableSet (chartTarget x) := (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  have hΦ := chartFormPullbackZero_support_properties x A hcA hAx
  obtain ⟨C, hC, hcmp⟩ := formNormSq_chart_weighted_comparison g x (K := tsupport Φ)
    (show IsCompact (tsupport Φ) from hΦ.1) hΦ.2.1
  let W := (chartTarget x).indicator (fun z => Real.sqrt (realMetricFn g.form x z).det *
    formNormSq g.form A (chartInv x z))
  have hWT : IntegrableOn (fun z => Real.sqrt (realMetricFn g.form x z).det *
      formNormSq g.form A (chartInv x z)) (chartTarget x) (lebesgueC n) := by
    simpa only [smul_eq_mul] using L18Aux.integrableOn_chart_volume_smul g μ hμ x
      (formNormSq_integrable g μ A hA).integrableOn
  have hW : Integrable W (lebesgueC n) := (integrable_indicator_iff ht).mpr hWT
  have hWnonneg (z : ComplexVector n) : 0 ≤ W z := by
    by_cases hz : z ∈ chartTarget x
    · simpa only [W, Set.indicator_of_mem hz] using
        mul_nonneg (Real.sqrt_nonneg (realMetricFn g.form x z).det) (formNormSq_nonneg g.form A (chartInv x z))
    · simp only [W, Set.indicator_of_notMem hz, le_refl]
  apply (modelForm_memLp_iff (lebesgueC n) 2 Φ).mpr
  intro I
  have hcoef := (modelForm_aestronglyMeasurable_iff (lebesgueC n) Φ).mp
    (chartFormPullbackZero_aestronglyMeasurable g μ hμ A hA x) I
  have hsq : AEStronglyMeasurable (fun z => (Φ z (fun r => realVec (I r))) ^ 2) (lebesgueC n) := by
    simpa only [pow_two, Pi.mul_def] using hcoef.mul hcoef
  have hb (z : ComplexVector n) : (Φ z (fun r => realVec (I r))) ^ 2 ≤ C * W z := by
    by_cases hz : z ∈ tsupport Φ
    · have hzt : z ∈ chartTarget x := hΦ.2.1 hz
      have hcoefz : Φ z (fun r => realVec (I r)) = formComponents A x z I := by
        simpa only [Set.indicator_of_mem hzt] using chartFormPullbackZero_apply_basis x A z I
      rw [hcoefz]
      simpa only [W, Set.indicator_of_mem hzt] using (hcmp A z hz).1 I
    · have hzero : Φ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hzcoef : Φ z (fun r => realVec (I r)) = 0 := by rw [hzero]; rfl
      rw [hzcoef, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (le_of_lt hC) (hWnonneg z)
  have hi : Integrable (fun z => (Φ z (fun r => realVec (I r))) ^ 2) (lebesgueC n) :=
    (hW.const_mul C).mono_nonneg hsq (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (Filter.Eventually.of_forall hb)
  exact (memLp_two_iff_integrable_sq hcoef).mpr hi

theorem integral_formNormSq_chartSupport (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (x : M.Carrier) (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    (∫ y, formNormSq g.form A y ∂μ) =
      ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z)
        ∂lebesgueC n := by
  have hs : tsupport (formNormSq g.form A) ⊆ (extChartAt (ComplexModel n) x).source :=
    (formInner_support_subset_left g.form A A).trans hAx
  have hm : AEStronglyMeasurable (formNormSq g.form A)
      (μ.restrict (extChartAt (ComplexModel n) x).source) :=
    (formNormSq_aestronglyMeasurable g μ A hA).mono_measure Measure.restrict_le_self
  calc
    _ = ∫ y in (extChartAt (ComplexModel n) x).source, formNormSq g.form A y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy =>
        image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)))).symm
    _ = _ := by simpa only [smul_eq_mul] using L18Aux.integral_chart_volume_ae g μ hμ x hm

theorem modelForm_coefficients_sum_sq_le_norm (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    (∑ I : Fin k → RIdx n, (P (fun r => realVec (I r))) ^ 2) ≤
      (∑ I : Fin k → RIdx n, ‖ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
        (fun r => realVec (I r))‖ ^ 2) * ‖P‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ I : Fin k → RIdx n, ‖ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
        (fun r => realVec (I r))‖ ^ 2 * ‖P‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro I _
      let L := ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))
      have h := L.le_opNorm P
      have hh := (sq_le_sq₀ (norm_nonneg (L P)) (mul_nonneg (norm_nonneg L) (norm_nonneg P))).mpr h
      simpa only [L, ContinuousAlternatingMap.apply_apply, Real.norm_eq_abs, sq_abs, mul_pow] using hh
    _ = _ := by rw [Finset.sum_mul]

theorem formNormSq_chart_weighted_opNorm_comparison (g : SmoothMetric M) (x : M.Carrier)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKt : K ⊆ chartTarget x) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A : RealForm M k) z, z ∈ K →
      Real.sqrt (realMetricFn g.form x z).det * formNormSq g.form A (chartInv x z) ≤
        D * ‖chartForm A x z‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hcmp⟩ := formNormSq_chart_weighted_comparison g x hcK hKt
  let B := ∑ I : Fin k → RIdx n, ‖ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ
    (fun r => realVec (I r))‖ ^ 2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun I _ => sq_nonneg _)
  refine ⟨C * (B + 1), mul_pos hC (by linarith), ?_⟩
  intro A z hz
  have hb : (∑ I, (formComponents A x z I) ^ 2) ≤ B * ‖chartForm A x z‖ ^ 2 := by
    simpa only [chartForm_apply_basis, B] using modelForm_coefficients_sum_sq_le_norm (chartForm A x z)
  calc
    _ ≤ C * ∑ I, (formComponents A x z I) ^ 2 := (hcmp A z hz).2
    _ ≤ C * (B * ‖chartForm A x z‖ ^ 2) := mul_le_mul_of_nonneg_left hb (le_of_lt hC)
    _ ≤ C * ((B + 1) * ‖chartForm A x z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)) (le_of_lt hC)
    _ = _ := by ring


theorem ofReal_integral_norm_sq_eq_eLpNorm_sq {D F : Type*} [MeasurableSpace D]
    [NormedAddCommGroup F] (ν : Measure D) {f : D → F} (hf : MemLp f 2 ν) :
    ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂ν) = (eLpNorm f 2 ν) ^ 2 := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hm : MemLp (fun x => ‖f x‖ ^ 2) 1 ν := memLp_one_iff_integrable.mpr hi
  have h1 : eLpNorm (fun x => ‖f x‖ ^ 2) 1 ν = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂ν) := by
    simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs, abs_pow, abs_norm] using
      hm.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
  have hp := eLpNorm_norm_rpow (p := 1) (q := 2) f hf.aestronglyMeasurable (by norm_num)
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  have h2 : eLpNorm (fun x => ‖f x‖ ^ 2) 1 ν = (eLpNorm f 2 ν) ^ 2 := by
    simpa only [htwo, one_mul, Real.rpow_two, ENNReal.rpow_two] using hp
  exact h1.symm.trans h2

theorem realForm_sub_support_subset (A B : RealForm M k) :
    closure {y | (A - B) y ≠ 0} ⊆ closure {y | A y ≠ 0} ∪ closure {y | B y ≠ 0} := by
  rw [← closure_union]
  apply closure_mono
  intro y hy
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  exact hy (by simp only [Pi.sub_apply, h.1, h.2, sub_self])

theorem chartForm_sub (A B : RealForm M k) (x : M.Carrier) (z : ComplexVector n) :
    chartForm (A - B) x z = chartForm A x z - chartForm B x z := by
  apply ContinuousAlternatingMap.ext
  intro v
  rfl

theorem formNormSq_chartInv_eq_zero_of_chartForm_eq_zero (g : HermitianField M)
    (A : RealForm M k) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (hzero : chartForm A x z = 0) : formNormSq g A (chartInv x z) = 0 := by
  have hc : formComponents A x z = 0 := by
    funext I
    rw [← chartForm_apply_basis A x z I, hzero]
    rfl
  change formInner g A A (chartInv x z) = 0
  rw [formInner_chartInv_eq_tensorPairing g A A x hz]
  simp only [hc, tensorCoefficientPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

theorem formL2DistanceSq_eq_ofReal_integral (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : RealForm M k) (hA : L2RealForm g.form μ A) (hB : L2RealForm g.form μ B) :
    formL2DistanceSq g.form μ A B = ENNReal.ofReal (∫ y, formNormSq g.form (A - B) y ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (formNormSq_integrable g μ _ (l2RealForm_sub g μ A B hA hB))
    (Filter.Eventually.of_forall fun y => formNormSq_nonneg g.form (A - B) y)).symm

theorem chartForm_pushforward_sub_pullbackZero (x : M.Carrier) (A : RealForm M k)
    (P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (chartFormPushforward x P - A) x z = P z - chartFormPullbackZero x A z := by
  rw [chartForm_sub, chartFormPushforward_to_chart x P hz]
  simp only [chartFormPullbackZero, if_pos hz]

/-- Genuine chart reconstruction transports standard model L² approximation
errors to the frozen metric L² distance, with one constant fixed before the
approximating model test is chosen. -/
theorem chartFormPushforward_l2_distance_bound (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    {K : Set (ComplexVector n)} (hcK : IsCompact K) (hKt : K ⊆ chartTarget x)
    (hAK : tsupport (chartFormPullbackZero x A) ⊆ K) :
    ∃ D : ℝ, 0 < D ∧ ∀ P : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ,
      ContDiff ℝ ∞ P → tsupport P ⊆ K →
        formL2DistanceSq g.form μ (chartFormPushforward x P) A ≤
          ENNReal.ofReal D * (eLpNorm (chartFormPullbackZero x A - P) 2 (lebesgueC n)) ^ 2 := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let Φ := chartFormPullbackZero x A
  have hΦ : MemLp Φ 2 (lebesgueC n) := chartFormPullbackZero_memLp g μ hμ A hA hcA x hAx
  obtain ⟨D, hD, hcmp⟩ := formNormSq_chart_weighted_opNorm_comparison (k := k) g x hcK hKt
  refine ⟨D, hD, ?_⟩
  intro P hP hPK
  have hcP : HasCompactSupport P := hcK.of_isClosed_subset (isClosed_tsupport _) hPK
  have hPt : tsupport P ⊆ chartTarget x := hPK.trans hKt
  let B := chartFormPushforward x P
  have hB : L2RealForm g.form μ B := chartFormPushforward_l2 g μ hμ x P hP hcP hPt
  have hBs : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source :=
    chartFormPushforward_source_support x P hP hcP hPt
  have hBA : L2RealForm g.form μ (B - A) := l2RealForm_sub g μ B A hB hA
  have hBAs : closure {y | (B - A) y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source :=
    (realForm_sub_support_subset B A).trans (Set.union_subset hBs hAx)
  have hPm : MemLp P 2 (lebesgueC n) := hP.continuous.memLp_of_hasCompactSupport hcP
  have hdiff : MemLp (Φ - P) 2 (lebesgueC n) := hΦ.sub hPm
  have hiE : Integrable (fun z => ‖Φ z - P z‖ ^ 2) (lebesgueC n) := by
    simpa only [Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  have ht : MeasurableSet (chartTarget x) := (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
  let F := (chartTarget x).indicator (fun z => Real.sqrt (realMetricFn g.form x z).det *
    formNormSq g.form (B - A) (chartInv x z))
  have hiFT : IntegrableOn (fun z => Real.sqrt (realMetricFn g.form x z).det *
      formNormSq g.form (B - A) (chartInv x z)) (chartTarget x) (lebesgueC n) := by
    simpa only [smul_eq_mul] using L18Aux.integrableOn_chart_volume_smul g μ hμ x
      (formNormSq_integrable g μ (B - A) hBA).integrableOn
  have hiF : Integrable F (lebesgueC n) := (integrable_indicator_iff ht).mpr hiFT
  have hframe {z : ComplexVector n} (hz : z ∈ chartTarget x) :
      chartForm (B - A) x z = P z - Φ z := chartForm_pushforward_sub_pullbackZero x A P hz
  have hpoint (z : ComplexVector n) : F z ≤ D * ‖Φ z - P z‖ ^ 2 := by
    by_cases hzt : z ∈ chartTarget x
    · by_cases hzK : z ∈ K
      · have hn : ‖chartForm (B - A) x z‖ = ‖Φ z - P z‖ := by rw [hframe hzt, norm_sub_rev]
        simpa only [F, Set.indicator_of_mem hzt, hn] using hcmp (B - A) z hzK
      · have hΦz : Φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hAK h))
        have hPz : P z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hPK h))
        have hcz : chartForm (B - A) x z = 0 := by rw [hframe hzt, hPz, hΦz, sub_self]
        have hn := formNormSq_chartInv_eq_zero_of_chartForm_eq_zero g.form (B - A) x hzt hcz
        simp only [F, Set.indicator_of_mem hzt, hn, mul_zero, hΦz, hPz, sub_self, norm_zero,
          zero_pow (by decide : (2 : ℕ) ≠ 0), le_refl]
    · simpa only [F, Set.indicator_of_notMem hzt] using mul_nonneg (le_of_lt hD) (sq_nonneg ‖Φ z - P z‖)
  have heq : (∫ y, formNormSq g.form (B - A) y ∂μ) = ∫ z, F z ∂lebesgueC n := by
    rw [integral_formNormSq_chartSupport g μ hμ (B - A) hBA x hBAs]
    exact (integral_indicator ht).symm
  have hi : (∫ y, formNormSq g.form (B - A) y ∂μ) ≤ D * ∫ z, ‖Φ z - P z‖ ^ 2 ∂lebesgueC n := by
    rw [heq]
    calc
      _ ≤ ∫ z, D * ‖Φ z - P z‖ ^ 2 ∂lebesgueC n := integral_mono hiF (hiE.const_mul D) hpoint
      _ = _ := integral_const_mul D _
  have hsq : ENNReal.ofReal (∫ z, ‖Φ z - P z‖ ^ 2 ∂lebesgueC n) =
      (eLpNorm (Φ - P) 2 (lebesgueC n)) ^ 2 := by
    simpa only [Pi.sub_apply] using ofReal_integral_norm_sq_eq_eLpNorm_sq (lebesgueC n) hdiff
  rw [formL2DistanceSq_eq_ofReal_integral g μ B A hB hA]
  calc
    _ ≤ ENNReal.ofReal (D * ∫ z, ‖Φ z - P z‖ ^ 2 ∂lebesgueC n) := ENNReal.ofReal_le_ofReal hi
    _ = _ := by rw [ENNReal.ofReal_mul (le_of_lt hD), hsq]


theorem codifferentialRealForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M (k + 1))
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    codifferentialRealForm g.form (A + B) = codifferentialRealForm g.form A + codifferentialRealForm g.form B := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  rw [codifferentialRealForm_represents g μ hμ (A + B) (smoothRealForm_add A B hA hB) x (chartPt x x) ht I]
  simp only [formComponents_add, Pi.add_apply]
  rw [codifferentialRealForm_represents g μ hμ A hA x (chartPt x x) ht I,
    codifferentialRealForm_represents g μ hμ B hB x (chartPt x x) ht I]
  exact codifferentialComponents_add_at g.form x (formComponents A x) (formComponents B x) (chartPt x x)
    (smoothRealForm_coefficient_differentiableAt A hA x ht)
    (smoothRealForm_coefficient_differentiableAt B hB x ht) I

theorem codifferentialRealForm_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (A : RealForm M (k + 1))
    (hA : SmoothRealForm A) : codifferentialRealForm g.form (c • A) = c • codifferentialRealForm g.form A := by
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  rw [codifferentialRealForm_represents g μ hμ (c • A) (smoothRealForm_smul c A hA) x (chartPt x x) ht I]
  simp only [formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [codifferentialRealForm_represents g μ hμ A hA x (chartPt x x) ht I]
  exact codifferentialComponents_smul_at g.form x c (formComponents A x) (chartPt x x)
    (smoothRealForm_coefficient_differentiableAt A hA x ht) I

theorem hodgeRealForm_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    hodgeRealForm g.form k (A + B) = hodgeRealForm g.form k A + hodgeRealForm g.form k B := by
  cases k with
  | zero =>
      simp only [hodgeRealForm, exteriorRealForm_add A B hA hB]
      exact codifferentialRealForm_add g μ hμ _ _ (exteriorRealForm_smooth A hA) (exteriorRealForm_smooth B hB)
  | succ j =>
      simp only [hodgeRealForm, codifferentialRealForm_add g μ hμ A B hA hB,
        exteriorRealForm_add A B hA hB,
        exteriorRealForm_add _ _ (codifferentialRealForm_smooth g μ hμ A hA)
          (codifferentialRealForm_smooth g μ hμ B hB),
        codifferentialRealForm_add g μ hμ _ _ (exteriorRealForm_smooth A hA) (exteriorRealForm_smooth B hB)]
      abel

theorem hodgeRealForm_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (A : RealForm M k)
    (hA : SmoothRealForm A) : hodgeRealForm g.form k (c • A) = c • hodgeRealForm g.form k A := by
  cases k with
  | zero =>
      simp only [hodgeRealForm, exteriorRealForm_smul c A hA]
      exact codifferentialRealForm_smul g μ hμ c _ (exteriorRealForm_smooth A hA)
  | succ j =>
      simp only [hodgeRealForm, codifferentialRealForm_smul g μ hμ c A hA,
        exteriorRealForm_smul c A hA,
        exteriorRealForm_smul c _ (codifferentialRealForm_smooth g μ hμ A hA),
        codifferentialRealForm_smul g μ hμ c _ (exteriorRealForm_smooth A hA), smul_add]

theorem hodgeRealForm_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    hodgeRealForm g.form k 0 = 0 := by
  simpa only [zero_smul] using hodgeRealForm_smul g μ hμ 0 (0 : RealForm M k) smoothRealForm_zero

theorem hodgeCorePair_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A W B Z : RealForm M k}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W)
    (hBZ : OperatorCandidates.HodgeCorePair g.form μ B Z) :
    OperatorCandidates.HodgeCorePair g.form μ (A + B) (W + Z) := by
  obtain ⟨hA, hcA, hW⟩ := (hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  obtain ⟨hB, hcB, hZ⟩ := (hodgeCorePair_iff_computed g μ hμ B Z).mp hBZ
  exact (hodgeCorePair_iff_computed g μ hμ _ _).mpr
    ⟨smoothRealForm_add A B hA hB, compactlySupportedRealForm_add A B hcA hcB,
      by rw [hW, hZ, hodgeRealForm_add g μ hμ A B hA hB]⟩

theorem hodgeCorePair_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) {A W : RealForm M k}
    (hAW : OperatorCandidates.HodgeCorePair g.form μ A W) :
    OperatorCandidates.HodgeCorePair g.form μ (c • A) (c • W) := by
  obtain ⟨hA, hcA, hW⟩ := (hodgeCorePair_iff_computed g μ hμ A W).mp hAW
  exact (hodgeCorePair_iff_computed g μ hμ _ _).mpr
    ⟨smoothRealForm_smul c A hA, compactlySupportedRealForm_multiply (fun _ => c) A hcA,
      by rw [hW, hodgeRealForm_smul g μ hμ c A hA]⟩

/-- The genuine smooth compact core inside the raw metric L² space. -/
def smoothCompactL2Submodule (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Submodule ℝ (L2FormSpace g μ k) where
  carrier := {u | SmoothRealForm u.toSection ∧ CompactlySupportedRealForm u.toSection}
  zero_mem' := by
    refine ⟨smoothRealForm_zero, ?_⟩
    change IsCompact (closure {y : M.Carrier | (0 : RealForm M k) y ≠ 0})
    simpa using (isCompact_empty : IsCompact (∅ : Set M.Carrier))
  add_mem' := by
    intro u v hu hv
    exact ⟨smoothRealForm_add _ _ hu.1 hv.1, compactlySupportedRealForm_add _ _ hu.2 hv.2⟩
  smul_mem' := by
    intro c u hu
    exact ⟨smoothRealForm_smul c _ hu.1,
      compactlySupportedRealForm_multiply (fun _ => c) _ hu.2⟩

/-- The compact smooth core in the actual Hilbert completion. -/
def smoothCompactRealizedSubmodule (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    Submodule ℝ (L2FormHilbert g μ k) :=
  (smoothCompactL2Submodule g μ k).map
    (UniformSpace.Completion.toComplL : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k).toLinearMap

theorem realize_smooth_compact_mem (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hsA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    realizeL2Form g μ (L2FormSpace.ofSection A hA) ∈ smoothCompactRealizedSubmodule g μ k :=
  ⟨L2FormSpace.ofSection A hA, ⟨hsA, hcA⟩, rfl⟩

/-- Every chart-supported rough L² form is a strong limit of genuine global
smooth compact forms; the common compact support is chosen before the sequence. -/
theorem exists_smooth_compact_chart_l2_approximation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    ∃ As : ℕ → RealForm M k,
      (∀ j, SmoothRealForm (As j) ∧ CompactlySupportedRealForm (As j) ∧ L2RealForm g.form μ (As j)) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let Φ := chartFormPullbackZero x A
  have hΦ := chartFormPullbackZero_support_properties x A hcA hAx
  obtain ⟨K, hcK, hKt, hΦK, happrox⟩ := smooth_compact_L2_approx_in_open (lebesgueC n)
    (chartFormPullbackZero_memLp g μ hμ A hA hcA x hAx) hΦ.1
    (isOpen_extChartAt_target (I := ComplexModel n) x) hΦ.2.1
  obtain ⟨D, hD, hbound⟩ := chartFormPushforward_l2_distance_bound g μ hμ A hA hcA x hAx hcK hKt hΦK
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose P hP hcP hPK herror using fun j => happrox (ε j) (hε j)
  let As : ℕ → RealForm M k := fun j => chartFormPushforward x (P j)
  have hsAs (j : ℕ) : SmoothRealForm (As j) :=
    chartFormPushforward_smooth x (P j) (hP j) (hcP j) ((hPK j).trans hKt)
  have hcAs (j : ℕ) : CompactlySupportedRealForm (As j) :=
    chartFormPushforward_compactlySupported x (P j) (hP j) (hcP j) ((hPK j).trans hKt)
  have hAs (j : ℕ) : L2RealForm g.form μ (As j) :=
    chartFormPushforward_l2 g μ hμ x (P j) (hP j) (hcP j) ((hPK j).trans hKt)
  refine ⟨As, fun j => ⟨hsAs j, hcAs j, hAs j⟩, ?_⟩
  have hmaj (j : ℕ) : formL2DistanceSq g.form μ (As j) A ≤ ENNReal.ofReal (D * ε j ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal D * (eLpNorm (Φ - P j) 2 (lebesgueC n)) ^ 2 := hbound _ (hP j) (hPK j)
      _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (ε j)) ^ 2 := by gcongr; exact herror j
      _ = _ := by rw [ENNReal.ofReal_mul hD.le, ENNReal.ofReal_pow (hε j).le]
  have hlim : Tendsto (fun j => ENNReal.ofReal (D * ε j ^ 2)) atTop (𝓝 0) := by
    have ht : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using ENNReal.tendsto_ofReal ((ht.pow 2).const_mul D)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hmaj

theorem realize_chart_supported_mem_core_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) (x : M.Carrier)
    (hAx : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    realizeL2Form g μ (L2FormSpace.ofSection A hA) ∈
      (smoothCompactRealizedSubmodule g μ k).topologicalClosure := by
  obtain ⟨As, hAs, ht⟩ := exists_smooth_compact_chart_l2_approximation g μ hμ A hA hcA x hAx
  let us : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (As j) (hAs j).2.2
  have hlim : Tendsto (fun j => realizeL2Form g μ (us j)) atTop
      (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection A hA))) :=
    (tendsto_realizeL2Form_iff g μ us (L2FormSpace.ofSection A hA)).mpr ht
  exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun j =>
    realize_smooth_compact_mem g μ (As j) (hAs j).2.2 (hAs j).1 (hAs j).2.1)

/-- Finite genuine chart localization upgrades the local approximation to
every compactly supported rough form, with the original global L² metric. -/
theorem realize_compact_mem_core_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A)
    (hcA : CompactlySupportedRealForm A) :
    realizeL2Form g μ (L2FormSpace.ofSection A hA) ∈
      (smoothCompactRealizedSubmodule g μ k).topologicalClosure := by
  classical
  obtain ⟨s, As, hAs, hsum⟩ := exists_finite_l2_chart_decomposition g μ A hA hcA
  let us : s → L2FormSpace g μ k := fun i => L2FormSpace.ofSection (As i) (hAs i).1
  have hsumU : (∑ i, us i) = L2FormSpace.ofSection A hA := by
    apply L2FormSpace.toSection_injective g μ k
    exact (map_sum (l2FormSubmodule g μ k).subtype us Finset.univ).trans hsum
  have hsumH : (∑ i, realizeL2Form g μ (us i)) =
      realizeL2Form g μ (L2FormSpace.ofSection A hA) := by
    let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
    change (∑ i, F (us i)) = F (L2FormSpace.ofSection A hA)
    rw [← map_sum, hsumU]
  rw [← hsumH]
  apply Submodule.sum_mem
  intro i _
  exact realize_chart_supported_mem_core_closure g μ hμ (As i) (hAs i).1
    (hAs i).2.1 (i : M.Carrier) (hAs i).2.2

/-- Cutoff exhaustion and the proved chart approximation place every raw
L² section in the closure of the actual smooth compact core. -/
theorem realize_mem_core_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    realizeL2Form g μ (L2FormSpace.ofSection A hA) ∈
      (smoothCompactRealizedSubmodule g μ k).topologicalClosure := by
  classical
  cases isEmpty_or_nonempty M.Carrier with
  | inl h =>
      letI := h
      have hzero : L2FormSpace.ofSection A hA = 0 := by
        apply L2FormSpace.toSection_injective g μ k
        funext y
        exact isEmptyElim y
      rw [hzero]
      exact Submodule.zero_mem _
  | inr h =>
      letI := h
      obtain ⟨As, hAs, ht⟩ := exists_compact_l2_approximation g μ (Classical.arbitrary M.Carrier) A hA
      let us : ℕ → L2FormSpace g μ k := fun j => L2FormSpace.ofSection (As j) (hAs j).1
      have hlim : Tendsto (fun j => realizeL2Form g μ (us j)) atTop
          (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection A hA))) :=
        (tendsto_realizeL2Form_iff g μ us (L2FormSpace.ofSection A hA)).mpr ht
      exact (smoothCompactRealizedSubmodule g μ k).isClosed_topologicalClosure.mem_of_tendsto hlim
        (Filter.Eventually.of_forall fun j =>
          realize_compact_mem_core_closure g μ hμ (As j) (hAs j).1 (hAs j).2)

/-- Genuine smooth compact sections are dense in the constructed Hilbert
space. Both raw section density and all local smoothing are proved above. -/
theorem smoothCompactRealizedSubmodule_closure_eq_top (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (smoothCompactRealizedSubmodule g μ k).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro u
  have hs : Set.range (realizeL2Form (k := k) g μ) ⊆
      (smoothCompactRealizedSubmodule g μ k).topologicalClosure := by
    rintro _ ⟨a, rfl⟩
    exact realize_mem_core_closure g μ hμ a.toSection a.toSection_l2
  have hc := closure_minimal hs (smoothCompactRealizedSubmodule g μ k).isClosed_topologicalClosure
  apply hc
  rw [(realizeL2Form_denseRange g μ k).closure_range]
  exact Set.mem_univ u

/-- The first projection of the frozen Hodge core is precisely the genuine
compact smooth subspace; every output is the computed global Hodge expression. -/
theorem hodgeCoreRealizedGraph_domain_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Prod.fst '' hodgeCoreRealizedGraph g μ k = (smoothCompactRealizedSubmodule g μ k : Set _) := by
  ext u
  constructor
  · rintro ⟨p, ⟨A, W, hcore, rfl⟩, rfl⟩
    exact realize_smooth_compact_mem g μ A hcore.2.2.2.1 hcore.1 hcore.2.1
  · rintro ⟨a, ha, rfl⟩
    have hcore := hodgeRealForm_corePair g μ hμ a.toSection ha.1 ha.2
    exact ⟨_, ⟨a.toSection, hodgeRealForm g.form k a.toSection, hcore, rfl⟩, rfl⟩

/-- Density now applies to the actual frozen Hodge core domain, rather than
only to an abstract completion or an independently chosen test space. -/
theorem hodgeCoreRealizedGraph_domain_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Dense (Prod.fst '' hodgeCoreRealizedGraph g μ k) := by
  rw [hodgeCoreRealizedGraph_domain_eq g μ hμ k, dense_iff_closure_eq,
    ← Submodule.topologicalClosure_coe, smoothCompactRealizedSubmodule_closure_eq_top g μ hμ k]
  rfl

/-- The exact realized Hodge core is a linear graph; no independently chosen
operator or domain is introduced. -/
def hodgeCoreGraphSubmodule (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Submodule ℝ (L2FormHilbert g μ k × L2FormHilbert g μ k) where
  carrier := hodgeCoreRealizedGraph g μ k
  zero_mem' := by
    have hs : SmoothRealForm (0 : RealForm M k) := smoothRealForm_zero
    have hc : CompactlySupportedRealForm (0 : RealForm M k) := by
      simpa [CompactlySupportedRealForm] using (isCompact_empty : IsCompact (∅ : Set M.Carrier))
    have hcore : OperatorCandidates.HodgeCorePair g.form μ (0 : RealForm M k) 0 :=
      (hodgeCorePair_iff_computed g μ hμ _ _).mpr ⟨hs, hc, (hodgeRealForm_zero g μ hμ k).symm⟩
    refine ⟨0, 0, hcore, ?_⟩
    let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
    exact Prod.ext (map_zero F).symm (map_zero F).symm
  add_mem' := by
    rintro p q ⟨A, W, hAW, rfl⟩ ⟨B, Z, hBZ, rfl⟩
    have hcore := hodgeCorePair_add g μ hμ hAW hBZ
    refine ⟨A + B, W + Z, hcore, ?_⟩
    let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
    change (F (L2FormSpace.ofSection A hAW.2.2.2.1) + F (L2FormSpace.ofSection B hBZ.2.2.2.1),
      F (L2FormSpace.ofSection W hAW.2.2.2.2.1) + F (L2FormSpace.ofSection Z hBZ.2.2.2.2.1)) = _
    rw [← map_add, ← map_add]
    rfl
  smul_mem' := by
    rintro c p ⟨A, W, hAW, rfl⟩
    have hcore := hodgeCorePair_smul g μ hμ c hAW
    refine ⟨c • A, c • W, hcore, ?_⟩
    let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
    change (c • F (L2FormSpace.ofSection A hAW.2.2.2.1),
      c • F (L2FormSpace.ofSection W hAW.2.2.2.2.1)) = _
    rw [← map_smul, ← map_smul]
    rfl

theorem hodgeCoreGraphSubmodule_no_vertical (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p : L2FormHilbert g μ k × L2FormHilbert g μ k)
    (hp : p ∈ hodgeCoreGraphSubmodule g μ hμ k) (hp0 : p.1 = 0) : p.2 = 0 := by
  obtain ⟨A, W, hAW, rfl⟩ := hp
  let F : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k := UniformSpace.Completion.toComplL
  have hA0 : A = 0 := smoothRealForm_eq_of_ae g μ hμ A 0 hAW.1 smoothRealForm_zero
    ((realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection A hAW.2.2.2.1) 0).mp
      (hp0.trans (map_zero F).symm))
  have hW := ((hodgeCorePair_iff_computed g μ hμ A W).mp hAW).2.2
  have hW0 : W = 0 := by rw [hW, hA0, hodgeRealForm_zero g μ hμ k]
  change realizeL2Form g μ (L2FormSpace.ofSection W hAW.2.2.2.2.1) = 0
  have hsec : L2FormSpace.ofSection W hAW.2.2.2.2.1 = 0 := by
    apply L2FormSpace.toSection_injective g μ k
    exact hW0
  rw [hsec]
  exact map_zero F

/-- The densely defined actual core operator, obtained from its verified
single-valued graph. The graph identity below rules out the junk branch. -/
def hodgeCoreOperator (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    L2FormHilbert g μ k →ₗ.[ℝ] L2FormHilbert g μ k :=
  (hodgeCoreGraphSubmodule g μ hμ k).toLinearPMap

theorem hodgeCoreOperator_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (hodgeCoreOperator g μ hμ k).graph = hodgeCoreGraphSubmodule g μ hμ k :=
  Submodule.toLinearPMap_graph_eq _ (hodgeCoreGraphSubmodule_no_vertical g μ hμ)

theorem hodgeCoreOperator_domain_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Dense ((hodgeCoreOperator g μ hμ k).domain : Set (L2FormHilbert g μ k)) := by
  have heq : ((hodgeCoreOperator g μ hμ k).domain : Set (L2FormHilbert g μ k)) =
      Prod.fst '' hodgeCoreRealizedGraph g μ k := by
    rw [← LinearPMap.graph_map_fst_eq_domain, hodgeCoreOperator_graph]
    rfl
  rw [heq]
  exact hodgeCoreRealizedGraph_domain_dense g μ hμ k

theorem hodgeCoreRealizedGraph_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {p q : L2FormHilbert g μ k × L2FormHilbert g μ k}
    (hp : p ∈ hodgeCoreRealizedGraph g μ k) (hq : q ∈ hodgeCoreRealizedGraph g μ k) :
    inner ℝ p.2 q.1 = inner ℝ p.1 q.2 := by
  obtain ⟨A, W, hAW, rfl⟩ := hp
  obtain ⟨B, Z, hBZ, rfl⟩ := hq
  simpa only [realizeL2Form_inner, L2FormSpace.toSection_ofSection] using
    hodgeCorePair_symmetric g μ hμ hAW hBZ

theorem hodgeCoreOperator_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (hodgeCoreOperator g μ hμ k).IsFormalAdjoint (hodgeCoreOperator g μ hμ k) := by
  intro u v
  apply hodgeCoreRealizedGraph_symmetric g μ hμ
    (p := ((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) u))
    (q := ((v : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) v))
  · change ((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) u) ∈
      hodgeCoreGraphSubmodule g μ hμ k
    rw [← hodgeCoreOperator_graph]
    rw [LinearPMap.mem_graph_iff]
    exact ⟨u, rfl, rfl⟩
  · change ((v : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) v) ∈
      hodgeCoreGraphSubmodule g μ hμ k
    rw [← hodgeCoreOperator_graph]
    rw [LinearPMap.mem_graph_iff]
    exact ⟨v, rfl, rfl⟩

theorem hodgeCoreOperator_nonnegative (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) (u : (hodgeCoreOperator g μ hμ k).domain) :
    0 ≤ inner ℝ (u : L2FormHilbert g μ k) ((hodgeCoreOperator g μ hμ k) u) := by
  have hp : ((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) u) ∈
      hodgeCoreGraphSubmodule g μ hμ k := by
    rw [← hodgeCoreOperator_graph]
    rw [LinearPMap.mem_graph_iff]
    exact ⟨u, rfl, rfl⟩
  obtain ⟨A, W, hAW, heq⟩ := hp
  change 0 ≤ inner ℝ (((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) u).1)
    (((u : L2FormHilbert g μ k), (hodgeCoreOperator g μ hμ k) u).2)
  rw [heq]
  simpa only [realizeL2Form_inner, L2FormSpace.toSection_ofSection] using
    hodgeCorePair_nonnegative g μ hμ hAW

theorem hodgeCoreOperator_closable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (hodgeCoreOperator g μ hμ k).IsClosable :=
  ((hodgeCoreOperator g μ hμ k).adjoint_isClosed (hodgeCoreOperator_domain_dense g μ hμ k)).isClosable.leIsClosable
    ((hodgeCoreOperator_symmetric g μ hμ k).le_adjoint (hodgeCoreOperator_domain_dense g μ hμ k))

/-- The original sequence definition of the minimal graph is exactly the
closure of the actual densely defined Hodge operator. -/
theorem hodgeMinimalGraph_iff_operator_closure (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k)
    (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W) :
    OperatorCandidates.HodgeMinimalGraph g.form μ A W ↔
      (realizeL2Form g μ (L2FormSpace.ofSection A hA),
        realizeL2Form g μ (L2FormSpace.ofSection W hW)) ∈
          (hodgeCoreOperator g μ hμ k).closure.graph := by
  rw [hodgeMinimalGraph_iff_core_closure g μ A W hA hW,
    ← (hodgeCoreOperator_closable g μ hμ k).graph_closure_eq_closure_graph,
    hodgeCoreOperator_graph]
  rfl

/-- The original distributional maximal graph is exactly the adjoint graph,
with the genuine core density proved above. -/
theorem hodgeMaximalGraph_iff_operator_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M k)
    (hA : L2RealForm g.form μ A) (hW : L2RealForm g.form μ W) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W ↔
      (realizeL2Form g μ (L2FormSpace.ofSection A hA),
        realizeL2Form g μ (L2FormSpace.ofSection W hW)) ∈
          (hodgeCoreOperator g μ hμ k).adjoint.graph := by
  rw [hodgeMaximalGraph_iff_core_pairing g μ A W hA hW,
    LinearPMap.adjoint_graph_eq_graph_adjoint (hodgeCoreOperator_domain_dense g μ hμ k),
    hodgeCoreOperator_graph, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    have hh := h (a, b) hab
    exact sub_eq_zero.mpr (by simpa only [real_inner_comm] using hh)
  · intro h p hp
    have hh := sub_eq_zero.mp (h p.1 p.2 hp)
    simpa only [real_inner_comm] using hh

/-- The actual kernel of the first-order Friedrichs commutator. The second
term comes from distributional integration by parts on the variable coefficient. -/
def friedrichsCommutatorKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a ρ : E → ℝ) (v x y : E) : ℝ :=
  fderiv ℝ ρ (x - y) v * (a x - a y) + ρ (x - y) * fderiv ℝ a y v

/-- A uniform pointwise majorant for the genuine commutator kernel. Its
right side depends only on x-y, the kernel and the coefficient Lipschitz bound. -/
theorem friedrichsCommutatorKernel_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a ρ : E → ℝ)
    (K : NNReal) (ha : LipschitzWith K a) (v x y : E) :
    ‖friedrichsCommutatorKernel a ρ v x y‖ ≤
      K * (‖x - y‖ * ‖fderiv ℝ ρ (x - y) v‖ + ‖v‖ * ‖ρ (x - y)‖) := by
  have hdiff : ‖a x - a y‖ ≤ K * ‖x - y‖ := by
    simpa only [dist_eq_norm] using ha.dist_le_mul x y
  have hderiv : ‖fderiv ℝ a y v‖ ≤ K * ‖v‖ :=
    ((fderiv ℝ a y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ ha) (norm_nonneg v))
  calc
    _ ≤ ‖fderiv ℝ ρ (x - y) v * (a x - a y)‖ + ‖ρ (x - y) * fderiv ℝ a y v‖ := norm_add_le _ _
    _ = ‖fderiv ℝ ρ (x - y) v‖ * ‖a x - a y‖ + ‖ρ (x - y)‖ * ‖fderiv ℝ a y v‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖fderiv ℝ ρ (x - y) v‖ * (K * ‖x - y‖) + ‖ρ (x - y)‖ * (K * ‖v‖) := by gcongr
    _ = _ := by ring

/-- Exact integration-by-parts identity for the first-order mollifier
commutator, on genuine compact C¹ inputs and the original Haar measure. -/
theorem friedrichs_commutator_integral_identity {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (a ρ u : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hu : ContDiff ℝ 1 u) (hcu : HasCompactSupport u) (v x : E) :
    a x * (∫ y, fderiv ℝ ρ (x - y) v * u y ∂ν) -
      (∫ y, ρ (x - y) * (a y * fderiv ℝ u y v) ∂ν) =
        ∫ y, friedrichsCommutatorKernel a ρ v x y * u y ∂ν := by
  let U : E → ℝ := fun y => a y * u y
  let R : E → ℝ := fun y => ρ (x - y)
  have hU : ContDiff ℝ 1 U := ha.mul hu
  have hcU : HasCompactSupport U := hcu.mul_left
  have hR : ContDiff ℝ 1 R := hρ.comp (contDiff_const.sub contDiff_id)
  have hdU (y : E) : fderiv ℝ U y v = a y * fderiv ℝ u y v + u y * fderiv ℝ a y v := by
    exact DFunLike.congr_fun (fderiv_fun_mul (ha.differentiable one_ne_zero y)
      (hu.differentiable one_ne_zero y)) v
  have hdR (y : E) : fderiv ℝ R y v = -fderiv ℝ ρ (x - y) v := by
    have hd := ((hρ.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)).fderiv
    simpa only [R, Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.id_apply, map_neg] using DFunLike.congr_fun hd v
  have hdρ : Continuous (fun y => fderiv ℝ ρ (x - y) v) :=
    ((hρ.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply continuous_const
  have hdu : Continuous (fun y => fderiv ℝ u y v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hda : Continuous (fun y => fderiv ℝ a y v) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbase : Integrable (fun y => fderiv ℝ ρ (x - y) v * u y) ν :=
    (hdρ.mul hu.continuous).integrable_of_hasCompactSupport hcu.mul_left
  have hX : Integrable (fun y => ρ (x - y) * (a y * fderiv ℝ u y v)) ν :=
    (hR.continuous.mul (ha.continuous.mul hdu)).integrable_of_hasCompactSupport
      (hcu.fderiv_apply ℝ v).mul_left.mul_left
  have hY : Integrable (fun y => fderiv ℝ ρ (x - y) v * a y * u y) ν :=
    ((hdρ.mul ha.continuous).mul hu.continuous).integrable_of_hasCompactSupport hcu.mul_left
  have hZ : Integrable (fun y => ρ (x - y) * fderiv ℝ a y v * u y) ν :=
    ((hR.continuous.mul hda).mul hu.continuous).integrable_of_hasCompactSupport hcu.mul_left
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := ν)
    (f := U) (g := R) (v := v)
    ((((hU.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hR.continuous).integrable_of_hasCompactSupport
      (hcU.fderiv_apply ℝ v).mul_right)
    ((hU.continuous.mul ((hR.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport hcU.mul_right)
    ((hU.continuous.mul hR.continuous).integrable_of_hasCompactSupport hcU.mul_right)
    (fun y _ => hU.differentiable one_ne_zero y) (fun y _ => hR.differentiable one_ne_zero y)
  have hleft : (fun y => U y * fderiv ℝ R y v) =
      (fun y => -(fderiv ℝ ρ (x - y) v * a y * u y)) := by
    funext y
    rw [hdR]
    dsimp only [U]
    ring
  have hright : (fun y => fderiv ℝ U y v * R y) =
      (fun y => ρ (x - y) * (a y * fderiv ℝ u y v) + ρ (x - y) * fderiv ℝ a y v * u y) := by
    funext y
    rw [hdU]
    dsimp only [R]
    ring
  rw [hleft, hright, integral_neg, integral_add hX hZ] at hIBP
  have hrel := neg_inj.mp hIBP
  calc
    _ = a x * (∫ y, fderiv ℝ ρ (x - y) v * u y ∂ν) -
        (∫ y, fderiv ℝ ρ (x - y) v * a y * u y ∂ν) +
        (∫ y, ρ (x - y) * fderiv ℝ a y v * u y ∂ν) := by rw [hrel]; ring
    _ = ∫ y, a x * (fderiv ℝ ρ (x - y) v * u y) -
        (fderiv ℝ ρ (x - y) v * a y * u y) + ρ (x - y) * fderiv ℝ a y v * u y ∂ν := by
      have hsum := (integral_add ((hbase.const_mul (a x)).sub hY) hZ).symm
      simp only [Pi.add_apply, Pi.sub_apply] at hsum
      rw [integral_sub (hbase.const_mul (a x)) hY, integral_const_mul] at hsum
      simpa only [Pi.add_apply, Pi.sub_apply] using hsum
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun y => by
      dsimp only [friedrichsCommutatorKernel]
      ring)

/-- Weighted Cauchy--Schwarz in a form used by the commutator kernel bound.
The zero-mass case is included, and all integrability is explicit. -/
theorem weighted_integral_sq_le {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (κ f : X → ℝ) (hκ : ∀ y, 0 ≤ κ y) (hκi : Integrable κ ν)
    (hκf : Integrable (fun y => κ y * f y) ν)
    (hκf2 : Integrable (fun y => κ y * f y ^ 2) ν) :
    (∫ y, κ y * f y ∂ν) ^ 2 ≤ (∫ y, κ y ∂ν) * ∫ y, κ y * f y ^ 2 ∂ν := by
  let m := ∫ y, κ y ∂ν
  let z := ∫ y, κ y * f y ∂ν
  let e := ∫ y, κ y * f y ^ 2 ∂ν
  have hm : 0 ≤ m := integral_nonneg hκ
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · have hκ0 : κ =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hκ hκi).mp hm0.symm
    have hz : z = 0 := by
      exact integral_eq_zero_of_ae (hκ0.mono fun y hy => by simp only [hy, zero_mul, Pi.zero_apply])
    change z ^ 2 ≤ m * e
    rw [← hm0, hz]
    simp
  · have hquad (t : ℝ) : 2 * t * z - t ^ 2 * m ≤ e := by
      have hi := integral_mono ((hκf.const_mul (2 * t)).sub (hκi.const_mul (t ^ 2))) hκf2
        (fun y => by
          change 2 * t * (κ y * f y) - t ^ 2 * κ y ≤ κ y * f y ^ 2
          nlinarith [mul_nonneg (hκ y) (sq_nonneg (f y - t))])
      simp only [Pi.sub_apply] at hi
      simpa only [m, z, e, integral_sub (hκf.const_mul (2 * t)) (hκi.const_mul (t ^ 2)), integral_const_mul] using hi
    have heq : 2 * (z / m) * z - (z / m) ^ 2 * m = z ^ 2 / m := by
      field_simp [ne_of_gt hmpos]
      ring
    have hh := hquad (z / m)
    rw [heq] at hh
    simpa only [mul_comm] using (div_le_iff₀ hmpos).mp hh

/-- The row estimate for a signed integral kernel, obtained from the actual
Bochner integral and weighted Cauchy--Schwarz. -/
theorem integral_kernel_norm_sq_le {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure X) (k : X → ℝ) (f : X → F)
    (hk : Integrable (fun y => |k y|) ν)
    (hkf : Integrable (fun y => k y • f y) ν)
    (hkf2 : Integrable (fun y => |k y| * ‖f y‖ ^ 2) ν) :
    ‖∫ y, k y • f y ∂ν‖ ^ 2 ≤ (∫ y, |k y| ∂ν) * ∫ y, |k y| * ‖f y‖ ^ 2 ∂ν := by
  have hn : Integrable (fun y => |k y| * ‖f y‖) ν := by
    simpa only [norm_smul, Real.norm_eq_abs] using hkf.norm
  have hCS := weighted_integral_sq_le ν (fun y => |k y|) (fun y => ‖f y‖)
    (fun y => abs_nonneg _) hk hn hkf2
  apply (pow_le_pow_left₀ (norm_nonneg _) ?_ 2).trans hCS
  simpa only [norm_smul, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => k y • f y)

/-- The L² Schur estimate used to bound Friedrichs commutators uniformly in
the mollifier scale. It applies in particular to compact-input kernels, for
which both joint integrability hypotheses follow from their actual supports. -/
theorem friedrichs_schur_integral_L2_bound {X Y F : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (K : X → Y → ℝ) (f : Y → F) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ x, Integrable (fun y => |K x y|) ν)
    (hrowC : ∀ x, (∫ y, |K x y| ∂ν) ≤ C)
    (hcolC : ∀ y, (∫ x, |K x y| ∂μ) ≤ C)
    (hprod : Integrable (fun p : X × Y => K p.1 p.2 • f p.2) (μ.prod ν))
    (hprod2 : Integrable (fun p : X × Y => |K p.1 p.2| * ‖f p.2‖ ^ 2) (μ.prod ν))
    (hf2 : Integrable (fun y => ‖f y‖ ^ 2) ν) :
    Integrable (fun x => ‖∫ y, K x y • f y ∂ν‖ ^ 2) μ ∧
      (∫ x, ‖∫ y, K x y • f y ∂ν‖ ^ 2 ∂μ) ≤ C ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂ν := by
  let S : X → ℝ := fun x => ∫ y, |K x y| * ‖f y‖ ^ 2 ∂ν
  have hS : Integrable S μ := hprod2.integral_prod_left
  have hT : Integrable (fun x => ∫ y, K x y • f y ∂ν) μ := hprod.integral_prod_left
  have hpoint : (fun x => ‖∫ y, K x y • f y ∂ν‖ ^ 2) ≤ᵐ[μ] (fun x => C * S x) := by
    filter_upwards [hprod.prod_right_ae, hprod2.prod_right_ae] with x hx hx2
    exact (integral_kernel_norm_sq_le ν (K x) f (hrow x) hx hx2).trans
      (mul_le_mul_of_nonneg_right (hrowC x) (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (sq_nonneg _)))
  have hT2 : Integrable (fun x => ‖∫ y, K x y • f y ∂ν‖ ^ 2) μ :=
    (hS.const_mul C).mono_nonneg (hT.aestronglyMeasurable.norm.pow 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hpoint
  have hcol : Integrable (fun y => (∫ x, |K x y| ∂μ) * ‖f y‖ ^ 2) ν :=
    hprod2.integral_prod_right.congr (Filter.Eventually.of_forall fun y =>
      integral_mul_const (‖f y‖ ^ 2) (fun x => |K x y|))
  have hSbound : (∫ x, S x ∂μ) ≤ C * ∫ y, ‖f y‖ ^ 2 ∂ν := by
    calc
      _ = ∫ y, (∫ x, |K x y| ∂μ) * ‖f y‖ ^ 2 ∂ν := by
        rw [show (∫ x, S x ∂μ) = ∫ y, ∫ x, |K x y| * ‖f y‖ ^ 2 ∂μ ∂ν from
          integral_integral_swap hprod2]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
          integral_mul_const (‖f y‖ ^ 2) (fun x => |K x y|))
      _ ≤ ∫ y, C * ‖f y‖ ^ 2 ∂ν := integral_mono hcol (hf2.const_mul C)
        (fun y => mul_le_mul_of_nonneg_right (hcolC y) (sq_nonneg _))
      _ = _ := integral_const_mul C _
  refine ⟨hT2, ?_⟩
  calc
    _ ≤ ∫ x, C * S x ∂μ := integral_mono_ae hT2 (hS.const_mul C) hpoint
    _ = C * ∫ x, S x ∂μ := integral_const_mul C _
    _ ≤ C * (C * ∫ y, ‖f y‖ ^ 2 ∂ν) := mul_le_mul_of_nonneg_left hSbound hC
    _ = _ := by ring

/-- Both Schur masses of the actual Friedrichs kernel are bounded by the
same explicit translation-invariant derivative moment. -/
theorem friedrichsCommutatorKernel_schur_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (a ρ : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (K : NNReal) (haK : LipschitzWith K a) (v : E) :
    let C : ℝ := ∫ z, K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖) ∂ν
    0 ≤ C ∧
      (∀ x, Integrable (fun y => |friedrichsCommutatorKernel a ρ v x y|) ν ∧
        (∫ y, |friedrichsCommutatorKernel a ρ v x y| ∂ν) ≤ C) ∧
      (∀ y, Integrable (fun x => |friedrichsCommutatorKernel a ρ v x y|) ν ∧
        (∫ x, |friedrichsCommutatorKernel a ρ v x y| ∂ν) ≤ C) := by
  let G : E → ℝ := fun z => K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖)
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hda : Continuous (fun z => fderiv ℝ a z v) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGcont : Continuous G := continuous_const.mul
    ((continuous_norm.mul hdρ.norm).add (continuous_const.mul hρ.continuous.norm))
  have hGc : HasCompactSupport G := by
    apply hcρ.mono'
    intro z hz
    by_contra hzt
    have hzero := image_eq_zero_of_notMem_tsupport hzt
    have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hzt
    exact hz (by simp only [G, hzero, hd0, ContinuousLinearMap.zero_apply, norm_zero, mul_zero, add_zero])
  have hGi : Integrable G ν := hGcont.integrable_of_hasCompactSupport hGc
  have hG0 (z : E) : 0 ≤ G z := by dsimp only [G]; positivity
  have hker : Continuous (fun p : E × E => friedrichsCommutatorKernel a ρ v p.1 p.2) :=
    ((hdρ.comp (continuous_fst.sub continuous_snd)).mul
      ((ha.continuous.comp continuous_fst).sub (ha.continuous.comp continuous_snd))).add
      ((hρ.continuous.comp (continuous_fst.sub continuous_snd)).mul (hda.comp continuous_snd))
  have hbound (x y : E) : |friedrichsCommutatorKernel a ρ v x y| ≤ G (x - y) := by
    simpa only [G, Real.norm_eq_abs] using friedrichsCommutatorKernel_norm_le a ρ K haK v x y
  refine ⟨integral_nonneg hG0, ?_, ?_⟩
  · intro x
    have htrans : Integrable (fun y => G (x - y)) ν := hGi.comp_sub_left x
    have hi : Integrable (fun y => |friedrichsCommutatorKernel a ρ v x y|) ν :=
      htrans.mono_nonneg
        (hker.comp (continuous_const.prodMk continuous_id)).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => abs_nonneg _) (Filter.Eventually.of_forall (hbound x))
    refine ⟨hi, ?_⟩
    have hh := integral_mono hi htrans (hbound x)
    simpa only [integral_sub_left_eq_self G ν x] using hh
  · intro y
    have htrans : Integrable (fun x => G (x - y)) ν := hGi.comp_sub_right y
    have hi : Integrable (fun x => |friedrichsCommutatorKernel a ρ v x y|) ν :=
      htrans.mono_nonneg
        (hker.comp (continuous_id.prodMk continuous_const)).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => abs_nonneg _) (Filter.Eventually.of_forall fun x => hbound x y)
    refine ⟨hi, ?_⟩
    have hh := integral_mono hi htrans (fun x => hbound x y)
    simpa only [integral_sub_right_eq_self G y] using hh

/-- The actual first-order Friedrichs kernel has the stated L² bound on
every L¹∩L² input, including the rough compact sections needed for localization.
No separate kernel integrability or Schur-mass assumptions are used. -/
theorem friedrichs_commutator_L2_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (a ρ : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (K : NNReal) (haK : LipschitzWith K a) (v : E)
    (f : E → F) (hf : Integrable f ν) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) ν) :
    let C : ℝ := ∫ z, K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖) ∂ν
    Integrable (fun x => ‖∫ y, friedrichsCommutatorKernel a ρ v x y • f y ∂ν‖ ^ 2) ν ∧
      (∫ x, ‖∫ y, friedrichsCommutatorKernel a ρ v x y • f y ∂ν‖ ^ 2 ∂ν) ≤
        C ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂ν := by
  let G : E → ℝ := fun z => K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖)
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hda : Continuous (fun z => fderiv ℝ a z v) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGc : HasCompactSupport G := by
    apply hcρ.mono'
    intro z hz
    by_contra hzt
    have hzero := image_eq_zero_of_notMem_tsupport hzt
    have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hzt
    exact hz (by simp only [G, hzero, hd0, ContinuousLinearMap.zero_apply, norm_zero, mul_zero, add_zero])
  have hGi : Integrable G ν :=
    (continuous_const.mul ((continuous_norm.mul hdρ.norm).add
      (continuous_const.mul hρ.continuous.norm))).integrable_of_hasCompactSupport hGc
  have hker : Continuous (fun p : E × E => friedrichsCommutatorKernel a ρ v p.1 p.2) :=
    ((hdρ.comp (continuous_fst.sub continuous_snd)).mul
      ((ha.continuous.comp continuous_fst).sub (ha.continuous.comp continuous_snd))).add
      ((hρ.continuous.comp (continuous_fst.sub continuous_snd)).mul (hda.comp continuous_snd))
  have hb (p : E × E) : ‖friedrichsCommutatorKernel a ρ v p.1 p.2‖ ≤ G (p.1 - p.2) :=
    friedrichsCommutatorKernel_norm_le a ρ K haK v p.1 p.2
  have hmajor : Integrable (fun p : E × E => ‖f p.2‖ * G (p.1 - p.2)) (ν.prod ν) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hGi
  have hprod : Integrable (fun p : E × E => friedrichsCommutatorKernel a ρ v p.1 p.2 • f p.2)
      (ν.prod ν) := by
    apply hmajor.mono' (hker.aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_snd)
    exact Filter.Eventually.of_forall fun p => by
      change ‖friedrichsCommutatorKernel a ρ v p.1 p.2 • f p.2‖ ≤ ‖f p.2‖ * G (p.1 - p.2)
      rw [norm_smul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right (hb p) (norm_nonneg (f p.2))
  have hmajor2 : Integrable (fun p : E × E => ‖f p.2‖ ^ 2 * G (p.1 - p.2)) (ν.prod ν) := by
    simpa only [ContinuousLinearMap.mul_apply'] using
      hf2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hGi
  have hprod2 : Integrable (fun p : E × E => |friedrichsCommutatorKernel a ρ v p.1 p.2| * ‖f p.2‖ ^ 2)
      (ν.prod ν) := by
    apply hmajor2.mono_nonneg
      (hker.abs.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_snd.norm.pow 2))
      (Filter.Eventually.of_forall fun p => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    exact Filter.Eventually.of_forall fun p => by
      change |friedrichsCommutatorKernel a ρ v p.1 p.2| * ‖f p.2‖ ^ 2 ≤ ‖f p.2‖ ^ 2 * G (p.1 - p.2)
      have hh := mul_le_mul_of_nonneg_right (hb p) (sq_nonneg ‖f p.2‖)
      simpa only [Real.norm_eq_abs, mul_comm] using hh
  obtain ⟨hC, hrow, hcol⟩ := friedrichsCommutatorKernel_schur_bounds ν a ρ ha hρ hcρ K haK v
  exact friedrichs_schur_integral_L2_bound ν ν (friedrichsCommutatorKernel a ρ v) f _ hC
    (fun x => (hrow x).1) (fun x => (hrow x).2) (fun y => (hcol y).2) hprod hprod2 hf2

/-- Ordinary dimension-normalized dilation of a real mollifier. -/
def rescaledFriedrichsMollifier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : E → ℝ) (ε : ℝ) (z : E) : ℝ :=
  (ε ^ finrank ℝ E)⁻¹ * ρ (ε⁻¹ • z)

theorem rescaledFriedrichsMollifier_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → ℝ) (ε : ℝ)
    (hρ : ContDiff ℝ 1 ρ) : ContDiff ℝ 1 (rescaledFriedrichsMollifier ρ ε) := by
  have hs : ContDiff ℝ 1 (fun z : E => ε⁻¹ • z) := contDiff_const.smul contDiff_id
  change ContDiff ℝ 1 (fun z : E => (ε ^ finrank ℝ E)⁻¹ * ρ (ε⁻¹ • z))
  exact contDiff_const.mul (hρ.comp hs)

theorem rescaledFriedrichsMollifier_compact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → ℝ) {ε : ℝ}
    (hε : ε ≠ 0) (hcρ : HasCompactSupport ρ) :
    HasCompactSupport (rescaledFriedrichsMollifier ρ ε) := by
  have hc : HasCompactSupport (fun z : E => ρ (ε⁻¹ • z)) := by
    simpa [Function.comp_def, Homeomorph.smul, Units.smul_def] using
      hcρ.comp_homeomorph (Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero hε)))
  exact hc.mul_left

theorem rescaledFriedrichsMollifier_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → ℝ) (ε : ℝ)
    (hρ : ContDiff ℝ 1 ρ) (z v : E) :
    fderiv ℝ (rescaledFriedrichsMollifier ρ ε) z v =
      (ε ^ finrank ℝ E)⁻¹ * ε⁻¹ * fderiv ℝ ρ (ε⁻¹ • z) v := by
  change fderiv ℝ (fun y => (ε ^ finrank ℝ E)⁻¹ * ρ (ε⁻¹ • y)) z v = _
  have hd := (((hρ.differentiable one_ne_zero (ε⁻¹ • z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_smul ε⁻¹)).const_mul ((ε ^ finrank ℝ E)⁻¹)).fderiv
  simpa only [rescaledFriedrichsMollifier, Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, mul_assoc]
    using DFunLike.congr_fun hd v

/-- The exact derivative moment controlling the Schur bound is unchanged
under positive mollifier dilation. Thus its operator bound is uniform in scale. -/
theorem rescaledFriedrichsMollifier_schur_mass {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) {ε : ℝ} (hε : 0 < ε) (K : NNReal) (v : E) :
    (∫ z, K * (‖z‖ * ‖fderiv ℝ (rescaledFriedrichsMollifier ρ ε) z v‖ +
      ‖v‖ * ‖rescaledFriedrichsMollifier ρ ε z‖) ∂ν) =
      ∫ z, K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖) ∂ν := by
  let G : E → ℝ := fun z => K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖)
  let c : ℝ := (ε ^ finrank ℝ E)⁻¹
  have hc : 0 < c := inv_pos.mpr (pow_pos hε _)
  have hpoint (z : E) :
      K * (‖z‖ * ‖fderiv ℝ (rescaledFriedrichsMollifier ρ ε) z v‖ +
        ‖v‖ * ‖rescaledFriedrichsMollifier ρ ε z‖) = c * G (ε⁻¹ • z) := by
    rw [rescaledFriedrichsMollifier_fderiv ρ ε hρ z v]
    simp only [rescaledFriedrichsMollifier, G, c, norm_mul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hε.le), Real.norm_of_nonneg hc.le]
    ring
  calc
    _ = ∫ z, c * G (ε⁻¹ • z) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = c * (ε ^ finrank ℝ E * ∫ z, G z ∂ν) := by
      rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg ν G hε.le, smul_eq_mul]
    _ = _ := by
      dsimp only [c]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]

/-- A single explicit constant bounds all positive-scale first-order
Friedrichs commutators on the localized L¹∩L² domain. -/
theorem friedrichs_commutator_uniform_L2_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (a ρ : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (K : NNReal) (haK : LipschitzWith K a) (v : E)
    (f : E → F) (hf : Integrable f ν) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) ν) :
    let C : ℝ := ∫ z, K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖) ∂ν
    0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      Integrable (fun x => ‖∫ y, friedrichsCommutatorKernel a (rescaledFriedrichsMollifier ρ ε) v x y • f y ∂ν‖ ^ 2) ν ∧
      (∫ x, ‖∫ y, friedrichsCommutatorKernel a (rescaledFriedrichsMollifier ρ ε) v x y • f y ∂ν‖ ^ 2 ∂ν) ≤
        C ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂ν := by
  refine ⟨integral_nonneg (fun z => by positivity), ?_⟩
  intro ε hε
  have h := friedrichs_commutator_L2_bound ν a (rescaledFriedrichsMollifier ρ ε) ha
    (rescaledFriedrichsMollifier_contDiff ρ ε hρ) (rescaledFriedrichsMollifier_compact ρ hε.ne' hcρ)
    K haK v f hf hf2
  simpa only [rescaledFriedrichsMollifier_schur_mass ν ρ hρ hε K v] using h

/-- Positive dilation preserves the mollifier mass for the original Haar
measure, with its real dimension normalization. -/
theorem rescaledFriedrichsMollifier_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    (ρ : E → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ z, rescaledFriedrichsMollifier ρ ε z ∂ν) = ∫ z, ρ z ∂ν := by
  change (∫ z, (ε ^ finrank ℝ E)⁻¹ * ρ (ε⁻¹ • z) ∂ν) = _
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg ν ρ hε.le,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]

/-- The actual supports of compact mollifier dilations shrink to zero. -/
theorem rescaledFriedrichsMollifier_support_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → ℝ)
    (hcρ : HasCompactSupport ρ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => Function.support (rescaledFriedrichsMollifier ρ (ε j))) atTop
      (𝓝 (0 : E)).smallSets := by
  obtain ⟨R, hR0, hR⟩ := hcρ.isBounded.exists_pos_norm_le
  rw [tendsto_smallSets_iff]
  intro s hs
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  have hlim : Tendsto (fun j => ε j * R) atTop (𝓝 0) := by simpa using ht.mul_const R
  filter_upwards [hlim.eventually (isOpen_Iio.mem_nhds hδ)] with j hj
  intro z hz
  have hzρ : ρ ((ε j)⁻¹ • z) ≠ 0 := by
    intro hzero
    exact hz (by simp only [rescaledFriedrichsMollifier, hzero, mul_zero])
  have hnorm : ‖z‖ ≤ ε j * R := by
    calc
      ‖z‖ = ‖ε j • ((ε j)⁻¹ • z)‖ := by
        rw [smul_smul, mul_inv_cancel₀ (hε j).ne', one_smul]
      _ = ε j * ‖(ε j)⁻¹ • z‖ := by rw [norm_smul, Real.norm_of_nonneg (hε j).le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hR _ (subset_closure hzρ)) (hε j).le
  apply hball
  exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hnorm.trans_lt hj)

open scoped Convolution in
/-- A genuine nonnegative normalized compact mollifier is a pointwise
approximate identity on every continuous Bochner field. -/
theorem rescaledFriedrichsMollifier_convolution_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (ρ : E → ℝ) (hcρ : HasCompactSupport ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρ1 : (∫ z, ρ z ∂ν) = 1) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (ht : Tendsto ε atTop (𝓝 0)) (f : E → F) (hf : Continuous f) (x : E) :
    Tendsto (fun j => (rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x)
      atTop (𝓝 (f x)) := by
  have hn (j : ℕ) (z : E) : 0 ≤ rescaledFriedrichsMollifier ρ (ε j) z := by
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hε j).le _)) (hρ0 _)
  have hm (j : ℕ) : (∫ z, rescaledFriedrichsMollifier ρ (ε j) z ∂ν) = 1 := by
    rw [rescaledFriedrichsMollifier_integral ν ρ (hε j), hρ1]
  exact MeasureTheory.convolution_tendsto_right
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hm)
    (rescaledFriedrichsMollifier_support_tendsto ρ hcρ ε hε ht)
    (Filter.Eventually.of_forall fun _ => hf.aestronglyMeasurable)
    ((hf.tendsto x).comp tendsto_snd) tendsto_const_nhds

open scoped Convolution Pointwise in
/-- The normalized mollifiers converge strongly in the actual L² integral
on compact continuous fields. The common compact dominating set is constructed
from the original supports and the scale bound. -/
theorem rescaledFriedrichsMollifier_convolution_L2_tendsto {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (f : E → F) (hf : Continuous f) (hcf : HasCompactSupport f) :
    Tendsto (fun j => ∫ x,
      ‖(rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x - f x‖ ^ 2 ∂ν)
      atTop (𝓝 0) := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let T : ℕ → E → F := fun j => φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f
  have hφ (j : ℕ) : ContDiff ℝ 1 (φ j) := rescaledFriedrichsMollifier_contDiff ρ (ε j) hρ
  have hcφ (j : ℕ) : HasCompactSupport (φ j) := rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ
  have hφ0 (j : ℕ) (z : E) : 0 ≤ φ j z :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (hε j).le _)) (hρ0 _)
  have hφ1 (j : ℕ) : (∫ z, φ j z ∂ν) = 1 := by
    change (∫ z, rescaledFriedrichsMollifier ρ (ε j) z ∂ν) = 1
    rw [rescaledFriedrichsMollifier_integral ν ρ (hε j), hρ1]
  have hfint : Integrable f ν := hf.integrable_of_hasCompactSupport hcf
  have hT (j : ℕ) : Continuous (T j) :=
    (hcφ j).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hφ j).continuous hfint.locallyIntegrable
  obtain ⟨R, hR0, hR⟩ := hcρ.isBounded.exists_pos_norm_le
  have hsφ (j : ℕ) : Function.support (φ j) ⊆ Metric.closedBall (0 : E) R := by
    intro z hz
    have hzρ : ρ ((ε j)⁻¹ • z) ≠ 0 := by
      intro hzero
      exact hz (by simp only [φ, rescaledFriedrichsMollifier, hzero, mul_zero])
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    calc
      ‖z‖ = ‖ε j • ((ε j)⁻¹ • z)‖ := by
        rw [smul_smul, mul_inv_cancel₀ (hε j).ne', one_smul]
      _ = ε j * ‖(ε j)⁻¹ • z‖ := by rw [norm_smul, Real.norm_of_nonneg (hε j).le]
      _ ≤ ε j * R := mul_le_mul_of_nonneg_left (hR _ (subset_closure hzρ)) (hε j).le
      _ ≤ R := mul_le_of_le_one_left hR0.le (hε1 j)
  let S : Set E := tsupport f + Metric.closedBall (0 : E) R
  have hcS : IsCompact S := (show IsCompact (tsupport f) from hcf).add (isCompact_closedBall (0 : E) R)
  have hTS (j : ℕ) : Function.support (T j) ⊆ S :=
    (MeasureTheory.support_convolution_subset_swap (f := φ j) (g := f) (μ := ν)
      (ContinuousLinearMap.lsmul ℝ ℝ)).trans (Set.add_subset_add subset_closure (hsφ j))
  have hfS : Function.support f ⊆ S := by
    intro x hx
    exact Set.mem_add.mpr ⟨x, subset_closure hx, 0,
      Metric.mem_closedBall.mpr (by simpa only [dist_self] using hR0.le), by simp⟩
  obtain ⟨M, hM⟩ := hcf.exists_bound_of_continuous hf
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hnormT (j : ℕ) (x : E) : ‖T j x‖ ≤ M := by
    have hb : Function.support (φ j) ⊆ Metric.ball (0 : E) (R + 1) :=
      (hsφ j).trans (Metric.closedBall_subset_ball (by linarith))
    have hd := MeasureTheory.dist_convolution_le (μ := ν) (g := f) (x₀ := x) (z₀ := 0)
      hM0 hb (hφ0 j) (hφ1 j) hf.aestronglyMeasurable
      (fun y _ => by simpa only [dist_zero_right] using hM y)
    simpa only [T, dist_zero_right] using hd
  let B : E → ℝ := S.indicator (fun _ => (2 * M) ^ 2)
  have hBi : Integrable B ν :=
    (integrable_indicator_iff hcS.measurableSet).mpr (integrableOn_const hcS.measure_lt_top.ne)
  have hB (j : ℕ) : (fun x => ‖‖T j x - f x‖ ^ 2‖) ≤ᵐ[ν] B := by
    exact Filter.Eventually.of_forall fun x => by
      change ‖‖T j x - f x‖ ^ 2‖ ≤ B x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ S
      · rw [show B x = (2 * M) ^ 2 from Set.indicator_of_mem hx _]
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact (norm_sub_le _ _).trans (by linarith [hnormT j x, hM x])
      · have hTx : T j x = 0 := by by_contra hz; exact hx (hTS j hz)
        have hfx : f x = 0 := by by_contra hz; exact hx (hfS hz)
        simp only [hTx, hfx, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
          B, Set.indicator_of_notMem hx, le_refl]
  have hlim (x : E) : Tendsto (fun j => ‖T j x - f x‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hp := rescaledFriedrichsMollifier_convolution_tendsto ν ρ hcρ hρ0 hρ1 ε hε ht f hf x
    simpa only [T, φ, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      ((hp.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))).norm).pow 2
  have hdom := tendsto_integral_of_dominated_convergence
    (F := fun j x => ‖T j x - f x‖ ^ 2) (f := fun _ : E => (0 : ℝ)) B
    (fun j => (((hT j).sub hf).norm.pow 2).aestronglyMeasurable) hBi hB
    (Filter.Eventually.of_forall hlim)
  simpa only [T, φ, Pi.sub_apply, Pi.pow_apply, integral_zero] using hdom

open scoped Convolution in
/-- On a genuine compact C¹ input, the first-order commutator is exactly
the difference of two ordinary mollifier errors. -/
theorem friedrichs_commutator_eq_smooth_errors {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (a ρ u : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hu : ContDiff ℝ 1 u) (hcu : HasCompactSupport u) (v x : E) :
    (∫ y, friedrichsCommutatorKernel a ρ v x y * u y ∂ν) =
      a x * ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => fderiv ℝ u y v)) x - fderiv ℝ u x v) -
      ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => a y * fderiv ℝ u y v)) x - a x * fderiv ℝ u x v) := by
  have h1 := friedrichs_commutator_integral_identity ν (fun _ : E => (1 : ℝ)) ρ u
    contDiff_const hρ hu hcu v x
  have hc : (∫ y, fderiv ℝ ρ (x - y) v * u y ∂ν) -
      (∫ y, ρ (x - y) * fderiv ℝ u y v ∂ν) = 0 := by
    simpa only [friedrichsCommutatorKernel, sub_self, mul_zero, zero_mul,
      fderiv_const_apply, ContinuousLinearMap.zero_apply, one_mul, zero_add, integral_zero] using h1
  have h := friedrichs_commutator_integral_identity ν a ρ u ha hρ hu hcu v x
  rw [sub_eq_zero.mp hc] at h
  simp_rw [MeasureTheory.convolution_lsmul_swap, smul_eq_mul]
  rw [← h]
  ring

open scoped Convolution in
/-- The commutator converges strongly to zero on genuine compact C¹ inputs.
Both terms in the exact residual formula are controlled by the proved L²
approximate identity; the coefficient bound is used only on that residual. -/
theorem friedrichs_commutator_smooth_L2_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (a ρ u : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (K : NNReal) (haK : LipschitzWith K a) (A : ℝ) (haA : ∀ x, ‖a x‖ ≤ A)
    (hu : ContDiff ℝ 1 u) (hcu : HasCompactSupport u) (v : E)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖∫ y, friedrichsCommutatorKernel a (rescaledFriedrichsMollifier ρ (ε j)) v x y • u y ∂ν‖ ^ 2 ∂ν)
      atTop (𝓝 0) := by
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let DU : E → ℝ := fun y => fderiv ℝ u y v
  let AU : E → ℝ := fun y => a y * DU y
  let eU : ℕ → E → ℝ := fun j x => (φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] DU) x - DU x
  let eA : ℕ → E → ℝ := fun j x => (φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] AU) x - AU x
  let R : ℕ → E → ℝ := fun j x => ∫ y, friedrichsCommutatorKernel a (φ j) v x y * u y ∂ν
  have hφ (j : ℕ) : ContDiff ℝ 1 (φ j) := rescaledFriedrichsMollifier_contDiff ρ (ε j) hρ
  have hcφ (j : ℕ) : HasCompactSupport (φ j) := rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ
  have hDU : Continuous DU := (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcDU : HasCompactSupport DU := hcu.fderiv_apply ℝ v
  have hAU : Continuous AU := ha.continuous.mul hDU
  have hcAU : HasCompactSupport AU := hcDU.mul_left
  have hA0 : 0 ≤ A := (norm_nonneg (a 0)).trans (haA 0)
  have herrInt (g : E → ℝ) (hg : Continuous g) (hcg : HasCompactSupport g) (j : ℕ) :
      Integrable (fun x => ‖(φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g) x - g x‖ ^ 2) ν := by
    have hgm : MemLp g 2 ν := hg.memLp_of_hasCompactSupport hcg
    have hJc : HasCompactSupport (φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g) :=
      HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := ν) (hcφ j) hcg
    have hJ : Continuous (φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g) :=
      (hcφ j).continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hφ j).continuous
        (hg.integrable_of_hasCompactSupport hcg).locallyIntegrable
    have hJm : MemLp (φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g) 2 ν :=
      hJ.memLp_of_hasCompactSupport hJc
    simpa only [Pi.sub_apply] using
      (memLp_two_iff_integrable_sq_norm (hJm.sub hgm).aestronglyMeasurable).mp (hJm.sub hgm)
  have hlimU : Tendsto (fun j => ∫ x, ‖eU j x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto ν ρ hρ hcρ hρ0 hρ1 ε hε hε1 ht DU hDU hcDU
  have hlimA : Tendsto (fun j => ∫ x, ‖eA j x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto ν ρ hρ hcρ hρ0 hρ1 ε hε hε1 ht AU hAU hcAU
  have hum : MemLp u 2 ν := hu.continuous.memLp_of_hasCompactSupport hcu
  have hu2 : Integrable (fun y => ‖u y‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hum.aestronglyMeasurable).mp hum
  have hUnif := friedrichs_commutator_uniform_L2_bound ν a ρ ha hρ hcρ K haK v u
    (hu.continuous.integrable_of_hasCompactSupport hcu) hu2
  have hRint (j : ℕ) : Integrable (fun x => ‖R j x‖ ^ 2) ν := by
    simpa only [R, φ, smul_eq_mul] using (hUnif.2 (ε j) (hε j)).1
  have hEq (j : ℕ) (x : E) : R j x = a x * eU j x - eA j x :=
    friedrichs_commutator_eq_smooth_errors ν a (φ j) u ha (hφ j) hu hcu v x
  have hpoint (j : ℕ) (x : E) :
      ‖R j x‖ ^ 2 ≤ (2 * A ^ 2) * ‖eU j x‖ ^ 2 + 2 * ‖eA j x‖ ^ 2 := by
    rw [hEq]
    have ht0 := norm_sub_le (a x * eU j x) (eA j x)
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ht0
    have ht1 : (‖a x * eU j x‖ + ‖eA j x‖) ^ 2 ≤
        2 * ‖a x * eU j x‖ ^ 2 + 2 * ‖eA j x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a x * eU j x‖ - ‖eA j x‖)]
    have hAx : ‖a x‖ ^ 2 ≤ A ^ 2 := (sq_le_sq₀ (norm_nonneg _) hA0).mpr (haA x)
    have hmul := mul_le_mul_of_nonneg_right hAx (sq_nonneg ‖eU j x‖)
    calc
      _ ≤ 2 * (‖a x‖ ^ 2 * ‖eU j x‖ ^ 2) + 2 * ‖eA j x‖ ^ 2 := by
        simpa only [norm_mul, mul_pow] using hs.trans ht1
      _ ≤ _ := by nlinarith [hmul]
  have hbound (j : ℕ) : (∫ x, ‖R j x‖ ^ 2 ∂ν) ≤
      (2 * A ^ 2) * (∫ x, ‖eU j x‖ ^ 2 ∂ν) + 2 * ∫ x, ‖eA j x‖ ^ 2 ∂ν := by
    have hiU : Integrable (fun x => ‖eU j x‖ ^ 2) ν := herrInt DU hDU hcDU j
    have hiA : Integrable (fun x => ‖eA j x‖ ^ 2) ν := herrInt AU hAU hcAU j
    calc
      _ ≤ ∫ x, (2 * A ^ 2) * ‖eU j x‖ ^ 2 + 2 * ‖eA j x‖ ^ 2 ∂ν :=
        integral_mono (hRint j) ((hiU.const_mul (2 * A ^ 2)).add (hiA.const_mul 2)) (hpoint j)
      _ = _ := by
        rw [integral_add (hiU.const_mul (2 * A ^ 2)) (hiA.const_mul 2), integral_const_mul, integral_const_mul]
  have hupper : Tendsto (fun j => (2 * A ^ 2) * (∫ x, ‖eU j x‖ ^ 2 ∂ν) +
      2 * ∫ x, ‖eA j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hlimU.const_mul (2 * A ^ 2)).add (hlimA.const_mul 2)
  have hzero := squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg ‖R j x‖)) hbound hupper
  simpa only [R, φ, smul_eq_mul] using hzero

open scoped Convolution in
/-- A nonnegative normalized scalar convolution is an L² contraction on
the genuine Bochner L¹∩L² domain. -/
theorem probability_convolution_L2_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (ρ : E → ℝ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (f : E → F) (hf : Integrable f ν) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) ν) :
    MemLp (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) 2 ν ∧
      (∫ x, ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x‖ ^ 2 ∂ν) ≤ ∫ y, ‖f y‖ ^ 2 ∂ν := by
  have hρi : Integrable ρ ν := integrable_of_integral_eq_one hρ1
  have ha (z : E) : |ρ z| = ρ z := abs_of_nonneg (hρ0 z)
  have hrow (x : E) : Integrable (fun y => |ρ (x - y)|) ν := by
    simpa only [ha] using hρi.comp_sub_left x
  have hrowC (x : E) : (∫ y, |ρ (x - y)| ∂ν) ≤ 1 := by
    simp only [ha, integral_sub_left_eq_self ρ ν x, hρ1, le_refl]
  have hcolC (y : E) : (∫ x, |ρ (x - y)| ∂ν) ≤ 1 := by
    simp only [ha, integral_sub_right_eq_self ρ y, hρ1, le_refl]
  have hprod : Integrable (fun p : E × E => ρ (p.1 - p.2) • f p.2) (ν.prod ν) := by
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply] using
      hf.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ).flip hρi
  have hprod2 : Integrable (fun p : E × E => |ρ (p.1 - p.2)| * ‖f p.2‖ ^ 2) (ν.prod ν) := by
    simpa only [ha, ContinuousLinearMap.mul_apply', mul_comm] using
      hf2.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρi
  have h := friedrichs_schur_integral_L2_bound ν ν (fun x y => ρ (x - y)) f 1 zero_le_one
    hrow hrowC hcolC hprod hprod2 hf2
  have hs : Integrable (fun x => ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x‖ ^ 2) ν ∧
      (∫ x, ‖(ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x‖ ^ 2 ∂ν) ≤ ∫ y, ‖f y‖ ^ 2 ∂ν := by
    simpa only [← MeasureTheory.convolution_lsmul_swap, one_pow, one_mul] using h
  have hm : AEStronglyMeasurable (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) ν := by
    simpa only [← MeasureTheory.convolution_lsmul_swap] using hprod.integral_prod_left.aestronglyMeasurable
  exact ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hs.1, hs.2⟩

/-- A compactly supported genuine L² field is L¹ for a measure finite on
compact sets. This is the local domain used by the kernel estimates. -/
theorem memLp_two_compact_integrable {X F : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [NormedAddCommGroup F] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (f : X → F) (hf : MemLp f 2 ν) (hcf : HasCompactSupport f) : Integrable f ν := by
  let S : Set X := tsupport f
  have hcS : IsCompact S := hcf
  letI : IsFiniteMeasure (ν.restrict S) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hcS.measure_lt_top⟩
  have hfr : MemLp f 2 (ν.restrict S) := hf.mono_measure Measure.restrict_le_self
  have hiOn : IntegrableOn f S ν := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) hfr
  have heq : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · exact Set.indicator_of_mem hx f
    · simp only [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  have hi : Integrable (S.indicator f) ν := (integrable_indicator_iff hcS.measurableSet).mpr hiOn
  simpa only [heq] using hi

open scoped Convolution in
/-- Strong L² approximation of every rough compact Bochner field by the
genuine normalized mollifiers. Smooth density and contraction are both proved
above, and the original raw function is retained throughout. -/
theorem rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (ρ : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (f : E → F) (hf : MemLp f 2 ν) (hcf : HasCompactSupport f) :
    Tendsto (fun j => ∫ x,
      ‖(rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x - f x‖ ^ 2 ∂ν)
      atTop (𝓝 0) := by
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let J : ℕ → (E → F) → E → F := fun j g => φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g
  have hφ (j : ℕ) : ContDiff ℝ 1 (φ j) := rescaledFriedrichsMollifier_contDiff ρ (ε j) hρ
  have hcφ (j : ℕ) : HasCompactSupport (φ j) := rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ
  have hφ0 (j : ℕ) (z : E) : 0 ≤ φ j z :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg (hε j).le _)) (hρ0 _)
  have hφ1 (j : ℕ) : (∫ z, φ j z ∂ν) = 1 := by
    change (∫ z, rescaledFriedrichsMollifier ρ (ε j) z ∂ν) = 1
    rw [rescaledFriedrichsMollifier_integral ν ρ (hε j), hρ1]
  have hB (g : E → F) (hgi : Integrable g ν) (hg2 : Integrable (fun x => ‖g x‖ ^ 2) ν) (j : ℕ) :
      MemLp (J j g) 2 ν ∧ (∫ x, ‖J j g x‖ ^ 2 ∂ν) ≤ ∫ x, ‖g x‖ ^ 2 ∂ν :=
    probability_convolution_L2_bound ν (φ j) (hφ0 j) (hφ1 j) g hgi hg2
  have hfi : Integrable f ν := memLp_two_compact_integrable ν f hf hcf
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have herrInt (j : ℕ) : Integrable (fun x => ‖J j f x - f x‖ ^ 2) ν := by
    have hm := (hB f hfi hf2 j).1.sub hf
    simpa only [Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  obtain ⟨S, _, _, _, happrox⟩ := smooth_compact_L2_approx_in_open ν hf hcf isOpen_univ (Set.subset_univ _)
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let η : ℝ := min 1 (δ / 12)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hδ (by norm_num))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : η ≤ δ / 12 := min_le_right _ _
  obtain ⟨P, hP, hcP, _, herr⟩ := happrox η hη
  have hPm : MemLp P 2 ν := hP.continuous.memLp_of_hasCompactSupport hcP
  have hPi : Integrable P ν := hP.continuous.integrable_of_hasCompactSupport hcP
  have hP2 : Integrable (fun x => ‖P x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hPm.aestronglyMeasurable).mp hPm
  let D : E → F := f - P
  have hDm : MemLp D 2 ν := hf.sub hPm
  have hDi : Integrable D ν := hfi.sub hPi
  have hD2 : Integrable (fun x => ‖D x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).mp hDm
  have hEη : (∫ x, ‖D x‖ ^ 2 ∂ν) ≤ η ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg η)).mp
    calc
      _ = (eLpNorm D 2 ν) ^ 2 := ofReal_integral_norm_sq_eq_eLpNorm_sq ν hDm
      _ ≤ (ENNReal.ofReal η) ^ 2 := pow_le_pow_left' herr 2
      _ = _ := (ENNReal.ofReal_pow hη.le 2).symm
  have hEδ : (∫ x, ‖D x‖ ^ 2 ∂ν) ≤ δ / 12 :=
    hEη.trans ((by nlinarith [hη.le, hη1] : η ^ 2 ≤ η).trans hηδ)
  have hPerr (j : ℕ) : Integrable (fun x => ‖J j P x - P x‖ ^ 2) ν := by
    have hm := (hB P hPi hP2 j).1.sub hPm
    simpa only [Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hPlim : Tendsto (fun j => ∫ x, ‖J j P x - P x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto ν ρ hρ hcρ hρ0 hρ1 ε hε hε1 ht P hP.continuous hcP
  have hconvD (j : ℕ) : ConvolutionExists (φ j) D (ContinuousLinearMap.lsmul ℝ ℝ) ν :=
    (hcφ j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hφ j).continuous hDi.locallyIntegrable
  have hconvP (j : ℕ) : ConvolutionExists (φ j) P (ContinuousLinearMap.lsmul ℝ ℝ) ν :=
    (hcφ j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hφ j).continuous hPi.locallyIntegrable
  have hlin (j : ℕ) (x : E) : J j f x = J j D x + J j P x := by
    have heq : D + P = f := sub_add_cancel f P
    simpa only [J, heq] using (hconvD j x).distrib_add (hconvP j x)
  have hdecomp (j : ℕ) (x : E) : J j f x - f x = J j D x + (J j P x - P x) - D x := by
    rw [hlin]
    change J j D x + J j P x - f x = J j D x + (J j P x - P x) - (f x - P x)
    abel
  have hpoint (j : ℕ) (x : E) : ‖J j f x - f x‖ ^ 2 ≤
      3 * ‖J j D x‖ ^ 2 + 3 * ‖J j P x - P x‖ ^ 2 + 3 * ‖D x‖ ^ 2 := by
    rw [hdecomp]
    have hn : ‖J j D x + (J j P x - P x) - D x‖ ≤
        ‖J j D x‖ + ‖J j P x - P x‖ + ‖D x‖ :=
      (norm_sub_le _ _).trans (by nlinarith [norm_add_le (J j D x) (J j P x - P x)])
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖J j D x‖ + ‖J j P x - P x‖ + ‖D x‖)).mpr hn
    have hsum : (‖J j D x‖ + ‖J j P x - P x‖ + ‖D x‖) ^ 2 ≤
        3 * ‖J j D x‖ ^ 2 + 3 * ‖J j P x - P x‖ ^ 2 + 3 * ‖D x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖J j D x‖ - ‖J j P x - P x‖),
        sq_nonneg (‖J j D x‖ - ‖D x‖), sq_nonneg (‖J j P x - P x‖ - ‖D x‖)]
    exact hs.trans hsum
  have hbound (j : ℕ) : (∫ x, ‖J j f x - f x‖ ^ 2 ∂ν) ≤
      6 * (∫ x, ‖D x‖ ^ 2 ∂ν) + 3 * ∫ x, ‖J j P x - P x‖ ^ 2 ∂ν := by
    have hiD : Integrable (fun x => ‖J j D x‖ ^ 2) ν :=
      (memLp_two_iff_integrable_sq_norm (hB D hDi hD2 j).1.aestronglyMeasurable).mp (hB D hDi hD2 j).1
    calc
      _ ≤ ∫ x, 3 * ‖J j D x‖ ^ 2 + 3 * ‖J j P x - P x‖ ^ 2 + 3 * ‖D x‖ ^ 2 ∂ν :=
        integral_mono (herrInt j) (((hiD.const_mul 3).add ((hPerr j).const_mul 3)).add (hD2.const_mul 3)) (hpoint j)
      _ = 3 * (∫ x, ‖J j D x‖ ^ 2 ∂ν) + 3 * (∫ x, ‖J j P x - P x‖ ^ 2 ∂ν) +
          3 * ∫ x, ‖D x‖ ^ 2 ∂ν := by
        have hsum := integral_add ((hiD.const_mul 3).add ((hPerr j).const_mul 3)) (hD2.const_mul 3)
        simp only [Pi.add_apply] at hsum
        rw [integral_add (hiD.const_mul 3) ((hPerr j).const_mul 3)] at hsum
        simpa only [integral_const_mul] using hsum
      _ ≤ _ := by nlinarith [(hB D hDi hD2 j).2]
  filter_upwards [hPlim.eventually (isOpen_Iio.mem_nhds (div_pos hδ (by norm_num : (0 : ℝ) < 6)))] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  change (∫ x, ‖J j f x - f x‖ ^ 2 ∂ν) < δ
  nlinarith [hbound j, hEδ]

/-- For a fixed compact C¹ kernel, the actual commutator kernel is bounded
globally in both variables. The bound is used for genuine L¹ row integrals. -/
theorem friedrichsCommutatorKernel_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a ρ : E → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (K : NNReal) (haK : LipschitzWith K a) (v : E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y, ‖friedrichsCommutatorKernel a ρ v x y‖ ≤ B := by
  let G : E → ℝ := fun z => K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖)
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hG : Continuous G := continuous_const.mul
    ((continuous_norm.mul hdρ.norm).add (continuous_const.mul hρ.continuous.norm))
  have hcG : HasCompactSupport G := by
    apply hcρ.mono'
    intro z hz
    by_contra hzt
    have hz0 := image_eq_zero_of_notMem_tsupport hzt
    have hd0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hzt
    exact hz (by simp only [G, hz0, hd0, ContinuousLinearMap.zero_apply, norm_zero, mul_zero, add_zero])
  obtain ⟨B, hB⟩ := hcG.exists_bound_of_continuous hG
  refine ⟨B, (norm_nonneg (G 0)).trans (hB 0), ?_⟩
  intro x y
  have hb : ‖friedrichsCommutatorKernel a ρ v x y‖ ≤ G (x - y) :=
    friedrichsCommutatorKernel_norm_le a ρ K haK v x y
  have hn : G (x - y) ≤ ‖G (x - y)‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (G (x - y))
  exact hb.trans (hn.trans (hB _))

/-- Every genuine L¹ input has an actual commutator integral in every row.
This supplies integral linearity before passing to the L² estimate. -/
theorem friedrichsCommutatorKernel_input_integrable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure E) (a ρ : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (K : NNReal) (haK : LipschitzWith K a) (v : E)
    (f : E → F) (hf : Integrable f ν) (x : E) :
    Integrable (fun y => friedrichsCommutatorKernel a ρ v x y • f y) ν := by
  obtain ⟨B, _, hB⟩ := friedrichsCommutatorKernel_bounded a ρ hρ hcρ K haK v
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hda : Continuous (fun z => fderiv ℝ a z v) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcoef : Continuous (fun y => friedrichsCommutatorKernel a ρ v x y) :=
    ((hdρ.comp (continuous_const.sub continuous_id)).mul (continuous_const.sub ha.continuous)).add
      ((hρ.continuous.comp (continuous_const.sub continuous_id)).mul hda)
  have hi := hf.bdd_smul B hcoef.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hB x y)
  exact hi.congr (Filter.Eventually.of_forall fun y => rfl)

/-- The genuine first-order Friedrichs commutators converge strongly to
zero for every rough compact L² scalar input. No derivative of the rough
input is evaluated: the commutator is the verified integral kernel. -/
theorem friedrichs_commutator_L2_tendsto_of_memLp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (a ρ : E → ℝ) (ha : ContDiff ℝ 1 a) (hρ : ContDiff ℝ 1 ρ)
    (hcρ : HasCompactSupport ρ) (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (K : NNReal) (haK : LipschitzWith K a) (A : ℝ) (haA : ∀ x, ‖a x‖ ≤ A)
    (f : E → ℝ) (hf : MemLp f 2 ν) (hcf : HasCompactSupport f) (v : E)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x,
      ‖∫ y, friedrichsCommutatorKernel a (rescaledFriedrichsMollifier ρ (ε j)) v x y • f y ∂ν‖ ^ 2 ∂ν)
      atTop (𝓝 0) := by
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let R : ℕ → (E → ℝ) → E → ℝ := fun j g x => ∫ y, friedrichsCommutatorKernel a (φ j) v x y * g y ∂ν
  let C : ℝ := ∫ z, K * (‖z‖ * ‖fderiv ℝ ρ z v‖ + ‖v‖ * ‖ρ z‖) ∂ν
  have hφ (j : ℕ) : ContDiff ℝ 1 (φ j) := rescaledFriedrichsMollifier_contDiff ρ (ε j) hρ
  have hcφ (j : ℕ) : HasCompactSupport (φ j) := rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ
  have hU (g : E → ℝ) (hgi : Integrable g ν) (hg2 : Integrable (fun x => ‖g x‖ ^ 2) ν) (j : ℕ) :
      Integrable (fun x => ‖R j g x‖ ^ 2) ν ∧
      (∫ x, ‖R j g x‖ ^ 2 ∂ν) ≤ C ^ 2 * ∫ x, ‖g x‖ ^ 2 ∂ν := by
    have h := friedrichs_commutator_uniform_L2_bound ν a ρ ha hρ hcρ K haK v g hgi hg2
    simpa only [R, φ, C, smul_eq_mul] using h.2 (ε j) (hε j)
  have hRow (j : ℕ) (g : E → ℝ) (hgi : Integrable g ν) (x : E) :
      Integrable (fun y => friedrichsCommutatorKernel a (φ j) v x y * g y) ν := by
    simpa only [smul_eq_mul] using friedrichsCommutatorKernel_input_integrable ν a (φ j) ha
      (hφ j) (hcφ j) K haK v g hgi x
  have hfi : Integrable f ν := memLp_two_compact_integrable ν f hf hcf
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  obtain ⟨S, _, _, _, happrox⟩ := smooth_compact_L2_approx_in_open ν hf hcf isOpen_univ (Set.subset_univ _)
  suffices hlim : Tendsto (fun j => ∫ x, ‖R j f x‖ ^ 2 ∂ν) atTop (𝓝 0) by
    simpa only [R, φ, smul_eq_mul] using hlim
  rw [Metric.tendsto_nhds]
  intro δ hδ
  let den : ℝ := 8 * (C ^ 2 + 1)
  have hden : 0 < den := by dsimp only [den]; positivity
  let η : ℝ := min 1 (δ / den)
  have hη : 0 < η := lt_min zero_lt_one (div_pos hδ hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : η ≤ δ / den := min_le_right _ _
  obtain ⟨P, hP, hcP, _, herr⟩ := happrox η hη
  have hPm : MemLp P 2 ν := hP.continuous.memLp_of_hasCompactSupport hcP
  have hPi : Integrable P ν := hP.continuous.integrable_of_hasCompactSupport hcP
  have hP2 : Integrable (fun x => ‖P x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hPm.aestronglyMeasurable).mp hPm
  let D : E → ℝ := f - P
  have hDm : MemLp D 2 ν := hf.sub hPm
  have hDi : Integrable D ν := hfi.sub hPi
  have hD2 : Integrable (fun x => ‖D x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hDm.aestronglyMeasurable).mp hDm
  have hEη : (∫ x, ‖D x‖ ^ 2 ∂ν) ≤ η ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (sq_nonneg η)).mp
    calc
      _ = (eLpNorm D 2 ν) ^ 2 := ofReal_integral_norm_sq_eq_eLpNorm_sq ν hDm
      _ ≤ (ENNReal.ofReal η) ^ 2 := pow_le_pow_left' herr 2
      _ = _ := (ENNReal.ofReal_pow hη.le 2).symm
  have hEδ : (∫ x, ‖D x‖ ^ 2 ∂ν) ≤ δ / den :=
    hEη.trans ((by nlinarith [hη.le, hη1] : η ^ 2 ≤ η).trans hηδ)
  have hSmall : 2 * C ^ 2 * (∫ x, ‖D x‖ ^ 2 ∂ν) ≤ δ / 4 := by
    have hm := (le_div_iff₀ hden).mp hEδ
    dsimp only [den] at hm
    have hE0 : 0 ≤ ∫ x, ‖D x‖ ^ 2 ∂ν := integral_nonneg (fun x => sq_nonneg _)
    nlinarith [hE0]
  have hPlim : Tendsto (fun j => ∫ x, ‖R j P x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [R, φ, smul_eq_mul] using friedrichs_commutator_smooth_L2_tendsto ν a ρ P ha hρ
      hcρ hρ0 hρ1 K haK A haA (hP.of_le (by simp)) hcP v ε hε hε1 ht
  have hlin (j : ℕ) (x : E) : R j f x = R j D x + R j P x := by
    calc
      _ = ∫ y, friedrichsCommutatorKernel a (φ j) v x y * D y +
          friedrichsCommutatorKernel a (φ j) v x y * P y ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by dsimp only [D, Pi.sub_apply]; ring
      _ = _ := integral_add (hRow j D hDi x) (hRow j P hPi x)
  have hpoint (j : ℕ) (x : E) : ‖R j f x‖ ^ 2 ≤ 2 * ‖R j D x‖ ^ 2 + 2 * ‖R j P x‖ ^ 2 := by
    rw [hlin]
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_add_le (R j D x) (R j P x))
    have ht0 : (‖R j D x‖ + ‖R j P x‖) ^ 2 ≤ 2 * ‖R j D x‖ ^ 2 + 2 * ‖R j P x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖R j D x‖ - ‖R j P x‖)]
    exact hs.trans ht0
  have hbound (j : ℕ) : (∫ x, ‖R j f x‖ ^ 2 ∂ν) ≤
      2 * C ^ 2 * (∫ x, ‖D x‖ ^ 2 ∂ν) + 2 * ∫ x, ‖R j P x‖ ^ 2 ∂ν := by
    calc
      _ ≤ ∫ x, 2 * ‖R j D x‖ ^ 2 + 2 * ‖R j P x‖ ^ 2 ∂ν :=
        integral_mono (hU f hfi hf2 j).1
          (((hU D hDi hD2 j).1.const_mul 2).add ((hU P hPi hP2 j).1.const_mul 2)) (hpoint j)
      _ = 2 * (∫ x, ‖R j D x‖ ^ 2 ∂ν) + 2 * ∫ x, ‖R j P x‖ ^ 2 ∂ν := by
        rw [integral_add ((hU D hDi hD2 j).1.const_mul 2) ((hU P hPi hP2 j).1.const_mul 2),
          integral_const_mul, integral_const_mul]
      _ ≤ _ := by nlinarith [(hU D hDi hD2 j).2]
  filter_upwards [hPlim.eventually (isOpen_Iio.mem_nhds (div_pos hδ (by norm_num : (0 : ℝ) < 4)))] with j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  nlinarith [hbound j, hSmall]

/-- Exterior multiplication by a genuine continuous covector. This is the
principal symbol of the frozen omission-formula exterior derivative. -/
def modelExteriorSymbol {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ξ : V →L[ℝ] ℝ) (P : V [⋀^Fin k]→L[ℝ] ℝ) : V [⋀^Fin (k + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight P)

theorem modelExteriorSymbol_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ξ : V →L[ℝ] ℝ) (P : V [⋀^Fin k]→L[ℝ] ℝ) (I : Fin (k + 1) → V) :
    modelExteriorSymbol ξ P I = ∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val * ξ (I r) * P (r.removeNth I) := by
  simp [modelExteriorSymbol, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousLinearMap.smulRight_apply, zsmul_eq_mul, mul_assoc]

/-- The degree-zero Cartan anticommutator, with the omitted negative degree
handled by the genuine zero-form convention. -/
theorem modelExteriorSymbol_curry_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ξ : V →L[ℝ] ℝ)
    (P : V [⋀^Fin 0]→L[ℝ] ℝ) (v : V) :
    (modelExteriorSymbol ξ P).curryLeft v = ξ v • P := by
  ext I
  simp [ContinuousAlternatingMap.curryLeft_apply_apply, modelExteriorSymbol_apply, Fin.sum_univ_succ, smul_eq_mul]

/-- Exact Cartan anticommutation of exterior multiplication and contraction.
This identifies the actual d+δ principal symbol square. -/
theorem modelExteriorSymbol_curry_add {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ξ : V →L[ℝ] ℝ)
    (P : V [⋀^Fin (k + 1)]→L[ℝ] ℝ) (v : V) :
    (modelExteriorSymbol ξ P).curryLeft v + modelExteriorSymbol ξ (P.curryLeft v) = ξ v • P := by
  apply ContinuousAlternatingMap.ext
  intro I
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, modelExteriorSymbol_apply, modelExteriorSymbol_apply,
    Fin.sum_univ_succ]
  simp only [Matrix.vecCons, Fin.val_zero, pow_zero, one_mul, Fin.cons_zero, Fin.removeNth_zero, Fin.tail_cons,
    Fin.val_succ, Fin.cons_succ]
  have hrem (r : Fin (k + 1)) :
      r.succ.removeNth (Fin.cons v I : Fin (k + 2) → V) =
        (Fin.cons v (r.removeNth I) : Fin (k + 1) → V) :=
    Fin.cons_comp_succ_succAbove v I r
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply, Matrix.vecCons, hrem]
  have hs : (∑ r : Fin (k + 1), (-1 : ℝ) ^ (r.val + 1) * ξ (I r) * P (Fin.cons v (r.removeNth I))) =
      -(∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val * ξ (I r) * P (Fin.cons v (r.removeNth I))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [pow_succ]
    ring
  rw [hs]
  ring

/-- Exterior multiplication by a fixed covector squares to zero. -/
theorem modelExteriorSymbol_sq_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (ξ : V →L[ℝ] ℝ)
    (P : V [⋀^Fin k]→L[ℝ] ℝ) : modelExteriorSymbol ξ (modelExteriorSymbol ξ P) = 0 := by
  let f : V →L[ℝ] V →L[ℝ] V [⋀^Fin k]→L[ℝ] ℝ := ξ.smulRight (ξ.smulRight P)
  have hf : ∀ x y, f x y = f y x := by
    intro x y
    ext I
    simp only [f, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    ring
  have heq : ξ.smulRight (modelExteriorSymbol ξ P) =
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ).comp f := by
    apply ContinuousLinearMap.ext
    intro x
    change ξ x • modelExteriorSymbol ξ P =
      ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ (ξ x • ξ.smulRight P)
    rw [map_smul]
    rfl
  change ContinuousAlternatingMap.alternatizeUncurryFin (ξ.smulRight (modelExteriorSymbol ξ P)) = 0
  rw [heq]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric hf

/-- Raising a covector with the exact coefficient matrix used by the form metric. -/
def modelMetricSharp (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ) : ComplexVector n :=
  ∑ a, ∑ b, (B a b * ξ (realVec a)) • realVec b

theorem modelMetricSharp_eval (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ) :
    ξ (modelMetricSharp B ξ) = ∑ a, ∑ b, B a b * ξ (realVec a) * ξ (realVec b) := by
  simp [modelMetricSharp, map_sum, map_smul, smul_eq_mul, mul_assoc]

theorem modelMetricSharp_curry_apply (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (Q : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) (I : Fin k → ComplexVector n) :
    (Q.curryLeft (modelMetricSharp B ξ)) I =
      ∑ a, ∑ b, (B a b * ξ (realVec a)) * Q (Fin.cons (realVec b) I) := by
  simp [modelMetricSharp, map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul, Matrix.vecCons]

/-- The frozen normalized coefficient metric, on actual alternating model forms. -/
def modelFormInner (B : Matrix (RIdx n) (RIdx n) ℝ)
    (P Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) : ℝ :=
  (Nat.factorial k : ℝ)⁻¹ * tensorCoefficientPairing B
    (fun I => P (fun r => realVec (I r))) (fun J => Q (fun r => realVec (J r)))

theorem modelFormInner_add_right (B : Matrix (RIdx n) (RIdx n) ℝ)
    (P Q R : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelFormInner B P (Q + R) = modelFormInner B P Q + modelFormInner B P R := by
  simp only [modelFormInner, ContinuousAlternatingMap.add_apply,
    tensorCoefficientPairing_add_right, mul_add]

theorem modelFormInner_smul_right (B : Matrix (RIdx n) (RIdx n) ℝ)
    (P Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (c : ℝ) :
    modelFormInner B P (c • Q) = c * modelFormInner B P Q := by
  simp only [modelFormInner, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    tensorCoefficientPairing_const_mul_right]
  ring

theorem modelFormInner_symm (B : Matrix (RIdx n) (RIdx n) ℝ) (hB : B.IsSymm)
    (P Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelFormInner B P Q = modelFormInner B Q P := by
  unfold modelFormInner
  rw [tensorCoefficientPairing_transpose, hB]

/-- Exterior multiplication and metric contraction are exact adjoints, including
the original paper's factorial normalization. -/
theorem modelFormInner_exterior_adjoint (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (Q : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    modelFormInner B (modelExteriorSymbol ξ P) Q =
      modelFormInner B P (Q.curryLeft (modelMetricSharp B ξ)) := by
  classical
  have hε : (fun I : Fin (k + 1) → RIdx n =>
      modelExteriorSymbol ξ P (fun r => realVec (I r))) =
      (fun I : Fin (k + 1) → RIdx n => ∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val *
        (ξ (realVec (I r)) * P (fun t => realVec (r.removeNth I t)))) := by
    funext I
    rw [modelExteriorSymbol_apply]
    apply Finset.sum_congr rfl
    intro r _
    have hremove : (r.removeNth (fun s => realVec (I s)) : Fin k → ComplexVector n) =
        (fun t => realVec (r.removeNth I t)) := by
      funext t
      rfl
    rw [hremove]
    ring
  have hcons (b : RIdx n) (J : Fin k → RIdx n) :
      (Fin.cons (realVec b) (fun s => realVec (J s)) : Fin (k + 1) → ComplexVector n) =
        (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s)) := by
    funext s
    cases s using Fin.cases <;> rfl
  have hQ : (fun J : Fin k → RIdx n =>
      (Q.curryLeft (modelMetricSharp B ξ)) (fun s => realVec (J s))) =
      (fun J : Fin k → RIdx n => ∑ a, ∑ b, (B a b * ξ (realVec a)) *
        Q (fun s => realVec (Fin.cons (α := fun _ => RIdx n) b J s))) := by
    funext J
    rw [modelMetricSharp_curry_apply]
    simp_rw [hcons]
  have hscale (a : RIdx n) (H : (Fin k → RIdx n) → ℝ) :
      tensorCoefficientPairing B (fun I => ξ (realVec a) * P (fun s => realVec (I s))) H =
        ξ (realVec a) * tensorCoefficientPairing B (fun I => P (fun s => realVec (I s))) H := by
    simp only [tensorCoefficientPairing, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    ring
  unfold modelFormInner
  rw [hε, tensorCoefficientPairing_alternating_sum B
    (fun a I => ξ (realVec a) * P (fun t => realVec (I t))) Q,
    ← mul_assoc, factorial_inv_mul_succ, hQ]
  simp_rw [hscale, tensorCoefficientPairing_fintypeSum_right,
    tensorCoefficientPairing_const_mul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The pointwise Clifford norm identity for every positive degree. -/
theorem modelFormInner_symbol_norm (B : Matrix (RIdx n) (RIdx n) ℝ) (hB : B.IsSymm)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    modelFormInner B (modelExteriorSymbol ξ P) (modelExteriorSymbol ξ P) +
      modelFormInner B (P.curryLeft (modelMetricSharp B ξ)) (P.curryLeft (modelMetricSharp B ξ)) =
      ξ (modelMetricSharp B ξ) * modelFormInner B P P := by
  calc
    _ = modelFormInner B P ((modelExteriorSymbol ξ P).curryLeft (modelMetricSharp B ξ)) +
        modelFormInner B (modelExteriorSymbol ξ (P.curryLeft (modelMetricSharp B ξ))) P := by
      rw [modelFormInner_exterior_adjoint B ξ P (modelExteriorSymbol ξ P),
        modelFormInner_exterior_adjoint B ξ (P.curryLeft (modelMetricSharp B ξ)) P]
    _ = modelFormInner B P ((modelExteriorSymbol ξ P).curryLeft (modelMetricSharp B ξ) +
        modelExteriorSymbol ξ (P.curryLeft (modelMetricSharp B ξ))) := by
      rw [modelFormInner_add_right, modelFormInner_symm B hB
        (modelExteriorSymbol ξ (P.curryLeft (modelMetricSharp B ξ))) P]
    _ = _ := by
      rw [modelExteriorSymbol_curry_add, modelFormInner_smul_right]

/-- The corresponding pointwise Clifford norm identity for scalar forms. -/
theorem modelFormInner_symbol_norm_zero (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin 0]→L[ℝ] ℝ) :
    modelFormInner B (modelExteriorSymbol ξ P) (modelExteriorSymbol ξ P) =
      ξ (modelMetricSharp B ξ) * modelFormInner B P P := by
  rw [modelFormInner_exterior_adjoint, modelExteriorSymbol_curry_zero, modelFormInner_smul_right]

/-- The model pairing is exactly the root pairing in each genuine chart. -/
theorem modelFormInner_chartForm (g : HermitianField M) (A B : RealForm M k)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    modelFormInner (realMetricFn g x z)⁻¹ (chartForm A x z) (chartForm B x z) =
      formInner g A B (chartInv x z) := by
  simpa only [modelFormInner, chartForm_apply_basis] using
    (formInner_chartInv_eq_tensorPairing g A B x hz).symm

theorem modelMetricSharp_scalarGradient (g : HermitianField M)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (fderiv ℝ (inChart x η) z)
        (modelMetricSharp (realMetricFn g x z)⁻¹ (fderiv ℝ (inChart x η) z)) =
      L18Aux.scalarGradientPair g η η (chartInv x z) := by
  rw [modelMetricSharp_eval, L18Aux.scalarGradientPair_eq_chart g hη hη x hz,
    L18Aux.chartGradientPair_eq_sum]
  rfl

/-- The true raw-form symbol energy equals the physical scalar gradient
energy times the true form norm, in every positive degree. -/
theorem actual_symbol_energy (g : HermitianField M) (A : RealForm M (k + 1))
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    let B := (realMetricFn g x z)⁻¹
    let ξ := fderiv ℝ (inChart x η) z
    let P := chartForm A x z
    modelFormInner B (modelExteriorSymbol ξ P) (modelExteriorSymbol ξ P) +
      modelFormInner B (P.curryLeft (modelMetricSharp B ξ)) (P.curryLeft (modelMetricSharp B ξ)) =
      L18Aux.scalarGradientPair g η η (chartInv x z) * formNormSq g A (chartInv x z) := by
  dsimp only
  rw [modelFormInner_symbol_norm _ (realMetricFn_inv_isSymm g x z),
    modelMetricSharp_scalarGradient g hη x hz, modelFormInner_chartForm g A A x hz]
  rfl

/-- The same true symbol energy identity in degree zero. -/
theorem actual_symbol_energy_zero (g : HermitianField M) (A : RealForm M 0)
    {η : M.Carrier → ℝ} (hη : SmoothFn η) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    let B := (realMetricFn g x z)⁻¹
    let ξ := fderiv ℝ (inChart x η) z
    let P := chartForm A x z
    modelFormInner B (modelExteriorSymbol ξ P) (modelExteriorSymbol ξ P) =
      L18Aux.scalarGradientPair g η η (chartInv x z) * formNormSq g A (chartInv x z) := by
  dsimp only
  rw [modelFormInner_symbol_norm_zero,
    modelMetricSharp_scalarGradient g hη x hz, modelFormInner_chartForm g A A x hz]
  rfl

theorem modelFormInner_zero_left (B : Matrix (RIdx n) (RIdx n) ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) : modelFormInner B 0 P = 0 := by
  simp [modelFormInner, tensorCoefficientPairing]

/-- The two contributions to each middle-degree Dirac symbol are orthogonal. -/
theorem modelFormInner_symbol_cross_zero (B : Matrix (RIdx n) (RIdx n) ℝ)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (Q : (ComplexVector n) [⋀^Fin (k + 2)]→L[ℝ] ℝ) :
    modelFormInner B (modelExteriorSymbol ξ P) (Q.curryLeft (modelMetricSharp B ξ)) = 0 := by
  rw [← modelFormInner_exterior_adjoint B ξ (modelExteriorSymbol ξ P) Q,
    modelExteriorSymbol_sq_zero, modelFormInner_zero_left]

/-- The true degreewise Dirac symbol has no cross term between its incoming
exterior and codifferential contributions. -/
theorem modelFormInner_dirac_symbol_split (B : Matrix (RIdx n) (RIdx n) ℝ) (hB : B.IsSymm)
    (ξ : ComplexVector n →L[ℝ] ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (Q : (ComplexVector n) [⋀^Fin (k + 2)]→L[ℝ] ℝ) :
    modelFormInner B (modelExteriorSymbol ξ P - Q.curryLeft (modelMetricSharp B ξ))
        (modelExteriorSymbol ξ P - Q.curryLeft (modelMetricSharp B ξ)) =
      modelFormInner B (modelExteriorSymbol ξ P) (modelExteriorSymbol ξ P) +
        modelFormInner B (Q.curryLeft (modelMetricSharp B ξ)) (Q.curryLeft (modelMetricSharp B ξ)) := by
  have hL := modelFormInner_symbol_cross_zero B ξ P Q
  have hR : modelFormInner B (Q.curryLeft (modelMetricSharp B ξ)) (modelExteriorSymbol ξ P) = 0 := by
    rw [modelFormInner_symm B hB, hL]
  unfold modelFormInner at hL hR ⊢
  simp only [ContinuousAlternatingMap.sub_apply, tensorCoefficientPairing,
    sub_mul, mul_sub, Finset.sum_sub_distrib] at hL hR ⊢
  nlinarith

/-- The model exterior symbol is exactly the multiplier error in the
frozen exteriorComponents expression. -/
theorem exteriorComponents_multiply_modelSymbol (η : ComplexVector n → ℝ)
    (A : RealForm M k) (x : M.Carrier) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z)
    (hA : ∀ I, DifferentiableAt ℝ (fun w => formComponents A x w I) z)
    (I : Fin (k + 1) → RIdx n) :
    exteriorComponents (fun w J => η w * formComponents A x w J) z I =
      η z * exteriorComponents (formComponents A x) z I +
        modelExteriorSymbol (fderiv ℝ η z) (chartForm A x z) (fun r => realVec (I r)) := by
  rw [exteriorComponents_multiply_at η (formComponents A x) z hη hA I,
    modelExteriorSymbol_apply]
  congr 1

/-- The metric contraction symbol is exactly the multiplier error in the
frozen codifferentialComponents expression. -/
theorem codifferentialComponents_multiply_modelSymbol (g : HermitianField M)
    (η : ComplexVector n → ℝ) (A : RealForm M (k + 1)) (x : M.Carrier) (z : ComplexVector n)
    (hη : DifferentiableAt ℝ η z)
    (hA : ∀ I, DifferentiableAt ℝ (fun w => formComponents A x w I) z)
    (I : Fin k → RIdx n) :
    codifferentialComponents g x (fun w J => η w * formComponents A x w J) z I =
      η z * codifferentialComponents g x (formComponents A x) z I -
        ((chartForm A x z).curryLeft
          (modelMetricSharp (realMetricFn g x z)⁻¹ (fderiv ℝ η z))) (fun r => realVec (I r)) := by
  rw [codifferentialComponents_multiply_at g x η (formComponents A x) z hη hA I,
    modelMetricSharp_curry_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hc : chartForm A x z (Fin.cons (realVec b) (fun r => realVec (I r))) =
      formComponents A x z (Fin.cons b I) := by
    change chartForm A x z (Fin.cons (realVec b) (fun r => realVec (I r))) =
      chartForm A x z (fun r => realVec (Fin.cons (α := fun _ => RIdx n) b I r))
    congr 1
    funext r
    cases r using Fin.cases <;> rfl
  rw [hc]
  rfl

open scoped Convolution in
/-- Differentiation of convolution on a genuine rough L¹ input. -/
theorem convolution_directional_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (ρ f : E → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hf : Integrable f ν) (x v : E) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x v =
      ∫ y, fderiv ℝ ρ (x - y) v * f y ∂ν := by
  have hd := hcρ.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ).flip
    hf.locallyIntegrable hρ x
  rw [MeasureTheory.convolution_flip] at hd
  rw [hd.fderiv, MeasureTheory.convolution_precompR_apply
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hf.locallyIntegrable (hcρ.fderiv ℝ)
    (hρ.continuous_fderiv one_ne_zero) x v]
  rfl

/-- The genuine distributional equation for a finite first-order system;
derivatives occur only on compact smooth tests and actual coefficients. -/
def firstOrderSystemWeakEquation {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [Fintype α] [Fintype ι] (ν : Measure E) (v : ι → E)
    (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (u : E → α → ℝ) (w : E → β → ℝ) : Prop :=
  ∀ r φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ y, φ y * w y r ∂ν) = ∑ c,
      (-(∑ i, ∫ y, (a r c i y * fderiv ℝ φ y (v i) +
        fderiv ℝ (a r c i) y (v i) * φ y) * u y c ∂ν) +
        ∫ y, φ y * (b r c y * u y c) ∂ν)

open scoped Convolution in
/-- An exact first-order graph commutator on rough inputs. The weak equation
is tested against the translated smooth kernel; no rough derivative is used. -/
theorem firstOrderSystemWeakEquation_mollifier_identity {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype α] [Fintype ι]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant]
    (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (ha : ∀ r c i, ContDiff ℝ 1 (a r c i))
    (K : β → α → ι → NNReal) (haK : ∀ r c i, LipschitzWith (K r c i) (a r c i))
    (u : E → α → ℝ) (w : E → β → ℝ) (hu : ∀ c, Integrable (fun y => u y c) ν)
    (hweak : firstOrderSystemWeakEquation ν v a b u w)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (r : β) (x : E) :
    (∑ c, ((∑ i, a r c i x * fderiv ℝ
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) x (v i)) +
        b r c x * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) x)) -
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => w y r)) x =
    (∑ c, ∑ i, ∫ y, friedrichsCommutatorKernel (a r c i) ρ (v i) x y * u y c ∂ν) +
      ∑ c, (b r c x * (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) x -
        (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => b r c y * u y c)) x) := by
  classical
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  let φ : E → ℝ := fun y => ρ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := by
    simpa [φ, Function.comp_def] using hcρ.comp_homeomorph (Homeomorph.subLeft x)
  have hdφ (y : E) (i : ι) : fderiv ℝ φ y (v i) = -fderiv ℝ ρ (x - y) (v i) := by
    have hd := ((hρ1.differentiable one_ne_zero (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)).fderiv
    simpa only [φ, Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg] using
      DFunLike.congr_fun hd (v i)
  have hbase (c : α) (i : ι) :
      Integrable (fun y => fderiv ℝ ρ (x - y) (v i) * u y c) ν := by
    have hdρ : Continuous (fun z => fderiv ℝ ρ z (v i)) :=
      (hρ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨D, hD⟩ := (hcρ.fderiv_apply ℝ (v i)).exists_bound_of_continuous hdρ
    have hc : Continuous (fun y : E => fderiv ℝ ρ (x - y) (v i)) :=
      hdρ.comp (continuous_const.sub continuous_id)
    have hi := (hu c).bdd_smul D hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hD (x - y))
    exact hi.congr (Filter.Eventually.of_forall fun y => rfl)
  have hterm (c : α) (i : ι) :
      (∫ y, (a r c i y * fderiv ℝ φ y (v i) +
        fderiv ℝ (a r c i) y (v i) * φ y) * u y c ∂ν) =
      (∫ y, friedrichsCommutatorKernel (a r c i) ρ (v i) x y * u y c ∂ν) -
        a r c i x * ∫ y, fderiv ℝ ρ (x - y) (v i) * u y c ∂ν := by
    have hR : Integrable
        (fun y => friedrichsCommutatorKernel (a r c i) ρ (v i) x y * u y c) ν := by
      simpa only [smul_eq_mul] using friedrichsCommutatorKernel_input_integrable ν
        (a r c i) ρ (ha r c i) hρ1 hcρ (K r c i) (haK r c i) (v i) (fun y => u y c) (hu c) x
    have heq : (fun y => (a r c i y * fderiv ℝ φ y (v i) +
        fderiv ℝ (a r c i) y (v i) * φ y) * u y c) =
        (fun y => friedrichsCommutatorKernel (a r c i) ρ (v i) x y * u y c -
          a r c i x * (fderiv ℝ ρ (x - y) (v i) * u y c)) := by
      funext y
      rw [hdφ]
      dsimp only [φ, friedrichsCommutatorKernel]
      ring
    rw [heq, integral_sub hR ((hbase c i).const_mul _), integral_const_mul]
  have hw := hweak r φ hφ hcφ
  simp_rw [hterm] at hw
  simp_rw [convolution_directional_derivative ν ρ _ hρ1 hcρ (hu _),
    MeasureTheory.convolution_lsmul_swap, smul_eq_mul]
  dsimp only [φ] at hw
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_sub] at hw ⊢
  linarith

/-- Smoothness of every order is preserved by the actual mollifier dilation. -/
theorem rescaledFriedrichsMollifier_contDiff_top {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : E → ℝ) (ε : ℝ)
    (hρ : ContDiff ℝ ∞ ρ) : ContDiff ℝ ∞ (rescaledFriedrichsMollifier ρ ε) := by
  change ContDiff ℝ ∞ (fun z : E => (ε ^ finrank ℝ E)⁻¹ * ρ (ε⁻¹ • z))
  exact contDiff_const.mul (hρ.comp (contDiff_const.smul contDiff_id))

open scoped Convolution in
/-- The zero-order part of the actual finite-system graph residual converges
strongly to zero on rough compact L² inputs. -/
theorem zeroth_order_commutator_L2_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (b ρ : E → ℝ) (hb : Continuous b) (B : ℝ) (hbB : ∀ x, ‖b x‖ ≤ B)
    (hρ : ContDiff ℝ 1 ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε atTop (𝓝 0)) (f : E → ℝ) (hf : MemLp f 2 ν) (hcf : HasCompactSupport f) :
    let R := fun j x => b x *
      (rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] f) x -
      (rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => b y * f y)) x
    (∀ j, MemLp (R j) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖R j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let J : ℕ → (E → ℝ) → E → ℝ := fun j g => φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g
  let bf : E → ℝ := fun y => b y * f y
  let R : ℕ → E → ℝ := fun j x => b x * J j f x - J j bf x
  let eF : ℕ → E → ℝ := fun j x => J j f x - f x
  let eB : ℕ → E → ℝ := fun j x => J j bf x - bf x
  have hB0 : 0 ≤ B := (norm_nonneg (b 0)).trans (hbB 0)
  have hmul (g : E → ℝ) (hg : MemLp g 2 ν) : MemLp (fun x => b x * g x) 2 ν := by
    apply hg.of_le_mul (c := B) (hb.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖b x * g x‖ ≤ B * ‖g x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbB x) (norm_nonneg _)
  have hbf : MemLp bf 2 ν := hmul f hf
  have hcbf : HasCompactSupport bf := hcf.mul_left
  have hJ (g : E → ℝ) (hg : MemLp g 2 ν) (hcg : HasCompactSupport g) (j : ℕ) : MemLp (J j g) 2 ν := by
    have hp0 (z : E) : 0 ≤ φ j z :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg (hε j).le _)) (hρ0 _)
    have hp1 : (∫ z, φ j z ∂ν) = 1 := by
      change (∫ z, rescaledFriedrichsMollifier ρ (ε j) z ∂ν) = 1
      rw [rescaledFriedrichsMollifier_integral ν ρ (hε j), hρ1]
    exact (probability_convolution_L2_bound ν (φ j) hp0 hp1 g
      (memLp_two_compact_integrable ν g hg hcg)
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)).1
  have hRm (j : ℕ) : MemLp (R j) 2 ν := by
    have hm := (hmul (J j f) (hJ f hf hcf j)).sub (hJ bf hbf hcbf j)
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun x => rfl) hm
  have heFi (j : ℕ) : Integrable (fun x => ‖eF j x‖ ^ 2) ν := by
    have hm := (hJ f hf hcf j).sub hf
    simpa only [eF, Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have heBi (j : ℕ) : Integrable (fun x => ‖eB j x‖ ^ 2) ν := by
    have hm := (hJ bf hbf hcbf j).sub hbf
    simpa only [eB, Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hlimF : Tendsto (fun j => ∫ x, ‖eF j x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ hρ hcρ hρ0 hρ1
      ε hε hε1 ht f hf hcf
  have hlimB : Tendsto (fun j => ∫ x, ‖eB j x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ hρ hcρ hρ0 hρ1
      ε hε hε1 ht bf hbf hcbf
  have hpoint (j : ℕ) (x : E) :
      ‖R j x‖ ^ 2 ≤ (2 * B ^ 2) * ‖eF j x‖ ^ 2 + 2 * ‖eB j x‖ ^ 2 := by
    have hEq : R j x = b x * eF j x - eB j x := by dsimp only [R, eF, eB, bf]; ring
    rw [hEq]
    have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_sub_le (b x * eF j x) (eB j x))
    have ht0 : (‖b x * eF j x‖ + ‖eB j x‖) ^ 2 ≤
        2 * ‖b x * eF j x‖ ^ 2 + 2 * ‖eB j x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖b x * eF j x‖ - ‖eB j x‖)]
    have hb2 : ‖b x‖ ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (norm_nonneg _) hB0).mpr (hbB x)
    have hm := mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖eF j x‖)
    have h := hs.trans ht0
    rw [norm_mul, mul_pow] at h
    nlinarith
  have hbound (j : ℕ) : (∫ x, ‖R j x‖ ^ 2 ∂ν) ≤
      (2 * B ^ 2) * (∫ x, ‖eF j x‖ ^ 2 ∂ν) + 2 * ∫ x, ‖eB j x‖ ^ 2 ∂ν := by
    have hRi := (memLp_two_iff_integrable_sq_norm (hRm j).aestronglyMeasurable).mp (hRm j)
    calc
      _ ≤ ∫ x, (2 * B ^ 2) * ‖eF j x‖ ^ 2 + 2 * ‖eB j x‖ ^ 2 ∂ν :=
        integral_mono hRi (((heFi j).const_mul (2 * B ^ 2)).add ((heBi j).const_mul 2)) (hpoint j)
      _ = _ := by rw [integral_add ((heFi j).const_mul (2 * B ^ 2)) ((heBi j).const_mul 2),
        integral_const_mul, integral_const_mul]
  have hupper : Tendsto (fun j => (2 * B ^ 2) * (∫ x, ‖eF j x‖ ^ 2 ∂ν) +
      2 * ∫ x, ‖eB j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hlimF.const_mul (2 * B ^ 2)).add (hlimB.const_mul 2)
  exact ⟨hRm, squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg ‖R j x‖)) hbound hupper⟩

/-- The actual coordinate expression of a finite first-order system. -/
def firstOrderSystemApply {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (u : E → α → ℝ) : E → β → ℝ :=
  fun x r => ∑ c, ((∑ i, a r c i x * fderiv ℝ (fun y => u y c) x (v i)) + b r c x * u x c)

open scoped Convolution in
/-- Friedrichs graph approximation for a genuine finite first-order system.
Every mollified input is smooth and compact, and the actual computed outputs
converge in L² to the original distributional output. -/
theorem firstOrderSystemWeakEquation_mollifier_graph_tendsto {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype α] [Fintype ι]
    (ν : Measure E) [ν.IsAddHaarMeasure] [ν.IsNegInvariant] [SigmaFinite ν]
    (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (ha : ∀ r c i, ContDiff ℝ 1 (a r c i))
    (K : β → α → ι → NNReal) (haK : ∀ r c i, LipschitzWith (K r c i) (a r c i))
    (A : β → α → ι → ℝ) (haA : ∀ r c i x, ‖a r c i x‖ ≤ A r c i)
    (hb : ∀ r c, Continuous (b r c)) (B : β → α → ℝ) (hbB : ∀ r c x, ‖b r c x‖ ≤ B r c)
    (u : E → α → ℝ) (w : E → β → ℝ)
    (hu : ∀ c, MemLp (fun y => u y c) 2 ν) (hcu : ∀ c, HasCompactSupport (fun y => u y c))
    (hw : ∀ r, MemLp (fun y => w y r) 2 ν) (hcw : ∀ r, HasCompactSupport (fun y => w y r))
    (hweak : firstOrderSystemWeakEquation ν v a b u w)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρ0 : ∀ z, 0 ≤ ρ z) (hρ1 : (∫ z, ρ z ∂ν) = 1)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1) (ht : Tendsto ε atTop (𝓝 0)) :
    let U : ℕ → E → α → ℝ := fun j x c =>
      (rescaledFriedrichsMollifier ρ (ε j) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] (fun y => u y c)) x
    (∀ j c, ContDiff ℝ ∞ (fun x => U j x c) ∧ HasCompactSupport (fun x => U j x c)) ∧
      (∀ c, Tendsto (fun j => ∫ x, ‖U j x c - u x c‖ ^ 2 ∂ν) atTop (𝓝 0)) ∧
      ∀ r, (∀ j, MemLp (fun x => firstOrderSystemApply v a b (U j) x r) 2 ν) ∧
        Tendsto (fun j => ∫ x, ‖firstOrderSystemApply v a b (U j) x r - w x r‖ ^ 2 ∂ν)
          atTop (𝓝 0) := by
  classical
  have hρc : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  let φ : ℕ → E → ℝ := fun j => rescaledFriedrichsMollifier ρ (ε j)
  let J : ℕ → (E → ℝ) → E → ℝ := fun j g => φ j ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ν] g
  let U : ℕ → E → α → ℝ := fun j x c => J j (fun y => u y c) x
  have hφ (j : ℕ) : ContDiff ℝ ∞ (φ j) := rescaledFriedrichsMollifier_contDiff_top ρ (ε j) hρ
  have hcφ (j : ℕ) : HasCompactSupport (φ j) := rescaledFriedrichsMollifier_compact ρ (hε j).ne' hcρ
  have hui (c : α) : Integrable (fun y => u y c) ν := memLp_two_compact_integrable ν _ (hu c) (hcu c)
  have hU (j : ℕ) (c : α) : ContDiff ℝ ∞ (fun x => U j x c) :=
    (hcφ j).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hφ j) (hui c).locallyIntegrable
  have hcU (j : ℕ) (c : α) : HasCompactSupport (fun x => U j x c) :=
    HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := ν) (hcφ j) (hcu c)
  have hJ (g : E → ℝ) (hg : MemLp g 2 ν) (hcg : HasCompactSupport g) (j : ℕ) : MemLp (J j g) 2 ν := by
    have hp0 (z : E) : 0 ≤ φ j z :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg (hε j).le _)) (hρ0 _)
    have hp1 : (∫ z, φ j z ∂ν) = 1 := by
      change (∫ z, rescaledFriedrichsMollifier ρ (ε j) z ∂ν) = 1
      rw [rescaledFriedrichsMollifier_integral ν ρ (hε j), hρ1]
    exact (probability_convolution_L2_bound ν (φ j) hp0 hp1 g
      (memLp_two_compact_integrable ν g hg hcg)
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)).1
  refine ⟨fun j c => ⟨hU j c, hcU j c⟩, ?_, ?_⟩
  · intro c
    exact rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ hρc hcρ hρ0 hρ1
      ε hε hε1 ht (fun y => u y c) (hu c) (hcu c)
  intro r
  let P : ℕ → E → ℝ := fun j x => firstOrderSystemApply v a b (U j) x r
  have hDU (j : ℕ) (c : α) (i : ι) :
      Continuous (fun x => fderiv ℝ (fun y => U j y c) x (v i)) :=
    ((hU j c).continuous_fderiv (by simp)).clm_apply continuous_const
  have hP (j : ℕ) : Continuous (P j) :=
    continuous_finsetSum _ fun c _ => (continuous_finsetSum _ fun i _ =>
      (ha r c i).continuous.mul (hDU j c i)).add ((hb r c).mul (hU j c).continuous)
  have hcP (j : ℕ) : HasCompactSupport (P j) := by
    have hcs (c : α) : HasCompactSupport (fun x =>
        ∑ i, a r c i x * fderiv ℝ (fun y => U j y c) x (v i)) := by
      have hh : HasCompactSupport (∑ i, (fun x : E =>
          a r c i x * fderiv ℝ (fun y => U j y c) x (v i))) :=
        HasCompactSupport.finset_sum (fun i _ => ((hcU j c).fderiv_apply ℝ (v i)).mul_left)
      convert hh using 1
      funext x
      simp only [Finset.sum_apply]
    have hh : HasCompactSupport (∑ c, (fun x : E =>
        (∑ i, a r c i x * fderiv ℝ (fun y => U j y c) x (v i)) + b r c x * U j x c)) :=
      HasCompactSupport.finset_sum (fun c _ => (hcs c).add (hcU j c).mul_left)
    convert hh using 1
    funext x
    simp only [P, firstOrderSystemApply, Finset.sum_apply]
  have hPm (j : ℕ) : MemLp (P j) 2 ν := (hP j).memLp_of_hasCompactSupport (hcP j)
  have hPi (j : ℕ) : Integrable (fun x => ‖P j x - w x r‖ ^ 2) ν := by
    have hm := (hPm j).sub (hw r)
    simpa only [Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  let R : ℕ → α → ι → E → ℝ := fun j c i x =>
    ∫ y, friedrichsCommutatorKernel (a r c i) (φ j) (v i) x y * u y c ∂ν
  let Z : ℕ → α → E → ℝ := fun j c x =>
    b r c x * J j (fun y => u y c) x - J j (fun y => b r c y * u y c) x
  let Werr : ℕ → E → ℝ := fun j x => J j (fun y => w y r) x - w x r
  have hRi (j : ℕ) (c : α) (i : ι) : Integrable (fun x => ‖R j c i x‖ ^ 2) ν := by
    have h := friedrichs_commutator_uniform_L2_bound ν (a r c i) ρ (ha r c i) hρc hcρ
      (K r c i) (haK r c i) (v i) (fun y => u y c) (hui c)
      ((memLp_two_iff_integrable_sq_norm (hu c).aestronglyMeasurable).mp (hu c))
    simpa only [R, φ, smul_eq_mul] using (h.2 (ε j) (hε j)).1
  have hRlim (c : α) (i : ι) : Tendsto (fun j => ∫ x, ‖R j c i x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [R, φ, smul_eq_mul] using friedrichs_commutator_L2_tendsto_of_memLp ν
      (a r c i) ρ (ha r c i) hρc hcρ hρ0 hρ1 (K r c i) (haK r c i) (A r c i) (haA r c i)
      (fun y => u y c) (hu c) (hcu c) (v i) ε hε hε1 ht
  have hZ (c : α) : (∀ j, MemLp (Z j c) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖Z j c x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    zeroth_order_commutator_L2_tendsto ν (b r c) ρ (hb r c) (B r c) (hbB r c)
      hρc hcρ hρ0 hρ1 ε hε hε1 ht (fun y => u y c) (hu c) (hcu c)
  have hWi (j : ℕ) : Integrable (fun x => ‖Werr j x‖ ^ 2) ν := by
    have hm := (hJ (fun y => w y r) (hw r) (hcw r) j).sub (hw r)
    simpa only [Werr, Pi.sub_apply] using (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hWlim : Tendsto (fun j => ∫ x, ‖Werr j x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    rescaledFriedrichsMollifier_convolution_L2_tendsto_of_memLp ν ρ hρc hcρ hρ0 hρ1
      ε hε hε1 ht (fun y => w y r) (hw r) (hcw r)
  let γ := (α × ι) ⊕ (α ⊕ Unit)
  let T : ℕ → E → γ → ℝ := fun j x s => match s with
    | .inl (c, i) => R j c i x
    | .inr (.inl c) => Z j c x
    | .inr (.inr _) => Werr j x
  let M : ℝ := Fintype.card γ
  have hTi (j : ℕ) (s : γ) : Integrable (fun x => ‖T j x s‖ ^ 2) ν := by
    rcases s with ⟨c, i⟩ | (c | t)
    · exact hRi j c i
    · exact (memLp_two_iff_integrable_sq_norm ((hZ c).1 j).aestronglyMeasurable).mp ((hZ c).1 j)
    · exact hWi j
  have hTlim (s : γ) : Tendsto (fun j => ∫ x, ‖T j x s‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    rcases s with ⟨c, i⟩ | (c | t)
    · exact hRlim c i
    · exact (hZ c).2
    · exact hWlim
  have hId (j : ℕ) (x : E) : P j x - w x r = ∑ s : γ, T j x s := by
    have h := firstOrderSystemWeakEquation_mollifier_identity ν v a b ha K haK u w hui hweak
      (φ j) (hφ j) (hcφ j) r x
    change P j x - J j (fun y => w y r) x = (∑ c, ∑ i, R j c i x) + ∑ c, Z j c x at h
    have hs : (∑ s : γ, T j x s) = (∑ c, ∑ i, R j c i x) + (∑ c, Z j c x) + Werr j x := by
      dsimp only [γ]
      simp [T, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc]
    rw [hs]
    dsimp only [Werr]
    linarith
  have hpoint (j : ℕ) (x : E) : ‖P j x - w x r‖ ^ 2 ≤ M * ∑ s : γ, ‖T j x s‖ ^ 2 := by
    rw [hId]
    have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun s _ => norm_nonneg (T j x s)))).mpr
      (norm_sum_le Finset.univ (fun s : γ => T j x s))
    exact hs.trans (by simpa only [M, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s : γ => ‖T j x s‖)))
  have hbound (j : ℕ) : (∫ x, ‖P j x - w x r‖ ^ 2 ∂ν) ≤ M * ∑ s : γ, ∫ x, ‖T j x s‖ ^ 2 ∂ν := by
    calc
      _ ≤ ∫ x, M * ∑ s : γ, ‖T j x s‖ ^ 2 ∂ν :=
        integral_mono (hPi j) ((integrable_finsetSum Finset.univ (fun s _ => hTi j s)).const_mul M) (hpoint j)
      _ = _ := by rw [integral_const_mul, integral_finsetSum Finset.univ (fun s _ => hTi j s)]
  have hupper : Tendsto (fun j => M * ∑ s : γ, ∫ x, ‖T j x s‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ (fun s _ => hTlim s)).const_mul M
  exact ⟨hPm, squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg ‖P j x - w x r‖)) hbound hupper⟩

local instance {n k : ℕ} : NormedAddCommGroup ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) := inferInstance
local instance {n k : ℕ} : NormedAddCommGroup (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)) := inferInstance
local instance {n k : ℕ} : NormedAddCommGroup
    (((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) × (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))) := inferInstance
local instance {n k : ℕ} : NormedSpace ℝ
    (((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) × (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))) := inferInstance
local instance {n j p : ℕ} : NormedAddCommGroup
    ((((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) × (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ))) →L[ℝ]
      ((ComplexVector n) [⋀^Fin p]→L[ℝ] ℝ)) := inferInstance
local instance {n j p : ℕ} : NormedSpace ℝ
    ((((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) × (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ))) →L[ℝ]
      ((ComplexVector n) [⋀^Fin p]→L[ℝ] ℝ)) := inferInstance

/-- Actual contraction as a continuous linear map on model alternating forms. -/
def modelContractionCLM (v : ComplexVector n) :
    ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ]
      ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousLinearMap.apply ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) v).comp
    (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := ComplexVector n) (F := ℝ) (n := k)).toContinuousLinearMap

theorem modelContractionCLM_apply (v : ComplexVector n)
    (P : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :
    modelContractionCLM v P = P.curryLeft v := rfl

/-- The frozen connection action is linear in the actual alternating fibre. -/
def modelConnectionActionCLM (C : Matrix (RIdx n) (RIdx n) ℝ) :
    ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
      ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM ℝ
    (ContinuousLinearMap.id ℝ (ComplexVector n))).flip (modelMatrixRowMap C.transpose)

theorem modelConnectionActionCLM_apply (C : Matrix (RIdx n) (RIdx n) ℝ)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelConnectionActionCLM C P = P.fderivCompContinuousLinearMap
      (ContinuousLinearMap.id ℝ (ComplexVector n)) (modelMatrixRowMap C.transpose) := rfl

/-- The covariant calculator depends continuously and linearly on its true first jet. -/
def modelCovariantJetCLM (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (a : RIdx n) :
    (((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) ×
      (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))) →L[ℝ]
      ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  ((ContinuousLinearMap.apply ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (realVec a)).comp
      (ContinuousLinearMap.snd ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
        (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)))) -
    (modelConnectionActionCLM (k := k) (christoffelMatrix g x z a)).comp
      (ContinuousLinearMap.fst ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
        (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)))

theorem modelCovariantJetCLM_apply (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (a : RIdx n) (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)) :
    modelCovariantJetCLM g x z a (P, D) = D (realVec a) - modelConnectionActionCLM (christoffelMatrix g x z a) P := rfl

/-- The actual codifferential is a first-order fibre-linear operator. -/
def modelCodifferentialJetCLM (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) ×
      (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ))) →L[ℝ]
      ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b •
    ((modelContractionCLM (k := k) (realVec b)).comp (modelCovariantJetCLM (k := k + 1) g x z a))

theorem modelCodifferentialJetCLM_apply (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (P : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    modelCodifferentialJetCLM g x z (P, D) = -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b •
      (D (realVec a) - modelConnectionActionCLM (christoffelMatrix g x z a) P).curryLeft (realVec b) := by
  simp only [modelCodifferentialJetCLM, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    modelContractionCLM_apply, modelCovariantJetCLM_apply]

theorem modelCodifferentialJetCLM_chart (g : HermitianField M) (A : RealForm M (k + 1))
    (x : M.Carrier) (z : ComplexVector n) :
    modelCodifferentialJetCLM g x z (chartForm A x z, fderiv ℝ (chartForm A x) z) =
      codifferentialChartForm g A x z := by
  simp only [modelCodifferentialJetCLM_apply, modelConnectionActionCLM_apply,
    codifferentialChartForm, covariantChartForm]

theorem modelCodifferentialJetCLM_apply_basis (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (P : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ))
    (I : Fin k → RIdx n) :
    modelCodifferentialJetCLM g x z (P, D) (fun r => realVec (I r)) =
      -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
        (D (realVec a) (fun r => realVec (Fin.cons (α := fun _ => RIdx n) b I r)) -
          tensorConnectionAction (christoffelMatrix g x z a)
            (fun J => P (fun r => realVec (J r))) (Fin.cons (α := fun _ => RIdx n) b I)) := by
  simp only [modelCodifferentialJetCLM_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hcons : Matrix.vecCons (realVec b) (fun r => realVec (I r)) =
      (fun r => realVec (Fin.cons (α := fun _ => RIdx n) b I r)) := by
    funext r
    cases r using Fin.cases <;> rfl
  rw [hcons, ContinuousAlternatingMap.sub_apply, modelConnectionActionCLM_apply,
    modelForm_connectionAction_coeff]

set_option maxHeartbeats 800000 in
/-- Every true scalar coefficient of the codifferential first jet is smooth
on the actual chart target, with the metric and connection retained. -/
theorem modelCodifferentialJetCLM_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (P : (ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)
    (D : ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    ContDiffOn ℝ ∞ (fun z => modelCodifferentialJetCLM g.form x z (P, D)) (chartTarget x) := by
  apply (modelForm_contDiffOn_iff _ _).mpr
  intro I
  have hs : ContDiffOn ℝ ∞ (fun z => -∑ a, ∑ b, (realMetricFn g.form x z)⁻¹ a b *
      (D (realVec a) (fun r => realVec (Fin.cons (α := fun _ => RIdx n) b I r)) -
        tensorConnectionAction (christoffelMatrix g.form x z a)
          (fun J => P (fun r => realVec (J r))) (Fin.cons (α := fun _ => RIdx n) b I))) (chartTarget x) := by
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro a _
    apply ContDiffOn.sum
    intro b _
    apply (L18Aux.realMetricFn_inverse_contDiffOn g x a b).mul
    apply contDiffOn_const.sub
    simp only [tensorConnectionAction, christoffelMatrix]
    apply ContDiffOn.sum
    intro r _
    apply ContDiffOn.sum
    intro c _
    exact (L18Aux.christoffel_contDiffOn g x c a
      ((Fin.cons (α := fun _ => RIdx n) b I) r)).mul contDiffOn_const
  apply hs.congr
  intro z _
  exact modelCodifferentialJetCLM_apply_basis g.form x z P D I

/-- The exterior calculator is the constant linear map on the derivative jet. -/
def modelExteriorJetCLM (n k : ℕ) :
    (((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) ×
      (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ))) →L[ℝ]
      ((ComplexVector n) [⋀^Fin (k + 1)]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexVector n) ℝ).comp
    (ContinuousLinearMap.snd ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
      (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)))

theorem modelExteriorJetCLM_chart (A : RealForm M k) (x : M.Carrier) (z : ComplexVector n) :
    modelExteriorJetCLM n k (chartForm A x z, fderiv ℝ (chartForm A x) z) =
      extDeriv (chartForm A x) z := rfl

/-- Scalar derivative coefficients obtained from a genuine fibre-linear first jet. -/
def firstJetDerivativeCoefficient {E F G α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype α] [Fintype ι]
    (e : Basis ι ℝ E) (f : Basis α ℝ F) (q : β → G →L[ℝ] ℝ)
    (J : E → (F × (E →L[ℝ] F)) →L[ℝ] G) : β → α → ι → E → ℝ :=
  fun r c i z => q r (J z (0, ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap (f c)))

def firstJetValueCoefficient {E F G α β : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Basis α ℝ F) (q : β → G →L[ℝ] ℝ)
    (J : E → (F × (E →L[ℝ] F)) →L[ℝ] G) : β → α → E → ℝ :=
  fun r c z => q r (J z (f c, 0))

/-- Every genuine linear first jet has exactly the finite scalar-system
coefficients obtained by evaluating it on basis jets. -/
theorem firstJetCLM_apply_basis {E F G α ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype α] [Fintype ι]
    (e : Basis ι ℝ E) (f : Basis α ℝ F) (q : G →L[ℝ] ℝ)
    (J : (F × (E →L[ℝ] F)) →L[ℝ] G) (P : F) (D : E →L[ℝ] F) :
    q (J (P, D)) = (∑ c, f.repr P c * q (J (f c, 0))) +
      ∑ i, ∑ c, f.repr (D (e i)) c *
        q (J (0, ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap (f c))) := by
  classical
  let L0 := q.comp (J.comp (ContinuousLinearMap.inl ℝ F (E →L[ℝ] F)))
  let L1 := q.comp (J.comp (ContinuousLinearMap.inr ℝ F (E →L[ℝ] F)))
  have hP : q (J (P, 0)) = ∑ c, f.repr P c * q (J (f c, 0)) := by
    change L0 P = _
    conv_lhs => rw [← f.sum_repr P]
    simp only [map_sum, map_smul, smul_eq_mul, L0,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hD : D = ∑ i, ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap (D (e i)) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg D (e.sum_repr v)
    simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using h.symm
  have hS : q (J (0, D)) = ∑ i, ∑ c, f.repr (D (e i)) c *
      q (J (0, ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap (f c))) := by
    change L1 D = _
    conv_lhs => rw [hD]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    let Ki := L1.comp (ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap)
    change Ki (D (e i)) = _
    conv_lhs => rw [← f.sum_repr (D (e i))]
    simp only [map_sum, map_smul, smul_eq_mul, Ki, L1,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  have hp : (P, D) = (P, 0) + (0, D) := by ext <;> simp
  rw [hp, map_add, map_add, hP, hS]

theorem firstOrderSystemApply_eq_firstJet {E F G α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype α] [Fintype ι]
    (e : Basis ι ℝ E) (f : Basis α ℝ F) (q : β → G →L[ℝ] ℝ)
    (J : E → (F × (E →L[ℝ] F)) →L[ℝ] G) (u : E → F) (z : E)
    (hu : DifferentiableAt ℝ u z) (r : β) :
    firstOrderSystemApply e (firstJetDerivativeCoefficient e f q J) (firstJetValueCoefficient f q J)
      (fun y c => f.repr (u y) c) z r = q r (J z (u z, fderiv ℝ u z)) := by
  classical
  have hd (c : α) (i : ι) :
      fderiv ℝ (fun y => f.repr (u y) c) z (e i) = f.repr (fderiv ℝ u z (e i)) c := by
    let L := (f.coord c).toContinuousLinearMap
    have h := (L.hasFDerivAt.comp z hu.hasFDerivAt).fderiv
    simpa only [L, Function.comp_def, ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using DFunLike.congr_fun h (e i)
  have h := firstJetCLM_apply_basis e f (q r) (J z) (u z) (fderiv ℝ u z)
  unfold firstOrderSystemApply firstJetDerivativeCoefficient firstJetValueCoefficient
  simp_rw [hd]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hM : (∑ i, ∑ c, q r (J z (0, ContinuousLinearMap.smulRightL ℝ E F
      (e.coord i).toContinuousLinearMap (f c))) * f.repr (fderiv ℝ u z (e i)) c) =
      ∑ i, ∑ c, f.repr (fderiv ℝ u z (e i)) c *
        q r (J z (0, ContinuousLinearMap.smulRightL ℝ E F (e.coord i).toContinuousLinearMap (f c))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro c _
    ring
  have hV : (∑ c, q r (J z (f c, 0)) * f.repr (u z) c) =
      ∑ c, f.repr (u z) c * q r (J z (f c, 0)) := by
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hM, hV]
  linarith

theorem firstJetDerivativeCoefficient_contDiffOn {E F G α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype α] [Fintype ι]
    (e : Basis ι ℝ E) (f : Basis α ℝ F) (q : β → G →L[ℝ] ℝ)
    (J : E → (F × (E →L[ℝ] F)) →L[ℝ] G) (O : Set E)
    (hJ : ∀ p, ContDiffOn ℝ ∞ (fun z => J z p) O) (r : β) (c : α) (i : ι) :
    ContDiffOn ℝ ∞ (firstJetDerivativeCoefficient e f q J r c i) O :=
  (q r).contDiff.comp_contDiffOn (hJ _)

theorem firstJetValueCoefficient_contDiffOn {E F G α β : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : Basis α ℝ F) (q : β → G →L[ℝ] ℝ)
    (J : E → (F × (E →L[ℝ] F)) →L[ℝ] G) (O : Set E)
    (hJ : ∀ p, ContDiffOn ℝ ∞ (fun z => J z p) O) (r : β) (c : α) :
    ContDiffOn ℝ ∞ (firstJetValueCoefficient f q J r c) O :=
  (q r).contDiff.comp_contDiffOn (hJ _)

instance modelRealFormFiniteDimensional (n k : ℕ) :
    FiniteDimensional ℝ ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective (modelFormCoefficientMap n k) (modelFormCoefficientMap_injective n k)

/-- The actual finite de Rham model fibre through real degree 2n. -/
abbrev modelGradedFiber (n : ℕ) := (j : Fin (2 * n + 1)) → (ComplexVector n) [⋀^Fin j.val]→L[ℝ] ℝ

local instance {n : ℕ} : NormedAddCommGroup (modelGradedFiber n) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (modelGradedFiber n) := inferInstance
local instance {n : ℕ} : FiniteDimensional ℝ (modelGradedFiber n) := inferInstance
local instance {n : ℕ} : NormedAddCommGroup (ComplexVector n →L[ℝ] modelGradedFiber n) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (ComplexVector n →L[ℝ] modelGradedFiber n) := inferInstance
local instance {n : ℕ} : NormedAddCommGroup (modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ (modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) := inferInstance
local instance {n j : ℕ} : NormedAddCommGroup
    ((modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ]
      ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ)) := inferInstance
local instance {n j : ℕ} : NormedSpace ℝ
    ((modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ]
      ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ)) := inferInstance
local instance {n : ℕ} : NormedAddCommGroup
    ((modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ] modelGradedFiber n) := inferInstance
local instance {n : ℕ} : NormedSpace ℝ
    ((modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ] modelGradedFiber n) := inferInstance

/-- Projection to an actual degree, extended by the genuine zero above 2n. -/
def modelGradedProjection (n j : ℕ) : modelGradedFiber n →L[ℝ] ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) :=
  if hj : j < 2 * n + 1 then
    (ContinuousLinearMap.proj (⟨j, hj⟩ : Fin (2 * n + 1)) :
      modelGradedFiber n →L[ℝ] ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ))
  else 0

def modelGradedJetProjection (n j : ℕ) :
    (modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ]
      (((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) ×
        (ComplexVector n →L[ℝ] ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ))) :=
  ((modelGradedProjection n j).comp
    (ContinuousLinearMap.fst ℝ (modelGradedFiber n) (ComplexVector n →L[ℝ] modelGradedFiber n))).prod
      ((ContinuousLinearMap.compL ℝ (ComplexVector n) (modelGradedFiber n)
          ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) (modelGradedProjection n j)).comp
        (ContinuousLinearMap.snd ℝ (modelGradedFiber n) (ComplexVector n →L[ℝ] modelGradedFiber n)))

theorem modelGradedJetProjection_apply (n j : ℕ) (P : modelGradedFiber n)
    (D : ComplexVector n →L[ℝ] modelGradedFiber n) :
    modelGradedJetProjection n j (P, D) =
      (modelGradedProjection n j P, (modelGradedProjection n j).comp D) := rfl

/-- The frozen full-degree Dirac expression as a real linear first-jet map. -/
def modelDiracDegreeJetCLM (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (j : ℕ) → (modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ]
      ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ)
  | 0 => (modelCodifferentialJetCLM (k := 0) g x z).comp (modelGradedJetProjection n 1)
  | j + 1 => (modelExteriorJetCLM n j).comp (modelGradedJetProjection n j) +
      (modelCodifferentialJetCLM (k := j + 1) g x z).comp (modelGradedJetProjection n (j + 2))

def modelDiracJetCLM (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) →L[ℝ] modelGradedFiber n :=
  ContinuousLinearMap.pi (fun j => modelDiracDegreeJetCLM g x z j.val)

def modelChartGradedForm (A : OperatorCandidates.GradedRealForm M) (x : M.Carrier) :
    ComplexVector n → modelGradedFiber n := fun z j => chartForm (A j.val) x z

theorem modelChartGradedForm_contDiffOn (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (modelChartGradedForm A x) (chartTarget x) :=
  contDiffOn_pi.mpr (fun j => chartForm_contDiffOn (A j.val) (hA j.val) x)

/-- Finite projection loses no genuine degree of an actual raw graded form. -/
theorem modelGradedProjection_chart (A : OperatorCandidates.GradedRealForm M)
    (x : M.Carrier) (z : ComplexVector n) (j : ℕ) :
    modelGradedProjection n j (modelChartGradedForm A x z) = chartForm (A j) x z := by
  classical
  by_cases hj : j < 2 * n + 1
  · simp only [modelGradedProjection, dif_pos hj, ContinuousLinearMap.proj_apply, modelChartGradedForm]
  · have hdeg : 2 * n < j := by omega
    rw [realForm_eq_zero_of_degree_gt (A j) hdeg]
    simp [modelGradedProjection, hj, chartForm]
    apply ContinuousAlternatingMap.ext
    intro v
    rfl

theorem modelGradedProjection_fderiv_chart (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (j : ℕ) :
    (modelGradedProjection n j).comp (fderiv ℝ (modelChartGradedForm A x) z) =
      fderiv ℝ (chartForm (A j) x) z := by
  have hd := ((modelChartGradedForm_contDiffOn A hA x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have heq : ((modelGradedProjection n j) ∘ modelChartGradedForm A x) = chartForm (A j) x :=
    funext (fun w => modelGradedProjection_chart A x w j)
  have h := ((modelGradedProjection n j).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  rw [heq] at h
  exact h.symm

/-- This is the original diracComponents, in every real form degree; the
matrix system is obtained from this actual jet map rather than postulated. -/
theorem modelDiracDegreeJetCLM_chart_coeff (g : HermitianField M)
    (A : OperatorCandidates.GradedRealForm M) (hA : ∀ j, SmoothRealForm (A j))
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) (j : ℕ)
    (I : Fin j → RIdx n) :
    modelDiracDegreeJetCLM g x z j
        (modelChartGradedForm A x z, fderiv ℝ (modelChartGradedForm A x) z) (fun r => realVec (I r)) =
      OperatorCandidates.diracComponents g x A j z I := by
  cases j with
  | zero =>
      simp only [modelDiracDegreeJetCLM, ContinuousLinearMap.comp_apply, modelGradedJetProjection_apply]
      rw [modelGradedProjection_chart, modelGradedProjection_fderiv_chart A hA x hz,
        modelCodifferentialJetCLM_chart]
      exact codifferentialChartForm_coeff g (A 1) (hA 1) x hz I
  | succ j =>
      simp only [modelDiracDegreeJetCLM, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.comp_apply, modelGradedJetProjection_apply]
      rw [modelGradedProjection_chart, modelGradedProjection_fderiv_chart A hA x hz,
        modelExteriorJetCLM_chart, modelGradedProjection_chart,
        modelGradedProjection_fderiv_chart A hA x hz, modelCodifferentialJetCLM_chart]
      simp only [ContinuousAlternatingMap.add_apply]
      change extDeriv (chartForm (A j) x) z (fun r => realVec (I r)) +
        codifferentialChartForm g (A (j + 2)) x z (fun r => realVec (I r)) = _
      rw [chartForm_extDeriv_apply (A j) (hA j) x hz I,
        codifferentialChartForm_coeff g (A (j + 2)) (hA (j + 2)) x hz I]
      rfl

theorem modelDiracJetCLM_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (p : modelGradedFiber n × (ComplexVector n →L[ℝ] modelGradedFiber n)) :
    ContDiffOn ℝ ∞ (fun z => modelDiracJetCLM g.form x z p) (chartTarget x) := by
  have hdeg (j : ℕ) : ContDiffOn ℝ ∞ (fun z => modelDiracDegreeJetCLM g.form x z j p) (chartTarget x) := by
    cases j with
    | zero =>
        simp only [modelDiracDegreeJetCLM, ContinuousLinearMap.comp_apply]
        exact modelCodifferentialJetCLM_contDiffOn g x (modelGradedJetProjection n 1 p).1
          (modelGradedJetProjection n 1 p).2
    | succ j =>
        simp only [modelDiracDegreeJetCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
        exact contDiffOn_const.add (modelCodifferentialJetCLM_contDiffOn g x
          (modelGradedJetProjection n (j + 2) p).1 (modelGradedJetProjection n (j + 2) p).2)
  exact contDiffOn_pi.mpr (fun j => hdeg j.val)

/-- The original normalized model metric as an actual real bilinear form. -/
def modelFormMetricBilin (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) (j : ℕ) :
    LinearMap.BilinForm ℝ ((ComplexVector n) [⋀^Fin j]→L[ℝ] ℝ) where
  toFun P :=
    { toFun := modelFormInner (realMetricFn g x z)⁻¹ P
      map_add' Q R := modelFormInner_add_right _ P Q R
      map_smul' c Q := by simpa only [RingHom.id_apply, smul_eq_mul] using
        modelFormInner_smul_right (realMetricFn g x z)⁻¹ P Q c }
  map_add' P Q := by
    ext R
    change modelFormInner (realMetricFn g x z)⁻¹ (P + Q) R =
      modelFormInner (realMetricFn g x z)⁻¹ P R + modelFormInner (realMetricFn g x z)⁻¹ Q R
    rw [modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) (P + Q) R,
      modelFormInner_add_right,
      modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) R P,
      modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) R Q]
  map_smul' c P := by
    ext R
    change modelFormInner (realMetricFn g x z)⁻¹ (c • P) R = c * modelFormInner (realMetricFn g x z)⁻¹ P R
    rw [modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) (c • P) R,
      modelFormInner_smul_right,
      modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) R P]

theorem modelFormMetricBilin_apply (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (P Q : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) :
    modelFormMetricBilin g x z k P Q = modelFormInner (realMetricFn g x z)⁻¹ P Q := rfl

theorem modelFormInner_self_pos (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (P : (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) (hP : P ≠ 0) :
    0 < modelFormInner (realMetricFn g x z)⁻¹ P P := by
  have hc : (fun I : Fin k → RIdx n => P (fun r => realVec (I r))) ≠ 0 := by
    intro h
    apply hP
    apply modelFormCoefficientMap_injective n k
    change modelFormCoefficientMap n k P = 0 at h
    exact h.trans (map_zero (modelFormCoefficientMap n k)).symm
  unfold modelFormInner
  rw [tensorCoefficientPairing_fin_eq_matrix]
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Nat.factorial_pos k)))
  have hT : (tensorMatrix (realMetricFn g x z)⁻¹ k).PosDef := by
    unfold tensorMatrix
    exact matrixPiProd_posDef (realMetricFn g x z)⁻¹ (realMetricFn_posDef_of_mem_target g x hz).inv k
  simpa only [star_trivial] using hT.dotProduct_mulVec_pos hc

def modelGradedMetricBilin (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    LinearMap.BilinForm ℝ (modelGradedFiber n) :=
  ∑ j : Fin (2 * n + 1), (modelFormMetricBilin g x z j.val).comp (LinearMap.proj j) (LinearMap.proj j)

theorem modelGradedMetricBilin_apply (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (P Q : modelGradedFiber n) :
    modelGradedMetricBilin g x z P Q =
      ∑ j : Fin (2 * n + 1), modelFormInner (realMetricFn g x z)⁻¹ (P j) (Q j) := by
  simp only [modelGradedMetricBilin, LinearMap.sum_apply, LinearMap.BilinForm.comp,
    LinearMap.compl₁₂_apply, LinearMap.proj_apply, modelFormMetricBilin_apply]

theorem modelGradedMetricBilin_symm (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (modelGradedMetricBilin g x z).IsSymm := by
  refine ⟨?_⟩
  intro P Q
  simp only [modelGradedMetricBilin_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact modelFormInner_symm _ (realMetricFn_inv_isSymm g x z) (P j) (Q j)

theorem modelGradedMetricBilin_posDef (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (modelGradedMetricBilin g x z).toQuadraticMap.PosDef := by
  intro P hP
  rw [LinearMap.BilinMap.toQuadraticMap_apply, modelGradedMetricBilin_apply]
  have hn (j : Fin (2 * n + 1)) : 0 ≤ modelFormInner (realMetricFn g x z)⁻¹ (P j) (P j) := by
    by_cases hj : P j = 0
    · simp only [hj, modelFormInner_zero_left, le_refl]
    · exact (modelFormInner_self_pos g x hz (P j) hj).le
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hP
  exact Finset.sum_pos' (fun j _ => hn j) ⟨j, Finset.mem_univ _, modelFormInner_self_pos g x hz (P j) hj⟩

/-- The exact fibre metric times the actual Riemannian volume density,
expressed in a fixed genuine finite basis. -/
def modelRiemannianGradedGram {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) : Matrix α α ℝ :=
  LinearMap.BilinForm.toMatrix b
    (Real.sqrt (realMetricFn g x z).det • modelGradedMetricBilin g x z)

theorem modelRiemannianGradedGram_entry {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (c d : α) :
    modelRiemannianGradedGram g x z b c d = Real.sqrt (realMetricFn g x z).det *
      ∑ j : Fin (2 * n + 1), modelFormInner (realMetricFn g x z)⁻¹ (b c j) (b d j) := by
  simp only [modelRiemannianGradedGram, LinearMap.BilinForm.toMatrix_apply,
    LinearMap.smul_apply, smul_eq_mul, modelGradedMetricBilin_apply]

theorem modelRiemannianGradedGram_posDef {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (b : Basis α ℝ (modelGradedFiber n)) : (modelRiemannianGradedGram g x z b).PosDef := by
  let B := Real.sqrt (realMetricFn g x z).det • modelGradedMetricBilin g x z
  have hS : B.IsSymm := by
    refine ⟨?_⟩
    intro P Q
    change Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z P Q =
      Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z Q P
    rw [(modelGradedMetricBilin_symm g x z).eq]
  have hP : B.toQuadraticMap.PosDef := by
    intro P hP
    change 0 < Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z P P
    exact mul_pos (Real.sqrt_pos.mpr (realMetricFn_posDef_of_mem_target g x hz).det_pos)
      (modelGradedMetricBilin_posDef g x hz P hP)
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b B hS).mp hP

theorem modelRiemannianGradedGram_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (c d : α) :
    ContDiffOn ℝ ∞ (fun z => modelRiemannianGradedGram g.form x z b c d) (chartTarget x) := by
  have hs : ContDiffOn ℝ ∞ (fun z => Real.sqrt (realMetricFn g.form x z).det *
      ∑ j : Fin (2 * n + 1), modelFormInner (realMetricFn g.form x z)⁻¹ (b c j) (b d j)) (chartTarget x) := by
    apply (L18Aux.volumeDensity_contDiffOn g x).mul
    apply ContDiffOn.sum
    intro j _
    apply contDiffOn_const.mul
    exact tensorCoefficientPairing_contDiffOn (fun z => (realMetricFn g.form x z)⁻¹)
      (fun _ I => b c j (fun r => realVec (I r))) (fun _ I => b d j (fun r => realVec (I r)))
      (chartTarget x) (L18Aux.realMetricFn_inverse_contDiffOn g x)
      (fun _ => contDiffOn_const) (fun _ => contDiffOn_const)
  apply hs.congr
  intro z _
  exact modelRiemannianGradedGram_entry g.form x z b c d

theorem modelRiemannianGradedGram_inverse_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (c d : α) :
    ContDiffOn ℝ ∞ (fun z => (modelRiemannianGradedGram g.form x z b)⁻¹ c d) (chartTarget x) :=
  L18Aux.contDiffOn_matrix_inv (modelRiemannianGradedGram_contDiffOn g x b)
    (fun z hz => ne_of_gt (modelRiemannianGradedGram_posDef g.form x hz b).det_pos) c d

theorem modelRiemannianGradedGram_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (P Q : modelGradedFiber n) :
    Real.sqrt (realMetricFn g x z).det *
        (∑ j : Fin (2 * n + 1), modelFormInner (realMetricFn g x z)⁻¹ (P j) (Q j)) =
      dotProduct (b.repr P) ((modelRiemannianGradedGram g x z b).mulVec (b.repr Q)) := by
  simpa only [modelRiemannianGradedGram, LinearMap.smul_apply, smul_eq_mul,
    modelGradedMetricBilin_apply] using
    LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b
      (Real.sqrt (realMetricFn g x z).det • modelGradedMetricBilin g x z) P Q

theorem modelRiemannianGradedGram_chart_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (b : Basis α ℝ (modelGradedFiber n)) (A B : OperatorCandidates.GradedRealForm M) :
    Real.sqrt (realMetricFn g x z).det * OperatorCandidates.gradedInner g A B (chartInv x z) =
      dotProduct (b.repr (modelChartGradedForm A x z))
        ((modelRiemannianGradedGram g x z b).mulVec (b.repr (modelChartGradedForm B x z))) := by
  rw [← modelRiemannianGradedGram_pairing g x z b (modelChartGradedForm A x z) (modelChartGradedForm B x z)]
  unfold OperatorCandidates.gradedInner
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (modelFormInner_chartForm g (A j.val) (B j.val) x hz).symm

/-- The inverse of the genuine metric-times-density Gram matrix produces
the dual test needed to read one actual distributional coefficient. -/
def modelRiemannianDualVector {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r : α) :
    ComplexVector n → modelGradedFiber n :=
  fun z => ∑ c, (modelRiemannianGradedGram g x z b)⁻¹ c r • b c

theorem modelRiemannianDualVector_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (z : ComplexVector n) :
    b.repr (modelRiemannianDualVector g x b r z) c = (modelRiemannianGradedGram g x z b)⁻¹ c r := by
  simp [modelRiemannianDualVector, map_sum, map_smul, Finsupp.single_apply]

theorem modelRiemannianDualVector_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r : α) :
    ContDiffOn ℝ ∞ (modelRiemannianDualVector g.form x b r) (chartTarget x) := by
  apply ContDiffOn.sum
  intro c _
  exact (modelRiemannianGradedGram_inverse_contDiffOn g x b c r).smul contDiffOn_const

theorem modelRiemannianDualVector_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (b : Basis α ℝ (modelGradedFiber n)) (r : α) (P : modelGradedFiber n) :
    Real.sqrt (realMetricFn g x z).det *
        (∑ j : Fin (2 * n + 1), modelFormInner (realMetricFn g x z)⁻¹
          (P j) (modelRiemannianDualVector g x b r z j)) = b.repr P r := by
  rw [modelRiemannianGradedGram_pairing g x z b P (modelRiemannianDualVector g x b r z)]
  have hcoords : (b.repr (modelRiemannianDualVector g x b r z) : α → ℝ) =
      ((modelRiemannianGradedGram g x z b)⁻¹).mulVec (Pi.single r (1 : ℝ)) := by
    funext c
    rw [modelRiemannianDualVector_coordinates]
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hcoords, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (modelRiemannianGradedGram_posDef g x hz b).det_pos)),
    Matrix.one_mulVec, dotProduct_single_one]

/-- A compact smooth scalar test yields a genuine compact smooth model
dual test, although the inverse Gram field is only needed inside the chart. -/
theorem modelRiemannianDualVector_cutoff_properties {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r : α)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    ContDiff ℝ ∞ (fun z => φ z • modelRiemannianDualVector g.form x b r z) ∧
      HasCompactSupport (fun z => φ z • modelRiemannianDualVector g.form x b r z) ∧
      tsupport (fun z => φ z • modelRiemannianDualVector g.form x b r z) ⊆ chartTarget x := by
  have hs : tsupport (fun z => φ z • modelRiemannianDualVector g.form x b r z) ⊆ tsupport φ :=
    tsupport_smul_subset_left φ _
  refine ⟨?_, hcφ.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hφO⟩
  apply contDiff_pi.mpr
  intro j
  exact (modelForm_cutoff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
    hφ hcφ hφO (fun z => modelRiemannianDualVector g.form x b r z j)
    (contDiffOn_pi.mp (modelRiemannianDualVector_contDiffOn g x b r) j)).1

/-- Reconstruct a genuine finite graded model test in the original tangent fibres. -/
def modelGradedChartPushforward (x : M.Carrier) (G : ComplexVector n → modelGradedFiber n) :
    OperatorCandidates.GradedRealForm M :=
  fun j => chartFormPushforward x (fun z => modelGradedProjection n j (G z))

theorem modelGradedChartPushforward_properties (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hGO : tsupport G ⊆ chartTarget x) :
    ∀ j, SmoothRealForm (modelGradedChartPushforward x G j) ∧
      CompactlySupportedRealForm (modelGradedChartPushforward x G j) ∧
      closure {y | modelGradedChartPushforward x G j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source := by
  intro j
  let P := fun z => modelGradedProjection n j (G z)
  have hP : ContDiff ℝ ∞ P := (modelGradedProjection n j).contDiff.comp hG
  have hs : tsupport P ⊆ tsupport G := by
    apply closure_mono
    intro z hz hzero
    exact hz (by simp only [P, hzero, map_zero])
  have hcP : HasCompactSupport P := hcG.of_isClosed_subset (isClosed_tsupport _) hs
  have hPO : tsupport P ⊆ chartTarget x := hs.trans hGO
  exact ⟨chartFormPushforward_smooth x P hP hcP hPO,
    chartFormPushforward_compactlySupported x P hP hcP hPO,
    chartFormPushforward_source_support x P hP hcP hPO⟩

theorem modelGradedChartPushforward_to_chart (x : M.Carrier) (G : ComplexVector n → modelGradedFiber n)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    modelChartGradedForm (modelGradedChartPushforward x G) x z = G z := by
  funext j
  change chartForm (chartFormPushforward x (fun w => modelGradedProjection n j.val (G w))) x z = G z j
  rw [chartFormPushforward_to_chart x _ hz]
  simp [modelGradedProjection, j.isLt]

theorem modelGradedChartPushforward_fderiv_to_chart (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    fderiv ℝ (modelChartGradedForm (modelGradedChartPushforward x G) x) z = fderiv ℝ G z := by
  have heq : modelChartGradedForm (modelGradedChartPushforward x G) x =ᶠ[𝓝 z] G := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact modelGradedChartPushforward_to_chart x G hw
  exact heq.fderiv_eq

theorem modelGradedChartPushforward_corePair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hGO : tsupport G ⊆ chartTarget x) :
    OperatorCandidates.DiracCorePair g.form μ (modelGradedChartPushforward x G)
      (diracRealForm g.form (modelGradedChartPushforward x G)) := by
  have hp := modelGradedChartPushforward_properties x G hG hcG hGO
  exact diracRealForm_corePair g μ hμ (modelGradedChartPushforward x G)
    (fun j => (hp j).1) (fun j => (hp j).2.1)

/-- Both the value and the computed operator output of every model test
reconstruct the original frozen actual Dirac core in the chart. -/
theorem modelGradedChartPushforward_dirac_to_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hGO : tsupport G ⊆ chartTarget x) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    modelChartGradedForm (diracRealForm g.form (modelGradedChartPushforward x G)) x z =
      modelDiracJetCLM g.form x z (G z, fderiv ℝ G z) := by
  let A := modelGradedChartPushforward x G
  have hA : ∀ j, SmoothRealForm (A j) := fun j => (modelGradedChartPushforward_properties x G hG hcG hGO j).1
  have hrep := diracRealForm_represents g μ hμ A hA
  funext j
  apply modelFormCoefficientMap_injective n j.val
  funext I
  change chartForm (diracRealForm g.form A j.val) x z (fun r => realVec (I r)) =
    modelDiracDegreeJetCLM g.form x z j.val (G z, fderiv ℝ G z) (fun r => realVec (I r))
  rw [chartForm_apply_basis, hrep x z hz j.val I]
  have hj := modelDiracDegreeJetCLM_chart_coeff g.form A hA x hz j.val I
  rw [modelGradedChartPushforward_to_chart x G hz, modelGradedChartPushforward_fderiv_to_chart x G hz] at hj
  exact hj.symm

theorem codifferentialRealForm_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (j : ℕ) :
    codifferentialRealForm g.form (0 : RealForm M (j + 1)) = 0 := by
  simpa only [zero_smul] using
    codifferentialRealForm_smul g μ hμ (0 : ℝ) (0 : RealForm M (j + 1)) smoothRealForm_zero

theorem gradedInner_symm (g : HermitianField M) (A B : OperatorCandidates.GradedRealForm M) :
    OperatorCandidates.gradedInner g A B = OperatorCandidates.gradedInner g B A := by
  funext y
  unfold OperatorCandidates.gradedInner
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (formInner_symm g (A j.val) (B j.val)) y

theorem gradedInner_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hB : OperatorCandidates.GradedL2 g.form μ B) :
    Integrable (OperatorCandidates.gradedInner g.form A B) μ := by
  have hi := integrable_finsetSum (Finset.univ : Finset (Fin (2 * n + 1))) (fun j _ =>
    formInner_integrable g μ (A j.val) (B j.val) (hA.2 j.val) (hB.2 j.val))
  convert hi using 1
  funext y
  simp only [OperatorCandidates.gradedInner, Finset.sum_apply]

/-- Actual full-degree Dirac Green, derived from the accepted d/δ Green
identity and the genuine degree bound at 2n. -/
theorem integral_graded_dirac_green (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (F G : OperatorCandidates.GradedRealForm M)
    (hF : ∀ j, SmoothRealForm (F j)) (hG : ∀ j, SmoothRealForm (G j))
    (hcF : ∀ j, CompactlySupportedRealForm (F j)) (hcG : ∀ j, CompactlySupportedRealForm (G j)) :
    (∫ y, OperatorCandidates.gradedInner g.form (diracRealForm g.form F) G y ∂μ) =
      ∫ y, OperatorCandidates.gradedInner g.form F (diracRealForm g.form G) y ∂μ := by
  classical
  have hdecomp (A B : OperatorCandidates.GradedRealForm M)
      (hA : ∀ j, SmoothRealForm (A j)) (hB : ∀ j, SmoothRealForm (B j))
      (hcA : ∀ j, CompactlySupportedRealForm (A j)) (hcB : ∀ j, CompactlySupportedRealForm (B j)) :
      (∫ y, OperatorCandidates.gradedInner g.form (diracRealForm g.form A) B y ∂μ) =
        ∑ j : Fin (2 * n), ((∫ y, formInner g.form (exteriorRealForm (A j.val)) (B (j.val + 1)) y ∂μ) +
          ∫ y, formInner g.form (codifferentialRealForm g.form (A (j.val + 1))) (B j.val) y ∂μ) := by
    let u (j : ℕ) := formInner g.form (exteriorRealForm (A j)) (B (j + 1))
    let v (j : ℕ) := formInner g.form (codifferentialRealForm g.form (A (j + 1))) (B j)
    have hiu (j : ℕ) : Integrable (u j) μ := formInner_integrable g μ _ _
      (exteriorRealForm_l2 g μ hμ (A j) (hA j) (hcA j))
      (smooth_compactlySupported_l2RealForm g μ hμ (B (j + 1)) (hB (j + 1)) (hcB (j + 1)))
    have hiv (j : ℕ) : Integrable (v j) μ := formInner_integrable g μ _ _
      (codifferentialRealForm_l2 g μ hμ (A (j + 1)) (hA (j + 1)) (hcA (j + 1)))
      (smooth_compactlySupported_l2RealForm g μ hμ (B j) (hB j) (hcB j))
    have hfield : OperatorCandidates.gradedInner g.form (diracRealForm g.form A) B =
        v 0 + ∑ j : Fin (2 * n), (u j.val + v (j.val + 1)) := by
      funext y
      unfold OperatorCandidates.gradedInner
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, diracRealForm, formInner_add_left,
        Pi.add_apply, Finset.sum_apply, u, v]
    have ha0 : A (2 * n + 1) = 0 := realForm_eq_zero_of_degree_gt _ (by omega)
    have hvN : (∫ y, v (2 * n) y ∂μ) = 0 := by
      dsimp only [v]
      rw [ha0, codifferentialRealForm_zero g μ hμ (2 * n), formInner_zero_left]
      simp only [Pi.zero_apply, integral_zero]
    have hshift : (∫ y, v 0 y ∂μ) + (∑ j : Fin (2 * n), ∫ y, v (j.val + 1) y ∂μ) =
        ∑ j : Fin (2 * n), ∫ y, v j.val y ∂μ := by
      have hs := Fin.sum_univ_succ (fun j : Fin (2 * n + 1) => ∫ y, v j.val y ∂μ)
      have ht := Fin.sum_univ_castSucc (fun j : Fin (2 * n + 1) => ∫ y, v j.val y ∂μ)
      simp only [Fin.val_zero, Fin.val_succ] at hs
      simp only [Fin.val_castSucc, Fin.val_last, hvN, add_zero] at ht
      linarith
    rw [hfield]
    have hS : Integrable (∑ j : Fin (2 * n), (u j.val + v (j.val + 1))) μ := by
      have hSraw := integrable_finsetSum (Finset.univ : Finset (Fin (2 * n)))
        (fun j _ => (hiu j.val).add (hiv (j.val + 1)))
      convert hSraw using 1
      funext y
      simp only [Finset.sum_apply]
    have hadd := integral_add (hiv 0) hS
    have hsum := integral_finsetSum (Finset.univ : Finset (Fin (2 * n)))
      (fun j _ => (hiu j.val).add (hiv (j.val + 1)))
    simp only [Pi.add_apply, Finset.sum_apply] at hadd hsum ⊢
    rw [hadd, hsum]
    simp_rw [integral_add (hiu _) (hiv _)]
    simp only [Finset.sum_add_distrib]
    dsimp only [u, v] at hshift ⊢
    linarith
  rw [gradedInner_symm g.form F (diracRealForm g.form G),
    hdecomp F G hF hG hcF hcG, hdecomp G F hG hF hcG hcF]
  apply Finset.sum_congr rfl
  intro j _
  have h1 := integral_exterior_codifferential g μ hμ (F j.val) (G (j.val + 1))
    (hF j.val) (hG (j.val + 1)) (hcF j.val)
  have h2 := integral_exterior_codifferential g μ hμ (G j.val) (F (j.val + 1))
    (hG j.val) (hF (j.val + 1)) (hcG j.val)
  rw [formInner_symm g.form (F j.val) (codifferentialRealForm g.form (G (j.val + 1)))] at h1
  rw [formInner_symm g.form (G j.val) (codifferentialRealForm g.form (F (j.val + 1)))] at h2
  linarith

theorem diracCorePair_output_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : OperatorCandidates.GradedRealForm M)
    (h : OperatorCandidates.DiracCorePair g.form μ A W) : W = diracRealForm g.form A := by
  have hA : ∀ j, SmoothRealForm (A j) := fun j => (h.2.2.1 j).1
  have hr := diracRealForm_represents g μ hμ A hA
  funext j
  apply realForm_eq_of_center_components
  intro x I
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  exact (h.2.2.2 x (chartPt x x) hz j I).trans (hr x (chartPt x x) hz j I).symm

theorem diracCorePair_symmetric (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W B Z : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.DiracCorePair g.form μ A W)
    (hB : OperatorCandidates.DiracCorePair g.form μ B Z) :
    (∫ y, OperatorCandidates.gradedInner g.form A Z y ∂μ) =
      ∫ y, OperatorCandidates.gradedInner g.form W B y ∂μ := by
  rw [diracCorePair_output_eq g μ hμ A W hA, diracCorePair_output_eq g μ hμ B Z hB]
  exact (integral_graded_dirac_green g μ hμ A B
    (fun j => (hA.2.2.1 j).1) (fun j => (hB.2.2.1 j).1)
    (fun j => (hA.2.2.1 j).2.1) (fun j => (hB.2.2.1 j).2.1)).symm

/-- Every original Dirac core pair belongs to the original maximal graph. -/
theorem diracCorePair_maximal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : OperatorCandidates.GradedRealForm M)
    (h : OperatorCandidates.DiracCorePair g.form μ A W) :
    OperatorCandidates.DiracMaximalGraph g.form μ A W := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro B Z hBZ
  exact ⟨gradedInner_integrable g μ A Z h.1 hBZ.2.1,
    gradedInner_integrable g μ W B h.2.1 hBZ.1, diracCorePair_symmetric g μ hμ A W B Z h hBZ⟩

theorem modelGradedMetricBilin_chart (g : HermitianField M) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (A B : OperatorCandidates.GradedRealForm M) :
    modelGradedMetricBilin g x z (modelChartGradedForm A x z) (modelChartGradedForm B x z) =
      OperatorCandidates.gradedInner g A B (chartInv x z) := by
  rw [modelGradedMetricBilin_apply]
  unfold OperatorCandidates.gradedInner
  apply Finset.sum_congr rfl
  intro j _
  exact modelFormInner_chartForm g (A j.val) (B j.val) x hz

/-- Raw L² pairings supported in one actual chart transport with exactly
the true density and normalized fibre metric. -/
theorem integral_gradedInner_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (A B : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A)
    (hB : OperatorCandidates.GradedL2 g.form μ B)
    (hBzero : ∀ j y, y ∉ (extChartAt (ComplexModel n) x).source → B j y = 0) :
    (∫ y, OperatorCandidates.gradedInner g.form A B y ∂μ) =
      ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        modelGradedMetricBilin g.form x z (modelChartGradedForm A x z) (modelChartGradedForm B x z)
          ∂lebesgueC n := by
  have hzero (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) :
      OperatorCandidates.gradedInner g.form A B y = 0 := by
    unfold OperatorCandidates.gradedInner
    apply Finset.sum_eq_zero
    intro j _
    calc
      _ = formInner g.form (A j.val) 0 y := formInner_congr_at g.form rfl (hBzero j.val y hy)
      _ = 0 := congrFun (formInner_zero_right g.form (A j.val)) y
  have hm : AEStronglyMeasurable (OperatorCandidates.gradedInner g.form A B)
      (μ.restrict (extChartAt (ComplexModel n) x).source) :=
    (gradedInner_integrable g μ A B hA hB).aestronglyMeasurable.mono_measure Measure.restrict_le_self
  calc
    _ = ∫ y in (extChartAt (ComplexModel n) x).source, OperatorCandidates.gradedInner g.form A B y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det *
        OperatorCandidates.gradedInner g.form A B (chartInv x z) ∂lebesgueC n := by
      simpa only [smul_eq_mul] using L18Aux.integral_chart_volume_ae g μ hμ x hm
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [modelGradedMetricBilin_chart g.form x hz A B]

theorem diracRealForm_eq_zero_outside_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : OperatorCandidates.GradedRealForm M)
    (hA : ∀ j, SmoothRealForm (A j)) (x : M.Carrier)
    (hAs : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source) :
    ∀ j y, y ∉ (extChartAt (ComplexModel n) x).source → diracRealForm g.form A j y = 0 := by
  intro j y hy
  have hd (i : ℕ) : exteriorRealForm (A i) y = 0 := by
    by_contra h
    exact hy (hAs i ((representsExterior_support_subset (exteriorRealForm_represents (A i) (hA i))) (subset_closure h)))
  have hδ (i : ℕ) : codifferentialRealForm g.form (A (i + 1)) y = 0 := by
    by_contra h
    exact hy (hAs (i + 1) ((codifferentialRealForm_support_subset g μ hμ (A (i + 1)) (hA (i + 1))) (subset_closure h)))
  cases j with
  | zero => exact hδ 0
  | succ j =>
      change exteriorRealForm (A j) y + codifferentialRealForm g.form (A (j + 2)) y = 0
      rw [hd j, hδ (j + 1), add_zero]

/-- The original actual maximal graph supplies the genuine weighted weak
test equation for every compact smooth finite model test in a chart. -/
theorem diracMaximalGraph_chart_test (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W) (x : M.Carrier)
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
      (modelChartGradedForm A x z) (modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)) ∂lebesgueC n) =
    ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
      (modelChartGradedForm W x z) (G z) ∂lebesgueC n := by
  let T := modelGradedChartPushforward x G
  let Z := diracRealForm g.form T
  have hp := modelGradedChartPushforward_properties x G hG hcG hGO
  have hT : ∀ j, SmoothRealForm (T j) := fun j => (hp j).1
  have hTs : ∀ j, closure {y | T j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source := fun j => (hp j).2.2
  have hT0 : ∀ j y, y ∉ (extChartAt (ComplexModel n) x).source → T j y = 0 := by
    intro j y hy
    by_contra h
    exact hy (hTs j (subset_closure h))
  have hZ0 : ∀ j y, y ∉ (extChartAt (ComplexModel n) x).source → Z j y = 0 :=
    diracRealForm_eq_zero_outside_chart g μ hμ T hT x hTs
  have hC := modelGradedChartPushforward_corePair g μ hμ x G hG hcG hGO
  have h := (hmax.2.2 T Z hC).2.2
  rw [integral_gradedInner_chart g μ hμ x A Z hmax.1 hC.2.1 hZ0,
    integral_gradedInner_chart g μ hμ x W T hmax.2.1 hC.1 hT0] at h
  calc
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
        (modelChartGradedForm A x z) (modelChartGradedForm Z x z) ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only [T, Z]
      rw [modelGradedChartPushforward_dirac_to_chart g μ hμ x G hG hcG hGO hz]
    _ = _ := h
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only [T]
      rw [modelGradedChartPushforward_to_chart x G hz]

/-- Weighted model Green is inherited from actual Dirac core symmetry. -/
theorem modelDiracJet_weighted_green (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier)
    (F G : ComplexVector n → modelGradedFiber n) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G)
    (hFO : tsupport F ⊆ chartTarget x) (hGO : tsupport G ⊆ chartTarget x) :
    (∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
      (F z) (modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)) ∂lebesgueC n) =
    ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
      (modelDiracJetCLM g.form x z (F z, fderiv ℝ F z)) (G z) ∂lebesgueC n := by
  have hC := modelGradedChartPushforward_corePair g μ hμ x F hF hcF hFO
  have hm := diracCorePair_maximal g μ hμ _ _ hC
  have ht := diracMaximalGraph_chart_test g μ hμ _ _ hm x G hG hcG hGO
  calc
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
        (modelChartGradedForm (modelGradedChartPushforward x F) x z)
        (modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)) ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [modelGradedChartPushforward_to_chart x F hz]
    _ = _ := ht
    _ = _ := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only
      rw [modelGradedChartPushforward_dirac_to_chart g μ hμ x F hF hcF hFO hz]

/-- The actual derivative coefficients of Dirac in a fixed finite graded basis. -/
def diracScalarDerivativeCoefficient {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) :
    α → α → RIdx n → ComplexVector n → ℝ :=
  firstJetDerivativeCoefficient (realModelBasis n) b (fun r => (b.coord r).toContinuousLinearMap)
    (modelDiracJetCLM g x)

def diracScalarValueCoefficient {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) :
    α → α → ComplexVector n → ℝ :=
  firstJetValueCoefficient b (fun r => (b.coord r).toContinuousLinearMap) (modelDiracJetCLM g x)

theorem modelDiracJetCLM_scalar_apply {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (G : ComplexVector n → modelGradedFiber n) (z : ComplexVector n)
    (hG : DifferentiableAt ℝ G z) (r : α) :
    firstOrderSystemApply (realModelBasis n) (diracScalarDerivativeCoefficient g x b)
        (diracScalarValueCoefficient g x b) (fun y c => b.repr (G y) c) z r =
      b.repr (modelDiracJetCLM g x z (G z, fderiv ℝ G z)) r := by
  simpa only [diracScalarDerivativeCoefficient, diracScalarValueCoefficient,
    LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using
    firstOrderSystemApply_eq_firstJet (realModelBasis n) b (fun r => (b.coord r).toContinuousLinearMap)
      (modelDiracJetCLM g x) G z hG r

theorem diracScalarDerivativeCoefficient_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (r c : α) (i : RIdx n) :
    ContDiffOn ℝ ∞ (diracScalarDerivativeCoefficient g.form x b r c i) (chartTarget x) :=
  firstJetDerivativeCoefficient_contDiffOn (realModelBasis n) b (fun r => (b.coord r).toContinuousLinearMap)
    (modelDiracJetCLM g.form x) (chartTarget x) (modelDiracJetCLM_contDiffOn g x) r c i

theorem diracScalarValueCoefficient_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α) :
    ContDiffOn ℝ ∞ (diracScalarValueCoefficient g.form x b r c) (chartTarget x) :=
  firstJetValueCoefficient_contDiffOn b (fun r => (b.coord r).toContinuousLinearMap)
    (modelDiracJetCLM g.form x) (chartTarget x) (modelDiracJetCLM_contDiffOn g x) r c

/-- Multiplying the genuine metric dual test by a scalar reads precisely
the corresponding scalar test against the original coefficient. -/
theorem modelRiemannianDualVector_smul_pairing {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x)
    (b : Basis α ℝ (modelGradedFiber n)) (r : α) (P : modelGradedFiber n) (s : ℝ) :
    Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z P
      (s • modelRiemannianDualVector g x b r z) = s * b.repr P r := by
  have h := modelRiemannianDualVector_pairing g x hz b r P
  rw [← modelGradedMetricBilin_apply] at h
  simp only [map_smul, RingHom.id_apply, smul_eq_mul]
  calc
    _ = s * (Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z P
        (modelRiemannianDualVector g x b r z)) := by ring
    _ = _ := by rw [h]

/-- Evaluation of the actual Dirac calculator on an elementary value and
derivative jet, with its exact real scalar coefficients. -/
theorem diracScalar_basis_jet {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (r c : α) (s : ℝ) (ξ : ComplexVector n →L[ℝ] ℝ) :
    b.repr (modelDiracJetCLM g x z (s • b c, ξ.smulRight (b c))) r =
      s * diracScalarValueCoefficient g x b r c z +
        ∑ i : RIdx n, ξ (realModelBasis n i) * diracScalarDerivativeCoefficient g x b r c i z := by
  have h := firstJetCLM_apply_basis (realModelBasis n) b (b.coord r).toContinuousLinearMap
    (modelDiracJetCLM g x z) (s • b c) (ξ.smulRight (b c))
  simpa [diracScalarDerivativeCoefficient, diracScalarValueCoefficient,
    firstJetDerivativeCoefficient, firstJetValueCoefficient, map_smul,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    Finsupp.single_apply, smul_eq_mul] using h

/-- A compact scalar test supported in an open chart makes a locally smooth
scalar coefficient into a genuine globally smooth compact test. -/
theorem scalar_cutoff_contDiff_properties {O : Set (ComplexVector n)} (hO : IsOpen O)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (f : ComplexVector n → ℝ) (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun z => φ z * f z) ∧ HasCompactSupport (fun z => φ z * f z) ∧
      tsupport (fun z => φ z * f z) ⊆ tsupport φ := by
  have hs : tsupport (fun z => φ z * f z) ⊆ tsupport φ := by
    apply closure_mono
    intro z hz hzero
    exact hz (by change φ z * f z = 0; rw [hzero, zero_mul])
  refine ⟨?_, hcφ.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport φ
  · exact hφ.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds (hφO hz)))
  · have heq : (fun w => φ w * f w) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport φ).compl_mem_nhds hz] with w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- A genuine smooth scalar distribution is determined by the original
compact smooth tests. The proof uses a nonnegative bump times its square. -/
theorem eq_zero_of_smooth_integral_tests (ν : Measure (ComplexVector n)) [ν.IsAddHaarMeasure]
    {O : Set (ComplexVector n)} (hO : IsOpen O) (f : ComplexVector n → ℝ)
    (hf : ContDiffOn ℝ ∞ f O)
    (htest : ∀ ψ : ComplexVector n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ z, ψ z * f z ∂ν) = 0) {z : ComplexVector n} (hz : z ∈ O) : f z = 0 := by
  obtain ⟨φ, hφO, hcφ, hφ, hφrange, hφz⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hO.mem_nhds hz)
  have hp := scalar_cutoff_contDiff_properties hO φ hφ hcφ hφO f hf
  have hzero : (∫ w, φ w * (f w) ^ 2 ∂ν) = 0 := by
    calc
      _ = ∫ w, (φ w * f w) * f w ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
      _ = 0 := htest _ hp.1 hp.2.1 (hp.2.2.trans hφO)
  have hi : Integrable (fun w => φ w * (f w) ^ 2) ν :=
    L18Aux.integrable_compactTest_mul ν hO hφ.continuous hcφ hφO (hf.continuousOn.pow 2)
  have hn (w : ComplexVector n) : 0 ≤ φ w * (f w) ^ 2 :=
    mul_nonneg (hφrange ⟨w, rfl⟩).1 (sq_nonneg _)
  have hae : (fun w => φ w * (f w) ^ 2) =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg hn hi).mp hzero
  have hc : ContinuousOn (fun w => φ w * (f w) ^ 2) O := hφ.continuous.continuousOn.mul (hf.continuousOn.pow 2)
  have hv : φ z * (f z) ^ 2 = 0 := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) hO hc continuousOn_const hz
  rw [hφz, one_mul] at hv
  exact sq_eq_zero_iff.mp hv

theorem modelRiemannianGradedGram_basis_left {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (c : α) (Q : modelGradedFiber n) :
    Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z (b c) Q =
      ∑ d, modelRiemannianGradedGram g x z b c d * b.repr Q d := by
  have h := modelRiemannianGradedGram_pairing g x z b (b c) Q
  rw [← modelGradedMetricBilin_apply g x z (b c) Q] at h
  simpa [dotProduct, Matrix.mulVec, Finsupp.single_apply] using h

/-- Every coordinate of the actual operator applied to a smooth model test
is smooth on the genuine chart target. -/
theorem diracScalar_apply_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (G : ComplexVector n → modelGradedFiber n) (hG : ContDiff ℝ ∞ G) (r : α) :
    ContDiffOn ℝ ∞ (fun z => b.repr (modelDiracJetCLM g.form x z (G z, fderiv ℝ G z)) r) (chartTarget x) := by
  have hU (c : α) : ContDiff ℝ ∞ (fun z => b.repr (G z) c) := by
    simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using
      (b.coord c).toContinuousLinearMap.contDiff.comp hG
  have hD (c : α) (i : RIdx n) :
      ContDiff ℝ ∞ (fun z => fderiv ℝ (fun y => b.repr (G y) c) z (realModelBasis n i)) :=
    ((hU c).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hP : ContDiffOn ℝ ∞ (fun z => firstOrderSystemApply (realModelBasis n)
      (diracScalarDerivativeCoefficient g.form x b) (diracScalarValueCoefficient g.form x b)
      (fun y c => b.repr (G y) c) z r) (chartTarget x) := by
    apply ContDiffOn.sum
    intro c _
    apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro i _
      exact (diracScalarDerivativeCoefficient_contDiffOn g x b r c i).mul (hD c i).contDiffOn
    · exact (diracScalarValueCoefficient_contDiffOn g x b r c).mul (hU c).contDiffOn
  apply hP.congr
  intro z _
  exact (modelDiracJetCLM_scalar_apply g.form x b G z (hG.differentiable (by simp) z) r).symm

/-- The exact formal-adjoint row of the actual scalar first-order system.
All derivatives remain on its smooth coefficients and the scalar test. -/
def diracFormalAdjointTestRow {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (r c : α) (φ : ComplexVector n → ℝ) (z : ComplexVector n) : ℝ :=
  -(∑ i : RIdx n, (diracScalarDerivativeCoefficient g x b r c i z * fderiv ℝ φ z (realModelBasis n i) +
      fderiv ℝ (diracScalarDerivativeCoefficient g x b r c i) z (realModelBasis n i) * φ z)) +
    diracScalarValueCoefficient g x b r c z * φ z

theorem diracFormalAdjointTestRow_contDiffOn {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (r c : α) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiffOn ℝ ∞ (diracFormalAdjointTestRow g.form x b r c φ) (chartTarget x) := by
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hφd (i : RIdx n) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z (realModelBasis n i)) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have had (i : RIdx n) : ContDiffOn ℝ ∞ (fun z =>
      fderiv ℝ (diracScalarDerivativeCoefficient g.form x b r c i) z (realModelBasis n i)) (chartTarget x) :=
    ((diracScalarDerivativeCoefficient_contDiffOn g x b r c i).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  apply ContDiffOn.add
  · apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro i _
    exact ((diracScalarDerivativeCoefficient_contDiffOn g x b r c i).mul (hφd i).contDiffOn).add
      ((had i).mul hφ.contDiffOn)
  · exact (diracScalarValueCoefficient_contDiffOn g x b r c).mul hφ.contDiffOn

theorem diracScalar_basis_test_apply {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (r c : α) (ψ : ComplexVector n → ℝ)
    (hψ : DifferentiableAt ℝ ψ z) :
    b.repr (modelDiracJetCLM g x z (ψ z • b c, fderiv ℝ (fun y => ψ y • b c) z)) r =
      ψ z * diracScalarValueCoefficient g x b r c z +
        ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * diracScalarDerivativeCoefficient g x b r c i z := by
  have hd : fderiv ℝ (fun y => ψ y • b c) z = (fderiv ℝ ψ z).smulRight (b c) :=
    (hψ.hasFDerivAt.smul_const (b c)).fderiv
  rw [hd]
  exact diracScalar_basis_jet g x z b r c (ψ z) (fderiv ℝ ψ z)

/-- Actual weighted Dirac Green, with the genuine inverse-Gram dual test,
reads one output row against an arbitrary scalar compact test. -/
theorem diracDualTest_integral_identity {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (φ ψ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ)
    (hφO : tsupport φ ⊆ chartTarget x) (hψO : tsupport ψ ⊆ chartTarget x) :
    let T := fun z => φ z • modelRiemannianDualVector g.form x b r z
    (∫ z, ψ z * (Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z (b c)
      (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z))) ∂lebesgueC n) =
    ∫ z, φ z * (ψ z * diracScalarValueCoefficient g.form x b r c z +
      ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * diracScalarDerivativeCoefficient g.form x b r c i z)
        ∂lebesgueC n := by
  let T := fun z => φ z • modelRiemannianDualVector g.form x b r z
  let F := fun z => ψ z • b c
  have hT := modelRiemannianDualVector_cutoff_properties g x b r φ hφ hcφ hφO
  have hF : ContDiff ℝ ∞ F := hψ.smul contDiff_const
  have hcF : HasCompactSupport F := hcψ.smul_right
  have hFO : tsupport F ⊆ chartTarget x := (tsupport_smul_subset_left ψ (fun _ => b c)).trans hψO
  have h := modelDiracJet_weighted_green g μ hμ x F T hF hT.1 hcF hT.2.1 hFO hT.2.2
  have hψzero (z : ComplexVector n) (hz : z ∉ chartTarget x) : ψ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hψO h))
  have hφzero (z : ComplexVector n) (hz : z ∉ chartTarget x) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
  calc
    _ = ∫ z in chartTarget x, ψ z * (Real.sqrt (realMetricFn g.form x z).det *
        modelGradedMetricBilin g.form x z (b c) (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z))) ∂lebesgueC n :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [hψzero z hz, zero_mul])).symm
    _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
        (F z) (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z)) ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only [F]
      simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
      ring
    _ = _ := h
    _ = ∫ z in chartTarget x, φ z * (ψ z * diracScalarValueCoefficient g.form x b r c z +
        ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * diracScalarDerivativeCoefficient g.form x b r c i z)
          ∂lebesgueC n := by
      apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
      intro z hz
      dsimp only [T, F]
      rw [modelRiemannianDualVector_smul_pairing g.form x hz b r _ (φ z),
        diracScalar_basis_test_apply g.form x z b r c ψ (hψ.differentiable (by simp) z)]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [hφzero z hz, zero_mul])

/-- Flat integration by parts computes the genuine formal-adjoint row of
the already identified actual Dirac scalar coefficients. -/
theorem diracFormalAdjointTestRow_integral {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (φ ψ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hψO : tsupport ψ ⊆ chartTarget x) :
    (∫ z, φ z * (ψ z * diracScalarValueCoefficient g.form x b r c z +
      ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * diracScalarDerivativeCoefficient g.form x b r c i z)
        ∂lebesgueC n) =
      ∫ z, ψ z * diracFormalAdjointTestRow g.form x b r c φ z ∂lebesgueC n := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let a := diracScalarDerivativeCoefficient g.form x b r c
  let b0 := diracScalarValueCoefficient g.form x b r c
  let U : RIdx n → ComplexVector n → ℝ := fun i z => φ z * a i z
  let K : ComplexVector n → ℝ := fun z => ∑ i, fderiv ℝ ψ z (realModelBasis n i) * U i z
  let L : ComplexVector n → ℝ := fun z => ψ z * ∑ i, fderiv ℝ (U i) z (realModelBasis n i)
  let t : ComplexVector n → ℝ := fun z => ψ z * (b0 z * φ z)
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have ha (i : RIdx n) : ContDiffOn ℝ ∞ (a i) (chartTarget x) :=
    diracScalarDerivativeCoefficient_contDiffOn g x b r c i
  have hU (i : RIdx n) : ContDiffOn ℝ ∞ (U i) (chartTarget x) := hφ.contDiffOn.mul (ha i)
  have hdψ (i : RIdx n) : Continuous (fun z => fderiv ℝ ψ z (realModelBasis n i)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hKI : Integrable K (lebesgueC n) :=
    integrable_finsetSum (Finset.univ : Finset (RIdx n)) (fun i _ =>
      L18Aux.integrable_compactTest_mul (lebesgueC n) hO (hdψ i)
        (hcψ.fderiv_apply ℝ (realModelBasis n i))
        ((tsupport_fderiv_apply_subset ℝ (realModelBasis n i)).trans hψO) (hU i).continuousOn)
  have hDU : ContDiffOn ℝ ∞ (fun z => ∑ i : RIdx n, fderiv ℝ (U i) z (realModelBasis n i)) (chartTarget x) := by
    apply ContDiffOn.sum
    intro i _
    exact ((hU i).fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hLI : Integrable L (lebesgueC n) :=
    L18Aux.integrable_compactTest_mul (lebesgueC n) hO hψ.continuous hcψ hψO hDU.continuousOn
  have htI : Integrable t (lebesgueC n) :=
    L18Aux.integrable_compactTest_mul (lebesgueC n) hO hψ.continuous hcψ hψO
      ((diracScalarValueCoefficient_contDiffOn g x b r c).continuousOn.mul hφ.continuous.continuousOn)
  have hIBP := L18Aux.integral_compactTest_divergence_on (lebesgueC n) hO
    (hψ.of_le (by simp)) hcψ hψO U (fun i => (hU i).of_le (by simp)) (realModelBasis n)
  change (∫ z, L z ∂lebesgueC n) = -(∫ z, K z ∂lebesgueC n) at hIBP
  have hprod (i : RIdx n) (z : ComplexVector n) (hz : z ∈ chartTarget x) :
      fderiv ℝ (U i) z (realModelBasis n i) = a i z * fderiv ℝ φ z (realModelBasis n i) +
        fderiv ℝ (a i) z (realModelBasis n i) * φ z := by
    have hp := DFunLike.congr_fun (fderiv_fun_mul (hφ.differentiable (by simp) z)
      (((ha i).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))) (realModelBasis n i)
    calc
      _ = φ z * fderiv ℝ (a i) z (realModelBasis n i) + a i z * fderiv ℝ φ z (realModelBasis n i) := hp
      _ = _ := by ring
  have hsum (z : ComplexVector n) (hz : z ∈ chartTarget x) :
      (∑ i : RIdx n, fderiv ℝ (U i) z (realModelBasis n i)) =
        ∑ i : RIdx n, (a i z * fderiv ℝ φ z (realModelBasis n i) +
          fderiv ℝ (a i) z (realModelBasis n i) * φ z) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hprod i z hz
  have hLeft : (fun z => φ z * (ψ z * b0 z + ∑ i : RIdx n,
      fderiv ℝ ψ z (realModelBasis n i) * a i z)) = t + K := by
    funext z
    change φ z * (ψ z * b0 z + ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * a i z) =
      ψ z * (b0 z * φ z) + ∑ i : RIdx n, fderiv ℝ ψ z (realModelBasis n i) * (φ z * a i z)
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have hRight : (fun z => ψ z * diracFormalAdjointTestRow g.form x b r c φ z) = t - L := by
    funext z
    change ψ z * diracFormalAdjointTestRow g.form x b r c φ z =
      ψ z * (b0 z * φ z) - ψ z * ∑ i : RIdx n, fderiv ℝ (U i) z (realModelBasis n i)
    by_cases hz : z ∈ chartTarget x
    · rw [hsum z hz]
      dsimp only [diracFormalAdjointTestRow, a, b0]
      ring
    · have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hψO h))
      simp only [hψz, zero_mul, sub_self]
  change (∫ z, φ z * (ψ z * b0 z + ∑ i : RIdx n,
    fderiv ℝ ψ z (realModelBasis n i) * a i z) ∂lebesgueC n) = _
  rw [hLeft, hRight]
  change (∫ z, t z + K z ∂lebesgueC n) = ∫ z, t z - L z ∂lebesgueC n
  rw [integral_add htI hKI, integral_sub htI hLI]
  linarith

/-- The inverse-Gram model test has exactly the standard formal-adjoint
row of the actual Dirac system, including every metric-density derivative. -/
theorem diracFormalAdjointTestRow_dual {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    let T := fun w => φ w • modelRiemannianDualVector g.form x b r w
    Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z (b c)
      (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z)) =
        diracFormalAdjointTestRow g.form x b r c φ z := by
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let T := fun w => φ w • modelRiemannianDualVector g.form x b r w
  let R := fun w => Real.sqrt (realMetricFn g.form x w).det * modelGradedMetricBilin g.form x w (b c)
    (modelDiracJetCLM g.form x w (T w, fderiv ℝ T w))
  have hT := modelRiemannianDualVector_cutoff_properties g x b r φ hφ hcφ hφO
  have hO := isOpen_extChartAt_target (I := ComplexModel n) x
  have hRs : ContDiffOn ℝ ∞ (fun w => ∑ d, modelRiemannianGradedGram g.form x w b c d *
      b.repr (modelDiracJetCLM g.form x w (T w, fderiv ℝ T w)) d) (chartTarget x) := by
    apply ContDiffOn.sum
    intro d _
    exact (modelRiemannianGradedGram_contDiffOn g x b c d).mul (diracScalar_apply_contDiffOn g x b T hT.1 d)
  have hR : ContDiffOn ℝ ∞ R (chartTarget x) := by
    apply hRs.congr
    intro w _
    exact modelRiemannianGradedGram_basis_left g.form x w b c (modelDiracJetCLM g.form x w (T w, fderiv ℝ T w))
  have hRow := diracFormalAdjointTestRow_contDiffOn g x b r c φ hφ
  have htest : ∀ ψ : ComplexVector n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTarget x → (∫ w, ψ w * (R w - diracFormalAdjointTestRow g.form x b r c φ w) ∂lebesgueC n) = 0 := by
    intro ψ hψ hcψ hψO
    have h1 := diracDualTest_integral_identity g μ hμ x b r c φ ψ hφ hψ hcφ hcψ hφO hψO
    have h2 := diracFormalAdjointTestRow_integral g x b r c φ ψ hφ hψ hcψ hψO
    have heq : (∫ w, ψ w * R w ∂lebesgueC n) =
        ∫ w, ψ w * diracFormalAdjointTestRow g.form x b r c φ w ∂lebesgueC n := h1.trans h2
    have hiR := L18Aux.integrable_compactTest_mul (lebesgueC n) hO hψ.continuous hcψ hψO hR.continuousOn
    have hiRow := L18Aux.integrable_compactTest_mul (lebesgueC n) hO hψ.continuous hcψ hψO hRow.continuousOn
    calc
      _ = ∫ w, ψ w * R w - ψ w * diracFormalAdjointTestRow g.form x b r c φ w ∂lebesgueC n :=
        integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)
      _ = (∫ w, ψ w * R w ∂lebesgueC n) -
          ∫ w, ψ w * diracFormalAdjointTestRow g.form x b r c φ w ∂lebesgueC n := integral_sub hiR hiRow
      _ = 0 := sub_eq_zero.mpr heq
  have hv := eq_zero_of_smooth_integral_tests (lebesgueC n) hO
    (fun w => R w - diracFormalAdjointTestRow g.form x b r c φ w) (hR.sub hRow) htest hz
  exact sub_eq_zero.mp hv

theorem modelGradedMetricBilin_basis_expand {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n)
    (b : Basis α ℝ (modelGradedFiber n)) (P Q : modelGradedFiber n) :
    Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z P Q =
      ∑ c, b.repr P c * (Real.sqrt (realMetricFn g x z).det * modelGradedMetricBilin g x z (b c) Q) := by
  conv_lhs => rw [← b.sum_repr P]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem diracFormalAdjointTestRow_zero_of_notMem_tsupport {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r c : α)
    (φ : ComplexVector n → ℝ) {z : ComplexVector n} (hz : z ∉ tsupport φ) :
    diracFormalAdjointTestRow g x b r c φ z = 0 := by
  simp only [diracFormalAdjointTestRow, image_eq_zero_of_notMem_tsupport hz,
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hz, ContinuousLinearMap.zero_apply,
    mul_zero, zero_add, Finset.sum_const_zero, neg_zero, add_zero]

/-- The original frozen Dirac maximal graph satisfies the standard scalar
distribution equation in every actual chart. No derivative of either raw
L² input or raw L² output occurs in this conclusion. -/
theorem diracMaximalGraph_scalar_test {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M) (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r : α)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    (∫ z, φ z * b.repr (modelChartGradedForm W x z) r ∂lebesgueC n) =
      ∫ z, (∑ c, b.repr (modelChartGradedForm A x z) c *
        diracFormalAdjointTestRow g.form x b r c φ z) ∂lebesgueC n := by
  let T := fun z => φ z • modelRiemannianDualVector g.form x b r z
  have hT := modelRiemannianDualVector_cutoff_properties g x b r φ hφ hcφ hφO
  have h := diracMaximalGraph_chart_test g μ hμ A W hmax x T hT.1 hT.2.1 hT.2.2
  have hs : (∫ z in chartTarget x, (∑ c, b.repr (modelChartGradedForm A x z) c *
        diracFormalAdjointTestRow g.form x b r c φ z) ∂lebesgueC n) =
      ∫ z in chartTarget x, φ z * b.repr (modelChartGradedForm W x z) r ∂lebesgueC n := by
    calc
      _ = ∫ z in chartTarget x, Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z
          (modelChartGradedForm A x z) (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z)) ∂lebesgueC n := by
        apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
        intro z hz
        dsimp only
        rw [modelGradedMetricBilin_basis_expand g.form x z b]
        apply Finset.sum_congr rfl
        intro c _
        have hr : Real.sqrt (realMetricFn g.form x z).det * modelGradedMetricBilin g.form x z (b c)
            (modelDiracJetCLM g.form x z (T z, fderiv ℝ T z)) = diracFormalAdjointTestRow g.form x b r c φ z :=
          diracFormalAdjointTestRow_dual g μ hμ x b r c φ hφ hcφ hφO hz
        rw [hr]
      _ = _ := h
      _ = _ := by
        apply setIntegral_congr_fun (isOpen_extChartAt_target (I := ComplexModel n) x).measurableSet
        intro z hz
        dsimp only [T]
        rw [modelRiemannianDualVector_smul_pairing g.form x hz b r (modelChartGradedForm W x z) (φ z)]
  have hφzero (z : ComplexVector n) (hz : z ∉ chartTarget x) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
  have hsumzero (z : ComplexVector n) (hz : z ∉ chartTarget x) :
      (∑ c, b.repr (modelChartGradedForm A x z) c * diracFormalAdjointTestRow g.form x b r c φ z) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    rw [diracFormalAdjointTestRow_zero_of_notMem_tsupport g.form x b r c φ (fun h => hz (hφO h)), mul_zero]
  calc
    _ = ∫ z in chartTarget x, φ z * b.repr (modelChartGradedForm W x z) r ∂lebesgueC n :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hφzero z hz, zero_mul])).symm
    _ = _ := hs.symm
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hsumzero

/-- The finite graded zero pullback uses the already constructed genuine
alternating chart pullbacks degree by degree. -/
def modelGradedChartPullbackZero (A : OperatorCandidates.GradedRealForm M)
    (x : M.Carrier) (z : ComplexVector n) : modelGradedFiber n :=
  fun j => chartFormPullbackZero x (A j.val) z

theorem modelGradedChartPullbackZero_eq (A : OperatorCandidates.GradedRealForm M)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    modelGradedChartPullbackZero A x z = modelChartGradedForm A x z := by
  funext j
  exact if_pos hz

/-- Actual compact chart-supported graded L² inputs have compact standard
model L² coordinates; no smoothness of the raw section is needed. -/
theorem modelGradedChartPullbackZero_properties {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A)
    (hcA : ∀ j, CompactlySupportedRealForm (A j)) (x : M.Carrier)
    (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n)) :
    HasCompactSupport (modelGradedChartPullbackZero A x) ∧
      tsupport (modelGradedChartPullbackZero A x) ⊆ chartTarget x ∧
      MemLp (modelGradedChartPullbackZero A x) 2 (lebesgueC n) ∧
      ∀ c, MemLp (fun z => b.repr (modelGradedChartPullbackZero A x z) c) 2 (lebesgueC n) := by
  classical
  let K := ⋃ j : Fin (2 * n + 1), tsupport (chartFormPullbackZero x (A j.val))
  have hj (j : Fin (2 * n + 1)) := chartFormPullbackZero_support_properties x (A j.val) (hcA j.val) (hAx j.val)
  have hK : IsCompact K := isCompact_iUnion (fun j => (hj j).1)
  have hKO : K ⊆ chartTarget x := by
    intro z hz
    obtain ⟨j, hjz⟩ := Set.mem_iUnion.mp hz
    exact (hj j).2.1 hjz
  have hs : tsupport (modelGradedChartPullbackZero A x) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    apply hz
    funext j
    exact image_eq_zero_of_notMem_tsupport (fun hjz => hzK (Set.mem_iUnion.mpr ⟨j, hjz⟩))
  have hm : MemLp (modelGradedChartPullbackZero A x) 2 (lebesgueC n) :=
    MemLp.of_eval (fun j => chartFormPullbackZero_memLp g μ hμ (A j.val) (hA.2 j.val)
      (hcA j.val) x (hAx j.val))
  refine ⟨hK.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hKO, hm, ?_⟩
  intro c
  simpa only [Function.comp_def, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using
    (b.coord c).toContinuousLinearMap.comp_memLp' hm

/-- The original maximal equation reads the same actual scalar row on the
standard zero pullbacks, since the row and its test vanish off the chart. -/
theorem diracMaximalGraph_zeroPullback_scalar_test {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M) (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n)) (r : α)
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    (∫ z, φ z * b.repr (modelGradedChartPullbackZero W x z) r ∂lebesgueC n) =
      ∫ z, (∑ c, b.repr (modelGradedChartPullbackZero A x z) c *
        diracFormalAdjointTestRow g.form x b r c φ z) ∂lebesgueC n := by
  calc
    _ = ∫ z, φ z * b.repr (modelChartGradedForm W x z) r ∂lebesgueC n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ chartTarget x
      · rw [modelGradedChartPullbackZero_eq W x hz]
      · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
        simp only [hφz, zero_mul]
    _ = _ := diracMaximalGraph_scalar_test g μ hμ A W hmax x b r φ hφ hcφ hφO
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro z
      dsimp only
      by_cases hz : z ∈ chartTarget x
      · rw [modelGradedChartPullbackZero_eq A x hz]
      · apply Finset.sum_congr rfl
        intro c _
        rw [diracFormalAdjointTestRow_zero_of_notMem_tsupport g.form x b r c φ (fun h => hz (hφO h))]
        simp only [mul_zero]

/-- Splitting a finite formal-adjoint row integral gives the precise weak
system consumed by the proved Friedrichs graph approximation theorem. -/
theorem firstOrderSystemWeakEquation_of_row_integral {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype α] [Fintype ι] (ν : Measure E) [IsLocallyFiniteMeasure ν]
    (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (ha : ∀ r c i, ContDiff ℝ 1 (a r c i)) (hb : ∀ r c, Continuous (b r c))
    (u : E → α → ℝ) (w : E → β → ℝ) (hu : ∀ c, MemLp (fun z => u z c) 2 ν)
    (hrow : ∀ r φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ z, φ z * w z r ∂ν) = ∫ z, (∑ c, u z c *
        (-(∑ i, (a r c i z * fderiv ℝ φ z (v i) +
          fderiv ℝ (a r c i) z (v i) * φ z)) + b r c z * φ z)) ∂ν) :
    firstOrderSystemWeakEquation ν v a b u w := by
  classical
  intro r φ hφ hcφ
  have hD (c : α) (i : ι) : Integrable (fun z =>
      (a r c i z * fderiv ℝ φ z (v i) + fderiv ℝ (a r c i) z (v i) * φ z) * u z c) ν := by
    have hda : Continuous (fun z => fderiv ℝ (a r c i) z (v i)) :=
      ((ha r c i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcont : Continuous (fun z => a r c i z * fderiv ℝ φ z (v i) +
        fderiv ℝ (a r c i) z (v i) * φ z) :=
      ((ha r c i).continuous.mul ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).add
        (hda.mul hφ.continuous)
    have hcomp : HasCompactSupport (fun z => a r c i z * fderiv ℝ φ z (v i) +
        fderiv ℝ (a r c i) z (v i) * φ z) :=
      (hcφ.fderiv_apply ℝ (v i)).mul_left.add hcφ.mul_left
    have hi := (hcont.memLp_of_hasCompactSupport hcomp (p := 2)).integrable_mul (hu c)
    exact hi.congr (Filter.Eventually.of_forall fun z => rfl)
  have hB (c : α) : Integrable (fun z => φ z * (b r c z * u z c)) ν := by
    have hm : MemLp (fun z => φ z * b r c z) 2 ν :=
      (hφ.continuous.mul (hb r c)).memLp_of_hasCompactSupport hcφ.mul_right
    exact (hm.integrable_mul (hu c)).congr (Filter.Eventually.of_forall fun z => by
      change (φ z * b r c z) * u z c = φ z * (b r c z * u z c)
      ring)
  have hf (c : α) : (fun z => u z c *
      (-(∑ i, (a r c i z * fderiv ℝ φ z (v i) +
        fderiv ℝ (a r c i) z (v i) * φ z)) + b r c z * φ z)) =
      (fun z => -(∑ i, (a r c i z * fderiv ℝ φ z (v i) +
        fderiv ℝ (a r c i) z (v i) * φ z) * u z c) + φ z * (b r c z * u z c)) := by
    funext z
    rw [← Finset.sum_mul]
    ring
  have hRI (c : α) : Integrable (fun z => u z c *
      (-(∑ i, (a r c i z * fderiv ℝ φ z (v i) +
        fderiv ℝ (a r c i) z (v i) * φ z)) + b r c z * φ z)) ν := by
    rw [hf c]
    exact (integrable_finsetSum Finset.univ (fun i _ => hD c i)).neg.add (hB c)
  rw [hrow r φ hφ hcφ, integral_finsetSum Finset.univ (fun c _ => hRI c)]
  apply Finset.sum_congr rfl
  intro c _
  have hN : Integrable (fun z => -(∑ i, (a r c i z * fderiv ℝ φ z (v i) +
      fderiv ℝ (a r c i) z (v i) * φ z) * u z c)) ν :=
    (integrable_finsetSum Finset.univ (fun i _ => hD c i)).neg
  rw [hf c, integral_add hN (hB c),
    integral_neg, integral_finsetSum Finset.univ (fun i _ => hD c i)]

/-- A compact actual maximal graph pair in one chart satisfies the global
Euclidean weak equation for genuine compactly extended actual coefficients.
The cutoff derivative vanishes on both raw supports by Fermat's theorem. -/
theorem diracMaximalGraph_exists_chart_weak_system {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M) (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hcA : ∀ j, CompactlySupportedRealForm (A j)) (hcW : ∀ j, CompactlySupportedRealForm (W j))
    (x : M.Carrier) (hAx : ∀ j, closure {y | A j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (hWx : ∀ j, closure {y | W j y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (b : Basis α ℝ (modelGradedFiber n)) :
    let U := modelGradedChartPullbackZero A x
    let V := modelGradedChartPullbackZero W x
    ∃ χ : ComplexVector n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ chartTarget x ∧ (∀ z, χ z ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ z ∈ tsupport U ∪ tsupport V, χ z = 1 ∧ fderiv ℝ χ z = 0) ∧
      (∀ r c i, ContDiff ℝ ∞ (fun z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z)) ∧
      (∀ r c, ContDiff ℝ ∞ (fun z => χ z * diracScalarValueCoefficient g.form x b r c z)) ∧
      firstOrderSystemWeakEquation (lebesgueC n) (realModelBasis n)
        (fun r c i z => χ z * diracScalarDerivativeCoefficient g.form x b r c i z)
        (fun r c z => χ z * diracScalarValueCoefficient g.form x b r c z)
        (fun z c => b.repr (U z) c) (fun z r => b.repr (V z) r) := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [lebesgueC_eq_volume]
    infer_instance
  let U := modelGradedChartPullbackZero A x
  let V := modelGradedChartPullbackZero W x
  have hU := modelGradedChartPullbackZero_properties g μ hμ A hmax.1 hcA x hAx b
  have hV := modelGradedChartPullbackZero_properties g μ hμ W hmax.2.1 hcW x hWx b
  let K := tsupport U ∪ tsupport V
  have hcK : IsCompact K := hU.1.union hV.1
  have hKO : K ⊆ chartTarget x := Set.union_subset hU.2.1 hV.2.1
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨Ω, hΩ, hKΩ, hΩO, hcΩ⟩ := exists_open_between_and_isCompact_closure hcK hO hKO
  obtain ⟨χ, hχ, hχrange0, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hΩ hcK.isClosed hKΩ
  have hχrange (z : ComplexVector n) : χ z ∈ Set.Icc (0 : ℝ) 1 :=
    hχrange0 (Set.mem_range_self z)
  have hcχ : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    simpa only [tsupport, hχsupport] using hcΩ
  have hχO : tsupport χ ⊆ chartTarget x := by
    simpa only [tsupport, hχsupport] using hΩO
  have hχK (z : ComplexVector n) (hz : z ∈ K) : χ z = 1 := (hχone z).mp hz
  have hχd (z : ComplexVector n) (hz : z ∈ K) : fderiv ℝ χ z = 0 := by
    apply IsLocalMax.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by rw [hχK z hz]; exact (hχrange y).2)
  let a := diracScalarDerivativeCoefficient g.form x b
  let b0 := diracScalarValueCoefficient g.form x b
  have ha (r c : α) (i : RIdx n) : ContDiffOn ℝ ∞ (a r c i) (chartTarget x) :=
    diracScalarDerivativeCoefficient_contDiffOn g x b r c i
  have hb (r c : α) : ContDiffOn ℝ ∞ (b0 r c) (chartTarget x) :=
    diracScalarValueCoefficient_contDiffOn g x b r c
  have hAe (r c : α) (i : RIdx n) : ContDiff ℝ ∞ (fun z => χ z * a r c i z) :=
    (scalar_cutoff_contDiff_properties hO χ hχ hcχ hχO _ (ha r c i)).1
  have hBe (r c : α) : ContDiff ℝ ∞ (fun z => χ z * b0 r c z) :=
    (scalar_cutoff_contDiff_properties hO χ hχ hcχ hχO _ (hb r c)).1
  refine ⟨χ, hχ, hcχ, hχO, hχrange, (fun z hz => ⟨hχK z hz, hχd z hz⟩), hAe, hBe, ?_⟩
  apply firstOrderSystemWeakEquation_of_row_integral (lebesgueC n) (realModelBasis n)
    (fun r c i z => χ z * a r c i z) (fun r c z => χ z * b0 r c z)
    (fun r c i => (hAe r c i).of_le (by simp)) (fun r c => (hBe r c).continuous)
    (fun z c => b.repr (U z) c) (fun z r => b.repr (V z) r) hU.2.2.2
  intro r φ hφ hcφ
  let ψ := fun z => χ z * φ z
  have hψ : ContDiff ℝ ∞ ψ := hχ.mul hφ
  have hcψ : HasCompactSupport ψ := hcχ.mul_right
  have hψχ : tsupport ψ ⊆ tsupport χ := by
    apply closure_mono
    intro z hz hzero
    exact hz (by change χ z * φ z = 0; rw [hzero, zero_mul])
  have hagg := diracMaximalGraph_zeroPullback_scalar_test g μ hμ A W hmax x b r ψ hψ hcψ (hψχ.trans hχO)
  have hw (z : ComplexVector n) : φ z * b.repr (V z) r = ψ z * b.repr (V z) r := by
    by_cases hz : V z = 0
    · simp only [hz, map_zero, Finsupp.zero_apply, mul_zero]
    · have hzK : z ∈ K := Or.inr (subset_tsupport V hz)
      simp only [ψ, hχK z hzK, one_mul]
  have hu (z : ComplexVector n) (c : α) :
      b.repr (U z) c * diracFormalAdjointTestRow g.form x b r c ψ z =
      b.repr (U z) c *
        (-(∑ i : RIdx n, ((χ z * a r c i z) * fderiv ℝ φ z (realModelBasis n i) +
          fderiv ℝ (fun y => χ y * a r c i y) z (realModelBasis n i) * φ z)) +
          (χ z * b0 r c z) * φ z) := by
    by_cases hz : U z = 0
    · simp only [hz, map_zero, Finsupp.zero_apply, zero_mul]
    · have hzK : z ∈ K := Or.inl (subset_tsupport U hz)
      have hzO := hKO hzK
      have hdψ : fderiv ℝ ψ z = fderiv ℝ φ z := by
        simpa only [hχK z hzK, hχd z hzK, one_smul, zero_smul, smul_zero, add_zero, zero_add] using
          fderiv_fun_mul (hχ.differentiable (by simp) z) (hφ.differentiable (by simp) z)
      have hdA (i : RIdx n) : fderiv ℝ (fun y => χ y * a r c i y) z = fderiv ℝ (a r c i) z := by
        simpa only [hχK z hzK, hχd z hzK, one_smul, zero_smul, smul_zero, add_zero, zero_add] using
          fderiv_fun_mul (hχ.differentiable (by simp) z)
            (((ha r c i).contDiffAt (hO.mem_nhds hzO)).differentiableAt (by simp))
      simp only [diracFormalAdjointTestRow, hdψ, hdA, ψ, hχK z hzK, one_mul, a, b0]
  calc
    _ = ∫ z, ψ z * b.repr (V z) r ∂lebesgueC n :=
      integral_congr_ae (Filter.Eventually.of_forall hw)
    _ = _ := hagg
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => Finset.sum_congr rfl (fun c _ => hu z c))

/-- Smooth compact coefficient extensions have the genuine uniform value
and Lipschitz bounds required by the proved Friedrichs commutator theorem. -/
theorem compact_contDiff_coefficient_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f) :
    ∃ C : ℝ, ∃ K : NNReal, (∀ z, ‖f z‖ ≤ C) ∧ LipschitzWith K f := by
  obtain ⟨C, hC⟩ := hf.continuous.bounded_above_of_compact_support hcf
  obtain ⟨D, hD⟩ := (hf.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcf.fderiv ℝ)
  refine ⟨C, ⟨max D 0, le_max_right _ _⟩, hC, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp))
  intro z
  change ‖fderiv ℝ f z‖ ≤ max D 0
  exact (hD z).trans (le_max_left _ _)

end Forms

/-- The third conjunct of `LeafObligations.L03`, with exactly its closed quantification. -/
theorem essentialSelfAdjointOfSquare_all :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      OperatorCandidates.EssentialSelfAdjointOfSquare (H := H) :=
  fun _ _ _ _ => essentialSelfAdjointOfSquare

end Yau.LeafProofs.L03

import Yau.Proofs.HeatSmoothExhaustionDimension

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.SmoothExhaustionAux

abbrev AffineBlock (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] ℝ) × ℝ

def affinePerturbation {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (f : α → ℝ) (v : Fin N → α → E) (w : Fin N → α → ℝ)
    (θ : Fin N → AffineBlock E) (p : α) : ℝ :=
  f p+∑ i, ((θ i).1 (v i p)+(θ i).2*w i p)

section Parameters
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {N : ℕ}

abbrev OtherParameters (i : Fin N) := {j : Fin N // j ≠ i} → AffineBlock E

def affineResidual (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    (i : Fin N) (u : E × OtherParameters (E := E) i) : ℝ :=
  f u.1+∑ j : {j : Fin N // j ≠ i}, ((u.2 j).1 (v j u.1)+(u.2 j).2*w j u.1)

def affineSpatialD (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    (i : Fin N) (u : E × OtherParameters (E := E) i) : E →L[ℝ] ℝ :=
  (fderiv ℝ (affineResidual f v w i) u).comp
    (ContinuousLinearMap.inl ℝ E (OtherParameters (E := E) i))

def badParameterGraph (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    (i : Fin N) (u : E × OtherParameters (E := E) i) (j : Fin N) : AffineBlock E :=
  if h : j=i then
    (-affineSpatialD f v w i u,
      affineSpatialD f v w i u u.1-affineResidual f v w i u)
  else u.2 ⟨j,h⟩

theorem affineResidual_smooth (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    {V : Set E} (hf : ContDiffOn ℝ ∞ f V)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) V) (hw : ∀ j, ContDiffOn ℝ ∞ (w j) V)
    (i : Fin N) :
    ContDiffOn ℝ ∞ (affineResidual f v w i) (V ×ˢ Set.univ) := by
  apply (hf.comp contDiffOn_fst (fun _ hu => hu.1)).add
  apply ContDiffOn.sum
  intro j _
  have ha : ContDiffOn ℝ ∞
      (fun u : E × OtherParameters (E := E) i => (u.2 j).1) (V ×ˢ Set.univ) := by fun_prop
  have hb : ContDiffOn ℝ ∞
      (fun u : E × OtherParameters (E := E) i => (u.2 j).2) (V ×ˢ Set.univ) := by fun_prop
  exact (ha.clm_apply ((hv j).comp contDiffOn_fst (fun _ hu => hu.1))).add
    (hb.mul ((hw j).comp contDiffOn_fst (fun _ hu => hu.1)))

theorem affineSpatialD_smooth (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) V) (hw : ∀ j, ContDiffOn ℝ ∞ (w j) V)
    (i : Fin N) :
    ContDiffOn ℝ ∞ (affineSpatialD f v w i) (V ×ˢ Set.univ) := by
  exact ((affineResidual_smooth f v w hf hv hw i).fderiv_of_isOpen
    (hV.prod isOpen_univ) (by simp)).clm_comp contDiffOn_const

theorem badParameterGraph_smooth (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) V) (hw : ∀ j, ContDiffOn ℝ ∞ (w j) V)
    (i : Fin N) :
    ContDiffOn ℝ ∞ (badParameterGraph f v w i) (V ×ˢ Set.univ) := by
  classical
  apply contDiffOn_pi.mpr
  intro j
  by_cases hj : j=i
  · simp only [badParameterGraph,dif_pos hj]
    have HD := affineSpatialD_smooth f v w hV hf hv hw i
    exact HD.neg.prodMk ((HD.clm_apply contDiffOn_fst).sub (affineResidual_smooth f v w hf hv hw i))
  · simp only [badParameterGraph,dif_neg hj]
    fun_prop

theorem affineSpatialD_hasFDerivAt (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    {V : Set E} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) V) (hw : ∀ j, ContDiffOn ℝ ∞ (w j) V)
    (i : Fin N) (z : E) (hz : z ∈ V) (q : OtherParameters (E := E) i) :
    HasFDerivAt (fun z' => affineResidual f v w i (z',q))
      (affineSpatialD f v w i (z,q)) z := by
  have HR := ((affineResidual_smooth f v w hf hv hw i).contDiffAt
    ((hV.prod isOpen_univ).mem_nhds (show (z,q) ∈ V ×ˢ Set.univ from ⟨hz,Set.mem_univ _⟩))).differentiableAt (by simp)
  have Hin : HasFDerivAt (fun z' : E => (z',q))
      (ContinuousLinearMap.inl ℝ E (OtherParameters (E := E) i)) z := by
    convert (hasFDerivAt_id z).prodMk (hasFDerivAt_const q z) using 1 <;>
      ext x <;> simp
  exact HR.hasFDerivAt.comp z Hin

theorem sum_split_one (F : Fin N → ℝ) (i : Fin N) :
    ∑ j, F j = F i+∑ j : {j : Fin N // j ≠ i}, F j := by
  classical
  have H := (Fintype.sum_subtype_add_sum_subtype (fun j : Fin N => j=i) F).symm
  have hd : ((default : {j : Fin N // j=i}) : Fin N)=i :=
    (default : {j : Fin N // j=i}).property
  simpa only [Fintype.sum_unique,hd] using H


/-- The singular-zero parameters belong to the explicit graph. -/
theorem singular_zero_mem_graph (f : E → ℝ) (v : Fin N → E → E) (w : Fin N → E → ℝ)
    {V U : Set E} (hV : IsOpen V) (hU : IsOpen U) (hUV : U ⊆ V)
    (hf : ContDiffOn ℝ ∞ f V)
    (hv : ∀ j, ContDiffOn ℝ ∞ (v j) V) (hw : ∀ j, ContDiffOn ℝ ∞ (w j) V)
    (i : Fin N) (hidentity : ∀ z ∈ U, v i z=z ∧ w i z=1)
    (θ : Fin N → AffineBlock E) (z : E) (hz : z ∈ U)
    (hzero : affinePerturbation f v w θ z=0)
    (hsing : fderiv ℝ (affinePerturbation f v w θ) z=0) :
    θ ∈ badParameterGraph f v w i '' (V ×ˢ Set.univ) := by
  classical
  let q : OtherParameters (E := E) i := fun j => θ j
  let D := affineSpatialD f v w i (z,q)
  let R := affineResidual f v w i (z,q)
  have heq : affinePerturbation f v w θ =ᶠ[𝓝 z]
      (fun z' => affineResidual f v w i (z',q)+(θ i).1 z'+(θ i).2) := by
    filter_upwards [hU.mem_nhds hz] with z' hz'
    rw [affinePerturbation,sum_split_one _ i,(hidentity z' hz').1,(hidentity z' hz').2]
    simp only [affineResidual,q,mul_one]
    ring
  have HD := ((affineSpatialD_hasFDerivAt f v w hV hf hv hw i z (hUV hz) q).add
    (θ i).1.hasFDerivAt).add_const (θ i).2
  have Hsum : D+(θ i).1=0 := by
    calc
      _ = fderiv ℝ (fun z' => affineResidual f v w i (z',q)+(θ i).1 z'+(θ i).2) z := HD.fderiv.symm
      _ = fderiv ℝ (affinePerturbation f v w θ) z := heq.fderiv_eq.symm
      _ = 0 := hsing
  have ha : (θ i).1 = -D := eq_neg_of_add_eq_zero_right Hsum
  have Hb : R+(θ i).1 z+(θ i).2=0 := heq.self_of_nhds.symm.trans hzero
  have hb : (θ i).2=D z-R := by rw [ha,ContinuousLinearMap.neg_apply] at Hb;linarith
  refine ⟨(z,q),⟨hUV hz,Set.mem_univ _⟩,?_⟩
  funext j
  by_cases hj : j=i
  · subst j
    simp only [badParameterGraph,dif_pos rfl]
    exact Prod.ext ha.symm hb.symm
  · simp only [badParameterGraph,dif_neg hj,q]

end Parameters
end Yau.Proofs.SmoothExhaustionAux

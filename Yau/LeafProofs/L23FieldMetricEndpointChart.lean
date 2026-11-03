import Yau.LeafProofs.L23FieldMetricUnitFamily
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! The genuine endpoint map has the explicit invertible zero-speed jet. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
universe u

def endpointLinearEquiv (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E × E) ≃L[ℝ] (E × E) where
  toLinearEquiv :=
    { toFun := fun p => (p.1,p.1+p.2)
      invFun := fun p => (p.1,p.2-p.1)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp
      map_add' := by intro p q; ext <;> simp [add_add_add_comm]
      map_smul' := by intro a p; ext <;> simp [smul_add] }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem exists_product_endpoint_chart
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : Set E) (hB : IsOpen B) (z : E) (hz : z ∈ B) (ρ : ℝ) (hρ : 0 < ρ)
    (g : E × E → E) (hg : ContDiffOn ℝ 3 g (B ×ˢ Metric.ball (0 : E) ρ))
    (hzero : ∀ x ∈ B, g (x,0) = x)
    (hvertical : HasFDerivAt (fun v => g (z,v)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ (B' : Set E) (ρ' : ℝ) (e : OpenPartialHomeomorph (E × E) (E × E)),
      IsOpen B' ∧ z ∈ B' ∧ B' ⊆ B ∧ 0 < ρ' ∧
      e.source = B' ×ˢ Metric.ball (0 : E) ρ' ∧
      e.source ⊆ B ×ˢ Metric.ball (0 : E) ρ ∧
      Set.EqOn e (fun p => (p.1,g p)) e.source ∧
      ContDiffOn ℝ 3 e.symm e.target := by
  let D := B ×ˢ Metric.ball (0 : E) ρ
  let p₀ : E × E := (z,0)
  have hD : IsOpen D := hB.prod Metric.isOpen_ball
  have hp₀ : p₀ ∈ D := ⟨hz,Metric.mem_ball_self hρ⟩
  have hgAt : ContDiffAt ℝ 3 g p₀ := hg.contDiffAt (hD.mem_nhds hp₀)
  have hhorizontal : HasFDerivAt (fun x => g (x,0)) (ContinuousLinearMap.id ℝ E) z := by
    apply (hasFDerivAt_id (𝕜 := ℝ) z).congr_of_eventuallyEq
    filter_upwards [hB.mem_nhds hz] with x hx
    exact hzero x hx
  have hDh := (hgAt.differentiableAt (by norm_num)).hasFDerivAt.comp z
    (ContinuousLinearMap.inl ℝ E E).hasFDerivAt
  have hDv := (hgAt.differentiableAt (by norm_num)).hasFDerivAt.comp 0
    ((hasFDerivAt_const (𝕜 := ℝ) z (0 : E)).prodMk (hasFDerivAt_id (𝕜 := ℝ) (0 : E)))
  have hH := hDh.unique hhorizontal
  have hV := hDv.unique hvertical
  have hderiv : fderiv ℝ g p₀ = ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro w
    have Hh := congrArg (fun A => A w.1) hH
    have Hv := congrArg (fun A => A w.2) hV
    change fderiv ℝ g p₀ (w.1,0) = w.1 at Hh
    change fderiv ℝ g p₀ (0,w.2) = w.2 at Hv
    change fderiv ℝ g p₀ w = w.1+w.2
    calc
      _ = fderiv ℝ g p₀ (w.1,0) + fderiv ℝ g p₀ (0,w.2) := by rw [← map_add]; simp
      _ = _ := by rw [Hh,Hv]
  let F : E × E → E × E := fun p => (p.1,g p)
  have hF : ContDiffOn ℝ 3 F D := contDiffOn_fst.prodMk hg
  have hFAt : ContDiffAt ℝ 3 F p₀ := hF.contDiffAt (hD.mem_nhds hp₀)
  have hDF : HasFDerivAt F (endpointLinearEquiv E).toContinuousLinearMap p₀ := by
    convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := p₀)).prodMk
      (hgAt.differentiableAt (by norm_num)).hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro w
    change (w.1,w.1+w.2) = (w.1,fderiv ℝ g p₀ w)
    rw [hderiv]
    rfl
  let e₀ := hFAt.toOpenPartialHomeomorph F hDF (by norm_num)
  have he₀ : p₀ ∈ e₀.source := hFAt.mem_toOpenPartialHomeomorph_source hDF (by norm_num)
  have hInv : ContDiffAt ℝ 3 e₀.symm (F p₀) := hFAt.to_localInverse hDF (by norm_num)
  obtain ⟨dInv,hdInv,hInvSub⟩ := Metric.mem_nhds_iff.mp (hInv.eventually (by norm_num))
  have hopen : IsOpen (e₀.source ∩ (D ∩ F ⁻¹' Metric.ball (F p₀) dInv)) :=
    e₀.open_source.inter (hF.continuousOn.isOpen_inter_preimage hD Metric.isOpen_ball)
  have hpoint : p₀ ∈ e₀.source ∩ (D ∩ F ⁻¹' Metric.ball (F p₀) dInv) :=
    ⟨he₀,hp₀,Metric.mem_ball_self hdInv⟩
  obtain ⟨d,hd,hdSub⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hpoint)
  let D' := Metric.ball z d ×ˢ Metric.ball (0 : E) d
  have hD' : IsOpen D' := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hsub : D' ⊆ e₀.source ∩ (D ∩ F ⁻¹' Metric.ball (F p₀) dInv) := by
    intro p hp
    apply hdSub
    rw [Metric.mem_ball,Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hp.1,hp.2⟩
  let e := e₀.restrOpen D' hD'
  have hsource : e.source = D' := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr (fun p hp => (hsub hp).1)
  refine ⟨Metric.ball z d,d,e,Metric.isOpen_ball,Metric.mem_ball_self hd,?_,hd,hsource,?_,?_,?_⟩
  · intro x hx
    have hp : ((x,0) : E × E) ∈ D' := ⟨hx,Metric.mem_ball_self hd⟩
    exact (hsub hp).2.1.1
  · intro p hp
    rw [hsource] at hp
    exact (hsub hp).2.1
  · intro p _
    rfl
  · intro y hy
    have hx : e.symm y ∈ D' := by rw [← hsource]; exact e.map_target hy
    have hFy : F (e.symm y) ∈ Metric.ball (F p₀) dInv := (hsub hx).2.2
    have heval : F (e.symm y) = y := e.right_inv hy
    rw [heval] at hFy
    have Hinv : ContDiffAt ℝ 3 e₀.symm y := hInvSub hFy
    exact Hinv.contDiffWithinAt

end Yau.LeafProofs.L23Aux

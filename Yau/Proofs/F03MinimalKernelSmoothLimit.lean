import Yau.Proofs.F03MinimalPackedLimit
import Yau.Proofs.F03LinearTensorTransport

/-! Literal local C∞ convergence of the original actual exhaustion kernels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

theorem dirichletMinimalKernelCandidate_localSmoothLimit
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    KernelLocalSmoothLimit (dirichletExhaustionKernels g hK μ hμ O hO)
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  intro x y K Q hKc hQc hKt hQt eps T heps hepsT m η hη
  obtain ⟨Ox,hx,hKOx,hxt,hxc⟩ := exists_open_between_and_isCompact_closure hKc
    (isOpen_extChartAt_target (I := ComplexModel n) x) hKt
  obtain ⟨Oy,hy,hQOy,hyt,hyc⟩ := exists_open_between_and_isCompact_closure hQc
    (isOpen_extChartAt_target (I := ComplexModel n) y) hQt
  let l : ℝ := eps/4
  let r : ℝ := T+2
  have hl : 0 < l := by dsimp [l];positivity
  obtain ⟨J0,hSmooth,hProduct,hLimit⟩ := dirichletMinimalPackedKernel_limit g hK μ hμ O hO x y
    Ox Oy hx hy hxc hyc hxt hyt l r hl
  let Os := kernelProductSpace Ox Oy
  let us : ℕ → Point (n+n) → ℝ := fun j =>
    dirichletPackedKernel g hK μ hμ (O (J0+j)) (hO.1 (J0+j)).1 x y
  let v := dirichletMinimalPackedKernel g hK μ hμ O hO x y
  let P := kernelPairTimePack n
  let C : Set (Point (n+n)) := P '' ((K ×ˢ Q) ×ˢ Icc eps T)
  have hCc : IsCompact C := ((hKc.prod hQc).prod isCompact_Icc).image P.continuous
  have hCD : C ⊆ Os ×ˢ Ioo l r := by
    rintro p ⟨q,hq,rfl⟩
    refine ⟨?_,?_⟩
    · exact ⟨q.1,⟨hKOx hq.1.1,hQOy hq.1.2⟩,rfl⟩
    · change l < q.2 ∧ q.2 < r
      dsimp only [l,r]
      constructor <;> linarith [hq.2.1,hq.2.2]
  let R : ℝ := (max 1 ‖P.toContinuousLinearMap‖)^m
  have hR : 0 < R := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) m
  obtain ⟨N,hN⟩ := hLimit C hCc hCD m (η/R) (div_pos hη hR)
  refine ⟨J0+N,fun j hj z hz w hw t ht => ?_⟩
  let k := j-J0
  have hk : N ≤ k := by dsimp [k];omega
  have hIndex : J0+k=j := by dsimp [k];omega
  have hPacked := hN k hk (P ((z,w),t)) ⟨((z,w),t),⟨⟨hz,hw⟩,ht⟩,rfl⟩
  have hTransport := norm_iteratedFDeriv_comp_linearEquiv_lt P (fun q => us k q-v q) m ((z,w),t) η hη hPacked
  convert hTransport using 1
  congr 2
  funext q
  dsimp only [Function.comp_def,us,v,dirichletPackedKernel,dirichletMinimalPackedKernel,P,kernelPairTimePack]
  rw [hIndex]
  simp only [ContinuousLinearEquiv.prodCongr_apply,ContinuousLinearEquiv.prodCongr_symm,
    ContinuousLinearEquiv.refl_apply,ContinuousLinearEquiv.symm_apply_apply,dirichletExhaustionKernels]

end Yau.Proofs.F03Aux

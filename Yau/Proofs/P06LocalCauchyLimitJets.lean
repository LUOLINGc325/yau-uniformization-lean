import Yau.LeafProofs.L16SmoothLimit
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The full Fréchet-jet version of the uniform-limit/FTC reconstruction used
in L16. The limit is local on an open set; no PDE or norm estimate is assumed. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.LocalCauchyLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]

def FullJetCauchyOn (f : ℕ → E → ℝ) (S : Set E) : Prop :=
  ∀ m (K : Set E), IsCompact K → K ⊆ S → ∀ η : ℝ, 0 < η →
    ∃ N, ∀ j, N ≤ j → ∀ l, N ≤ l → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (f j) p - iteratedFDeriv ℝ m (f l) p‖ < η

/-- Actual locally uniform limits of all full jets, with every derivative
identified by the fundamental theorem for limits of derivatives. -/
theorem exists_smooth_fullJet_limit {f : ℕ → E → ℝ} {S : Set E}
    (hS : IsOpen S) (hf : ∀ j, ContDiffOn ℝ ∞ (f j) S) (hc : FullJetCauchyOn f S) :
    ∃ v : E → ℝ, ContDiffOn ℝ ∞ v S ∧
      ∀ m (K : Set E), IsCompact K → K ⊆ S →
        TendstoUniformlyOn (fun j => iteratedFDeriv ℝ m (f j))
          (iteratedFDeriv ℝ m v) atTop K := by
  classical
  have hex (m : ℕ) (x : E) : ∃ v : E [×m]→L[ℝ] ℝ,
      x ∈ S → Tendsto (fun j => iteratedFDeriv ℝ m (f j) x) atTop (𝓝 v) := by
    by_cases hx : x ∈ S
    · have hC : CauchySeq (fun j => iteratedFDeriv ℝ m (f j) x) := by
        apply Metric.cauchySeq_iff.mpr
        intro η hη
        obtain ⟨N,hN⟩ := hc m {x} isCompact_singleton (by simpa using hx) η hη
        exact ⟨N,fun j hj l hl => by simpa only [dist_eq_norm] using hN j hj l hl x (mem_singleton x)⟩
      obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hC
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose J hJ using hex
  have hloc (m : ℕ) : TendstoLocallyUniformlyOn
      (fun j => iteratedFDeriv ℝ m (f j)) (J m) atTop S := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hS).mpr
    intro K hKS hK
    apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
    · apply Metric.uniformCauchySeqOn_iff.mpr
      intro η hη
      obtain ⟨N,hN⟩ := hc m K hK hKS η hη
      exact ⟨N,fun j hj l hl p hp => by simpa only [dist_eq_norm] using hN j hj l hl p hp⟩
    · exact fun p hp => hJ m p (hKS hp)
  let C (m : ℕ) := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) ℝ
  have hdlim (m : ℕ) : TendstoLocallyUniformlyOn
      (fun j => fderiv ℝ (iteratedFDeriv ℝ m (f j)))
      (fun x => C m (J (m+1) x)) atTop S := by
    have h := (C m).toContinuousLinearEquiv.toContinuousLinearMap.uniformContinuous.comp_tendstoLocallyUniformlyOn (hloc (m+1))
    simpa only [C,fderiv_iteratedFDeriv,Function.comp_def,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h
  have hd (m : ℕ) (x : E) (hx : x ∈ S) : HasFDerivAt (J m) (C m (J (m+1) x)) x := by
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn hS (hdlim m)
    · intro j y hy
      have hcj : ContDiffAt ℝ (m+1 : ℕ) (f j) y :=
        ((hf j).contDiffAt (hS.mem_nhds hy)).of_le (by simp)
      exact (hcj.differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self m)).hasFDerivAt
    · exact fun y hy => hJ m y hy
    · exact hx
  have hCn : ∀ q : ℕ, ∀ m : ℕ, ContDiffOn ℝ q (J m) S := by
    intro q
    induction q with
    | zero =>
      intro m
      apply contDiffOn_zero.mpr
      apply (hloc m).continuousOn
      exact (Eventually.of_forall fun j y hy =>
        (((hf j).contDiffAt (hS.mem_nhds hy)).continuousAt_iteratedFDeriv (by simp)).continuousWithinAt).frequently
    | succ q ih =>
      intro m
      rw [show ((q+1 : ℕ) : ℕ∞ω) = (q : ℕ∞ω)+1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hS]
      refine ⟨fun x hx => (hd m x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
      apply ((C m).toContinuousLinearEquiv.contDiff.comp_contDiffOn (ih (m+1))).congr
      exact fun x hx => (hd m x hx).fderiv
  let v : E → ℝ := fun x => continuousMultilinearCurryFin0 ℝ E ℝ (J 0 x)
  have hv : ContDiffOn ℝ ∞ v S :=
    (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (contDiffOn_infty.mpr fun q => hCn q 0)
  have hjet : ∀ m : ℕ, EqOn (iteratedFDeriv ℝ m v) (J m) S := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,v,
        LinearIsometryEquiv.symm_apply_apply]
    | succ m ih =>
      intro x hx
      have heq : iteratedFDeriv ℝ m v =ᶠ[𝓝 x] J m :=
        Filter.eventually_of_mem (hS.mem_nhds hx) fun y hy => ih hy
      rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,
        heq.fderiv_eq,(hd m x hx).fderiv]
      exact (C m).symm_apply_apply _
  refine ⟨v,hv,?_⟩
  intro m K hK hKS
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hS).mp (hloc m) K hKS hK
  exact hu.congr_right (fun x hx => (hjet m (hKS hx)).symm)

end Yau.NodeProofs.P06Aux.LocalCauchyLimit

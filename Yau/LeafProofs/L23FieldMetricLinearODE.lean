import Yau.LeafProofs.L23FieldMetricLocalFlow
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual C3 fundamental solutions for time-dependent linear equations, locally uniform in initial time. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 800000

theorem linearODE_contDiffOn_three
    (A W : ℝ → E →L[ℝ] E) (I : Set ℝ) (hI : IsOpen I)
    (hA : ContDiffOn ℝ 2 A I)
    (hW : ∀ t ∈ I, HasDerivAt W ((A t).comp (W t)) t) : ContDiffOn ℝ 3 W I := by
  have hD : DifferentiableOn ℝ W I := fun t ht => (hW t ht).differentiableAt.differentiableWithinAt
  have hW₀ : ContDiffOn ℝ 0 W I := by simpa only [contDiffOn_zero] using hD.continuousOn
  have step (k : ℕ) (hk : k ≤ 2) (hWk : ContDiffOn ℝ k W I) : ContDiffOn ℝ (k+1 : ℕ) W I := by
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨hD,by simp,?_⟩
    have HC : ContDiffOn ℝ k (fun t => (A t).comp (W t)) I :=
      (hA.of_le (by exact_mod_cast hk)).clm_comp hWk
    exact HC.congr (fun t ht => (hW t ht).deriv)
  have H₁ := step 0 (by omega) hW₀
  have H₂ := step 1 (by omega) H₁
  exact step 2 le_rfl H₂

theorem exists_local_fundamental_solution [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (hJ : IsOpen J) (hA : ContDiffOn ℝ 2 A J)
    (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    ∃ r : ℝ, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Metric.ball t₀ r, ∃ W : ℝ → E →L[ℝ] E,
        W 0 = ContinuousLinearMap.id ℝ E ∧ ContDiffOn ℝ 3 W (Set.Ioo (-ε) ε) ∧
        ∀ u ∈ Set.Ioo (-ε) ε, t+u ∈ J ∧ HasDerivAt W ((A (t+u)).comp (W u)) u := by
  let F : (ℝ × (E →L[ℝ] E)) → ℝ × (E →L[ℝ] E) := fun p => (1,(A p.1).comp p.2)
  let z₀ : ℝ × (E →L[ℝ] E) := (t₀,ContinuousLinearMap.id ℝ E)
  have HF : ContDiffAt ℝ 2 F z₀ :=
    contDiffAt_const.prodMk (((hA.contDiffAt (hJ.mem_nhds ht₀)).comp z₀ contDiffAt_fst).clm_comp contDiffAt_snd)
  obtain ⟨r,hr,ε,hε,φ,V,hφ,hV,hi,hs,hx,hjoint⟩ := exists_C1_local_ODE_flow HF
    (hJ.prod isOpen_univ) (show z₀ ∈ J ×ˢ (Set.univ : Set (E →L[ℝ] E)) from ⟨ht₀,Set.mem_univ _⟩)
  refine ⟨r,hr,ε,hε,?_⟩
  intro t ht
  let p : ℝ × (E →L[ℝ] E) := (t,ContinuousLinearMap.id ℝ E)
  have hp : p ∈ Metric.ball z₀ r := by
    simpa only [p,z₀,Metric.mem_ball,Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using ht
  have hinit : φ p 0 = p := (hi p hp).1
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith,hε⟩
  have htimeD (u : ℝ) (hu : u ∈ Set.Ioo (-ε) ε) : HasDerivAt (fun v => (φ p v).1) 1 u := by
    convert! (ContinuousLinearMap.fst ℝ ℝ (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt u
      (hs p hp u hu).2.1 using 1
  have htime (u : ℝ) (hu : u ∈ Set.Ioo (-ε) ε) : (φ p u).1 = t+u := by
    have HD (v : ℝ) (hv : v ∈ Set.Ioo (-ε) ε) :
        HasDerivAt (fun s => (φ p s).1-s) 0 v := by
      convert! (htimeD v hv).sub (hasDerivAt_id v) using 1 <;> simp
    have H := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-ε) ε).isPreconnected
      (fun v hv => (HD v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (HD v hv).deriv) hu h₀
    have Hfirst : (φ p u).1-u = t := by simpa only [hinit,sub_zero] using H
    linarith
  let W : ℝ → E →L[ℝ] E := fun u => (φ p u).2
  have hmaps (u : ℝ) (hu : u ∈ Set.Ioo (-ε) ε) : t+u ∈ J := by
    rw [← htime u hu]
    exact (hs p hp u hu).1.1
  have hsol (u : ℝ) (hu : u ∈ Set.Ioo (-ε) ε) : HasDerivAt W ((A (t+u)).comp (W u)) u := by
    have H := (ContinuousLinearMap.snd ℝ ℝ (E →L[ℝ] E)).hasFDerivAt.comp_hasDerivAt u
      (hs p hp u hu).2.1
    change HasDerivAt W ((A (φ p u).1).comp (W u)) u at H
    rwa [htime u hu] at H
  have hAshift : ContDiffOn ℝ 2 (fun u => A (t+u)) (Set.Ioo (-ε) ε) :=
    hA.comp (contDiffOn_const.add contDiffOn_id) hmaps
  refine ⟨W,?_,linearODE_contDiffOn_three (fun u => A (t+u)) W _ isOpen_Ioo hAshift hsol,?_⟩
  · exact congrArg Prod.snd hinit
  · intro u hu
    exact ⟨hmaps u hu,hsol u hu⟩

end Yau.LeafProofs.L23Aux

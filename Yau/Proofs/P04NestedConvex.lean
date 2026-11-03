import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

noncomputable section
open Set Filter
open scoped Topology

namespace Yau.Proofs.P04Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem exists_norm_minimizer {C : Set H} (hne : C.Nonempty)
    (hc : IsClosed C) (hv : Convex ℝ C) :
    ∃ v ∈ C, ∀ w ∈ C, ‖v‖ ≤ ‖w‖ := by
  obtain ⟨v,hvC,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv (0 : H)
  refine ⟨v,hvC,fun w hw => ?_⟩
  have hb : BddBelow (range (fun z : C => ‖(0 : H)-z‖)) :=
    ⟨0,fun z hz => by obtain ⟨w,rfl⟩ := hz;exact norm_nonneg _⟩
  have HH := ciInf_le hb (⟨w,hw⟩ : C)
  rw [← hmin] at HH
  simpa only [zero_sub,norm_neg] using HH

theorem minimizer_distance_sq_le {C : Set H} (hc : Convex ℝ C)
    {v w : H} (hv : v ∈ C) (hw : w ∈ C)
    (hmin : ∀ z ∈ C, ‖v‖ ≤ ‖z‖) :
    ‖v-w‖^2 ≤ 2*(‖w‖^2-‖v‖^2) := by
  have hm : (1/2 : ℝ) • v+(1/2 : ℝ) • w ∈ C :=
    hc hv hw (by norm_num) (by norm_num) (by norm_num)
  have Hmin := hmin _ hm
  have hmid : ‖(1/2 : ℝ) • v+(1/2 : ℝ) • w‖ = (1/2 : ℝ)*‖v+w‖ := by
    rw [← smul_add,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  rw [hmid] at Hmin
  have Hp := parallelogram_law_with_norm ℝ v w
  nlinarith [norm_nonneg v,norm_nonneg (v+w)]

/-- Nested nonempty closed convex bounded sets in the actual complete Hilbert
space have a common point. The proof constructs a strong limit of minimizers. -/
theorem exists_mem_all_nested_closed_convex (C : ℕ → Set H)
    (hne : ∀ j, (C j).Nonempty) (hclosed : ∀ j, IsClosed (C j))
    (hconvex : ∀ j, Convex ℝ (C j)) (hnested : Antitone C)
    (R : ℝ) (hbound : ∀ j v, v ∈ C j → ‖v‖ ≤ R) :
    ∃ v : H, ∀ j, v ∈ C j := by
  classical
  choose v hv hmin using fun j => exists_norm_minimizer (hne j) (hclosed j) (hconvex j)
  let b : ℕ → ℝ := fun j => ‖v j‖^2
  have hR : 0 ≤ R := (norm_nonneg (v 0)).trans (hbound 0 _ (hv 0))
  have hbmono : Monotone b := by
    intro j l hjl
    have HH := hmin j _ (hnested hjl (hv l))
    dsimp only [b]
    nlinarith [norm_nonneg (v j),norm_nonneg (v l)]
  have hbb : BddAbove (range b) := by
    refine ⟨R^2,?_⟩
    rintro _ ⟨j,rfl⟩
    have HH := hbound j _ (hv j)
    dsimp only [b]
    nlinarith [norm_nonneg (v j)]
  let L := iSup b
  have hlim : Tendsto b atTop (𝓝 L) := tendsto_atTop_ciSup hbmono hbb
  have hle (j : ℕ) : b j ≤ L := le_ciSup hbb j
  have hcauchy : CauchySeq v := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε^2/2) (by positivity)
    refine ⟨N,fun m hm k hk => ?_⟩
    have hlow : L-b N < ε^2/2 := by
      have HH := hN N le_rfl
      rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hle N))] at HH
      exact HH
    have hclose (j l : ℕ) (hj : N ≤ j) (hjl : j ≤ l) : dist (v j) (v l) < ε := by
      have HH := minimizer_distance_sq_le (hconvex j) (hv j) (hnested hjl (hv l)) (hmin j)
      have Hmono := hbmono hj
      have Hle := hle l
      change ‖v j-v l‖^2 ≤ 2*(b l-b j) at HH
      have Hnorm : ‖v j-v l‖ < ε := by nlinarith [norm_nonneg (v j-v l)]
      simpa only [dist_eq_norm] using Hnorm
    rcases le_total m k with hmk|hkm
    · exact hclose m k hm hmk
    · simpa only [dist_comm] using hclose k m hk hkm
  obtain ⟨v₀,hv₀⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨v₀,fun j => ?_⟩
  exact (hclosed j).mem_of_tendsto hv₀
    (Filter.eventually_atTop.mpr ⟨j,fun l hl => hnested hl (hv l)⟩)

end Yau.Proofs.P04Aux

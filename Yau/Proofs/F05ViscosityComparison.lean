import Yau.Proofs.F05ViscosityMaximumContact
import Yau.Proofs.F05ViscosityContact

/-! The original upper viscosity inequality compares to an actual smooth
nonnegative solution on a compact domain through strict interior contacts. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smoothNear_time_differentiable {u : M.Carrier → ℝ → ℝ} {x : M.Carrier} {t : ℝ}
    (hu : SmoothNear u x t) : DifferentiableAt ℝ (u x) t := by
  have hCenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hh := hu.comp t (contDiffAt_const.prodMk contDiffAt_id :
    ContDiffAt ℝ ∞ (fun r : ℝ => (chartPt x x,r)) t)
  have hDiff := hh.differentiableAt (by simp)
  simpa only [Function.comp_def,hCenter] using hDiff

theorem F05_viscosity_comparison_bounded {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T S : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (u v : M.Carrier → ℝ → ℝ) (hv : NonlinearViscositySub h T v)
    (hVusc : UpperSemicontinuousOn (fun q : M.Carrier × ℝ => v q.1 q.2) (closure O ×ˢ Icc 0 S))
    (hUCont : ContinuousOn (fun q : M.Carrier × ℝ => u q.1 q.2) (closure O ×ˢ Icc 0 S))
    (hV0 : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S, 0 ≤ v x t)
    (hU0 : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S, 0 ≤ u x t)
    (B A₀ : ℝ) (hVBound : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S, v x t ≤ B)
    (hBound : ∀ x ∈ O, ∀ t ∈ Ioo 0 S,
      |scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x| ≤ A₀)
    (hInitial : ∀ x ∈ closure O, v x 0 ≤ u x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 S, v x t ≤ u x t)
    (hSmooth : ∀ x ∈ O, ∀ t ∈ Ioo 0 S, SmoothNear u x t)
    (hEquation : ∀ x ∈ O, ∀ t ∈ Ioo 0 S, timeDeriv u x t =
      scalarNonlinearRHS (scalarCurvature (h t) x) (laplacian (h t) (fun y => u y t) x) (u x t)) :
    ∀ x ∈ closure O, ∀ t ∈ Ico 0 S, v x t ≤ u x t := by
  intro x₀ hx₀ t₀ ht₀
  by_contra hn
  have hPos : 0 < v x₀ t₀-u x₀ t₀ := sub_pos.mpr (lt_of_not_ge hn)
  let C := 1+|A₀|
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hAC : A₀ < C := by dsimp only [C]; linarith [le_abs_self A₀]
  let g := fun x t => (Real.exp (C*t))⁻¹*(v x t-u x t)
  have hWeight (t : ℝ) (ht : 0 ≤ t) : 0 < (Real.exp (C*t))⁻¹ ∧ (Real.exp (C*t))⁻¹ ≤ 1 := by
    refine ⟨inv_pos.mpr (Real.exp_pos _),?_⟩
    apply (inv_le_one₀ (Real.exp_pos _)).mpr
    exact Real.one_le_exp_iff.mpr (mul_nonneg hC ht)
  have hGBound (x : M.Carrier) (hx : x ∈ closure O) (t : ℝ) (ht : t ∈ Icc 0 S) : g x t ≤ B := by
    have hGap : v x t-u x t ≤ v x t := sub_le_self _ (hU0 x hx t ht)
    exact ((mul_le_mul_of_nonneg_left hGap (hWeight t ht.1).1.le).trans
      (mul_le_of_le_one_left (hV0 x hx t ht) (hWeight t ht.1).2)).trans (hVBound x hx t ht)
  have hGPos : 0 < g x₀ t₀ := mul_pos (hWeight t₀ ht₀.1).1 hPos
  let ε := g x₀ t₀*(S-t₀)/2
  have hε : 0 < ε := div_pos (mul_pos hGPos (sub_pos.mpr ht₀.2)) (by norm_num)
  obtain ⟨s,ht₀s,hsS,hTerminal⟩ := exists_terminal_penalty_time S ε B t₀ hε ht₀.2
  have hs : 0 < s := ht₀.1.trans_lt ht₀s
  let q := fun x t => g x t-ε/(S-t)
  have hSmall : closure O ×ˢ Icc 0 s ⊆ closure O ×ˢ Icc 0 S := fun p hp => ⟨hp.1,hp.2.1,hp.2.2.trans hsS.le⟩
  have hUscGap : UpperSemicontinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2-u p.1 p.2) (closure O ×ˢ Icc 0 s) := by
    simpa only [sub_eq_add_neg,Pi.neg_apply] using (hVusc.mono hSmall).add ((hUCont.mono hSmall).neg.upperSemicontinuousOn)
  have hWeightC : Continuous (fun p : M.Carrier × ℝ => (Real.exp (C*p.2))⁻¹) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).inv₀ (fun _ => Real.exp_ne_zero _)
  have hGusc : UpperSemicontinuousOn (fun p : M.Carrier × ℝ => g p.1 p.2) (closure O ×ˢ Icc 0 s) :=
    upperSemicontinuousOn_pos_mul hUscGap hWeightC.continuousOn (fun _ _ => inv_pos.mpr (Real.exp_pos _))
  have hPenalty : ContinuousOn (fun p : M.Carrier × ℝ => ε/(S-p.2)) (closure O ×ˢ Icc 0 s) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_snd)
      (fun p hp => ne_of_gt (sub_pos.mpr (hp.2.2.trans_lt hsS)))
  have hQusc : UpperSemicontinuousOn (fun p : M.Carrier × ℝ => q p.1 p.2) (closure O ×ˢ Icc 0 s) := by
    simpa only [q,sub_eq_add_neg,Pi.neg_apply] using hGusc.add hPenalty.neg.upperSemicontinuousOn
  have hInitialQ (x : M.Carrier) (hx : x ∈ closure O) : q x 0 ≤ 0 := by
    have hGap := mul_nonpos_of_nonneg_of_nonpos (hWeight 0 le_rfl).1.le (sub_nonpos.mpr (hInitial x hx))
    change g x 0-ε/(S-0) ≤ 0
    have hPenalty0 : 0 < ε/(S-0) := div_pos hε (by linarith)
    linarith
  have hBoundaryQ (x : M.Carrier) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 s) : q x t ≤ 0 := by
    have hGap := mul_nonpos_of_nonneg_of_nonpos (hWeight t ht.1).1.le
      (sub_nonpos.mpr (hBoundary x hx t ⟨ht.1,ht.2.trans hsS.le⟩))
    change g x t-ε/(S-t) ≤ 0
    have hPenalty0 : 0 < ε/(S-t) := div_pos hε (sub_pos.mpr (ht.2.trans_lt hsS))
    linarith
  have hFinalQ (x : M.Carrier) (hx : x ∈ closure O) : q x s ≤ 0 := by
    change g x s-ε/(S-s) ≤ 0
    linarith [hGBound x hx s ⟨hs.le,hsS.le⟩]
  have hTargetQ : 0 < q x₀ t₀ := by
    have hCancel : ε/(S-t₀) = g x₀ t₀/2 := by
      dsimp only [ε]
      field_simp [ne_of_gt (sub_pos.mpr ht₀.2)]
    change 0 < g x₀ t₀-ε/(S-t₀)
    rw [hCancel]
    linarith
  obtain ⟨x,hx,t,ht,hQPos,hMax⟩ := F05_interior_upper_contact hA hs q hQusc hInitialQ hBoundaryQ hFinalQ
    ⟨x₀,hx₀,t₀,⟨ht₀.1,ht₀s.le⟩,hTargetQ⟩
  have htS : t ∈ Ioo 0 S := ⟨ht.1,ht.2.trans hsS⟩
  exact no_nonnegative_penalized_max h T u v hv x t C S ε ht.1 (htS.2.trans_le hST) htS.2 hε hMax
    hQPos.le (hSmooth x hx t htS) (F05_smoothNear_time_differentiable (hSmooth x hx t htS))
    (hEquation x hx t htS) (hU0 x (subset_closure hx) t ⟨htS.1.le,htS.2.le⟩) A₀ hAC (hBound x hx t htS)

end Yau.Proofs.F05Aux

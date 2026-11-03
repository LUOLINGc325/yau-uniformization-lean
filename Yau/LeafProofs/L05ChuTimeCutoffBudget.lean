import Yau.LeafProofs.L05ChuCausalCutoff
import Yau.LeafProofs.L16TimeTransport

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem chuCausalTimeCutoff_deriv (l r t : ℝ) :
    deriv (chuCausalTimeCutoff l r) t=deriv (L16Aux.initialTimeCutoff (r-l)) (t-l) := by
  have hd := (L16Aux.initialTimeCutoff_contDiff (r-l)).differentiable (by simp)
  have hh := (hd (t-l)).hasDerivAt.comp t ((hasDerivAt_id t).sub_const l)
  convert! hh.deriv using 1 <;> simp only [mul_one]

theorem chuCausalTimeCutoff_uniform_holder_jets {n : ℕ} {gamma : ℝ}
    (hg : 0 < gamma) (hg1 : gamma < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l r : ℝ, l < r → r-l ≤ 1 →
      HolderBound gamma (cylinder (n := n) Set.univ l r)
        (fun p => chuCausalTimeCutoff l r p.2) (C/(r-l)^2) ∧
      HolderBound gamma (cylinder (n := n) Set.univ l r)
        (fun p => deriv (chuCausalTimeCutoff l r) p.2) (C/(r-l)^2) := by
  obtain ⟨C,hC,hRule⟩ := L16Aux.initialTimeCutoff_uniform_holder_jets (n := n) hg hg1
  refine ⟨C,hC,?_⟩
  intro l r hlr hT1
  have hs := hRule (r-l) (sub_pos.mpr hlr) hT1
  have hs0 : HolderBound gamma (cylinder (n := n) Set.univ (l+(-l)) (r+(-l)))
      (fun p => L16Aux.initialTimeCutoff (r-l) p.2) (C/(r-l)^2) := by
    simpa only [add_neg_cancel,← sub_eq_add_neg] using hs.1
  have hs1 : HolderBound gamma (cylinder (n := n) Set.univ (l+(-l)) (r+(-l)))
      (fun p => deriv (L16Aux.initialTimeCutoff (r-l)) p.2) (C/(r-l)^2) := by
    simpa only [add_neg_cancel,← sub_eq_add_neg] using hs.2
  have h0 := L16Aux.holderBound_timeTranslate (l := l) (r := r) (τ := -l) hs0
  have h1 := L16Aux.holderBound_timeTranslate (l := l) (r := r) (τ := -l) hs1
  have hzero : HolderBound gamma (cylinder (n := n) Set.univ l r)
      (fun p => chuCausalTimeCutoff l r p.2) (C/(r-l)^2) := by
    convert! h0 using 1
  have hone : HolderBound gamma (cylinder (n := n) Set.univ l r)
      (fun p => deriv (L16Aux.initialTimeCutoff (r-l)) (p.2-l)) (C/(r-l)^2) := by
    convert! h1 using 1
  refine ⟨hzero,?_⟩
  exact L16Aux.holderBound_congr_on hone (fun p hp => (chuCausalTimeCutoff_deriv l r p.2).symm)

end Yau.LeafProofs.L05Aux

import Yau.Proofs.F05BootstrapQuotientSource
import Yau.Proofs.F05BootstrapQuotientLimit
import Yau.Proofs.F05BootstrapShiftLimit

/-! The full actual quotient source has a common Holder bound and converges
to the computed first good differentiated source. Current Hessians are only
shifted and passed to their Holder limits, never differentiated jointly. -/

open Set Filter
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05FirstGoodSource (T : ℝ) (d : Option (RIdx n)) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ) (z : Point n) : ℝ :=
  F05GoodPartial T d f z+
    (∑ j,∑ k,F05GoodPartial T d a z j k*F05RelDD X u z (realVec j) (realVec k))+
    ∑ j,F05GoodPartial T d (fun p => b p j) z*F05RelD X u z (realVec j)

theorem F05_first_good_source_eq_word_source (T : ℝ) (d : Option (RIdx n)) (X : Set (Space n))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (f u : Point n → ℝ) :
    F05FirstGoodSource T d X a b f u = F05GoodSource T X a b f u [d] := by
  funext z
  simp only [F05FirstGoodSource,F05GoodSource,F05GoodCorrection,F05GoodWord,commutatorSplits,
    List.flatMap_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  ring

theorem F05_contraction_source_tendsto {f : ℕ → ℝ} {a : ℕ → Mat n} {b : ℕ → RIdx n → ℝ}
    {H : ℕ → Space n →L[ℝ] Space n →L[ℝ] ℝ} {G : ℕ → Space n →L[ℝ] ℝ}
    {fLim : ℝ} {aLim : Mat n} {bLim : RIdx n → ℝ}
    {HLim : Space n →L[ℝ] Space n →L[ℝ] ℝ} {GLim : Space n →L[ℝ] ℝ}
    (hf : Tendsto f atTop (𝓝 fLim)) (ha : Tendsto a atTop (𝓝 aLim))
    (hb : ∀ j, Tendsto (fun k => b k j) atTop (𝓝 (bLim j)))
    (hH : Tendsto H atTop (𝓝 HLim)) (hG : Tendsto G atTop (𝓝 GLim)) :
    Tendsto (fun k => f k+(∑ j,∑ l,a k j l*H k (realVec j) (realVec l))+
      ∑ j,b k j*G k (realVec j)) atTop
      (𝓝 (fLim+(∑ j,∑ l,aLim j l*HLim (realVec j) (realVec l))+
        ∑ j,bLim j*GLim (realVec j))) := by
  have hA (j l : RIdx n) : Tendsto (fun k => a k j l) atTop (𝓝 (aLim j l)) :=
    ((matrixEntryCLM j l).continuous.tendsto aLim).comp ha
  have hHessian (j l : RIdx n) : Tendsto (fun k => H k (realVec j) (realVec l)) atTop
      (𝓝 (HLim (realVec j) (realVec l))) := by
    have hEvaluation : Continuous (fun A : Space n →L[ℝ] Space n →L[ℝ] ℝ => A (realVec j) (realVec l)) := by fun_prop
    exact (hEvaluation.tendsto HLim).comp hH
  have hGradient (j : RIdx n) : Tendsto (fun k => G k (realVec j)) atTop (𝓝 (GLim (realVec j))) := by
    have hEvaluation : Continuous (fun A : Space n →L[ℝ] ℝ => A (realVec j)) := by fun_prop
    exact (hEvaluation.tendsto GLim).comp hG
  have hPrincipal := tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
    (fun l _ => (hA j l).mul (hHessian j l)))
  have hDrift := tendsto_finsetSum Finset.univ (fun j _ => (hb j).mul (hGradient j))
  exact (hf.add hPrincipal).add hDrift

theorem F05_good_quotient_source_common_limit {ν d : Option (RIdx n)} {T α F M U : ℝ}
    (hα : 0 < α) {Q K : Set (Point n)} {h : ℕ → ℝ} (hh : ∀ k, 0 < h k)
    (hZero : Tendsto h atTop (𝓝 0)) (hQ : Q ⊆ K)
    (hSegment : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1,
      F05GoodSegment d (h k) p θ ∈ F05PosPatch ν T)
    (hIn : ∀ k p, p ∈ Q → ∀ θ ∈ Icc (0 : ℝ) 1, F05GoodSegment d (h k) p θ ∈ K)
    (X : Set (Space n)) {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f u : Point n → ℝ}
    (hDa : F05GoodDiffOn T d a (F05PosPatch ν T))
    (hDb : ∀ j, F05GoodDiffOn T d (fun p => b p j) (F05PosPatch ν T))
    (hDf : F05GoodDiffOn T d f (F05PosPatch ν T))
    (ha : HolderBound α K (F05GoodPartial T d a) M)
    (hb : ∀ j, HolderBound α K (F05GoodPartial T d (fun p => b p j)) M)
    (hf : HolderBound α K (F05GoodPartial T d f) F)
    (hH : HolderBound α K (F05RelDD X u) U) (hG : HolderBound α K (F05RelD X u) U) :
    (∀ k, HolderBound α Q (F05GoodQuotientSource d (h k) X a b f u) (linearizedSourceBudget n F M U)) ∧
      ∀ z ∈ Q, Tendsto (fun k => F05GoodQuotientSource d (h k) X a b f u z) atTop
        (𝓝 (F05FirstGoodSource T d X a b f u z)) := by
  have hfQuotient := F05_good_quotients_uniform_limit hα hh hZero hDf hSegment hIn hf
  have haQuotient := F05_good_quotients_uniform_limit hα hh hZero hDa hSegment hIn ha
  have hbQuotient (j : RIdx n) := F05_good_quotients_uniform_limit hα hh hZero (hDb j) hSegment hIn (hb j)
  have hMap : ∀ k, MapsTo (F05GoodShift d (h k)) Q K := by
    intro k p hp
    cases d with
    | none =>
      have hEndpoint := hIn k p hp 0 (by norm_num)
      simpa only [F05GoodShift,F05GoodSegment,timeTranslatePoint,zero_mul,add_zero,sub_eq_add_neg] using hEndpoint
    | some j =>
      have hEndpoint := hIn k p hp 1 (by norm_num)
      simpa only [F05GoodShift,F05GoodSegment,spatialTranslatePoint,one_mul] using hEndpoint
  have hHShift := F05_good_shifts_uniform_limit hα (fun k => (hh k).le) hZero hQ hMap hH
  have hGShift := F05_good_shifts_uniform_limit hα (fun k => (hh k).le) hZero hQ hMap hG
  refine ⟨fun k => F05_good_quotient_source_holder X (hfQuotient.1 k) (haQuotient.1 k)
    (fun j => (hbQuotient j).1 k) (F05_good_shift_holder hH (hMap k))
    (F05_good_shift_holder hG (hMap k)),?_⟩
  intro z hz
  exact F05_contraction_source_tendsto (hfQuotient.2.tendsto_at hz) (haQuotient.2.tendsto_at hz)
    (fun j => (hbQuotient j).2.tendsto_at hz) (hHShift.tendsto_at hz) (hGShift.tendsto_at hz)

end Yau.Proofs.F05Aux

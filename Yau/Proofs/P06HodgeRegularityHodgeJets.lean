import Yau.Proofs.P06HodgeRegularityHodgeForward
import Yau.Proofs.P06HodgeRegularityFiniteChain
import Yau.Proofs.P06HodgeRegularityWeakJetCutoff

/-! N original closed Hodge graph edges give N actual compact chart weak
jets in every degree. No common smooth core for the powers is used. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeClosureGraph_chain_cutoff_weakJet {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (A : ℕ → RealForm M k)
    (hA : ∀ j ≤ N, L2RealForm g.form μ (A j))
    (hgraph : ∀ j (hj : j < N),
      (realizeActualForm g μ (A j) (hA j (by omega)),
        realizeActualForm g μ (A (j+1)) (hA (j+1) (by omega))) ∈
          (hodgeCoreOperator g μ hμ k).closure.graph)
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ J : List (RIdx n) → ComplexVector n → α → ℝ,
      regularityWeakJet (lebesgueC n) Set.univ (realModelBasis n) N
        (fun z c => χ z * hodgeRegularityCoord b (A 0) x z c) J ∧
      ∀ w c, tsupport (fun z => J w z c) ⊆ tsupport χ := by
  classical
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [lebesgueC_eq_volume]; infer_instance
  letI : (lebesgueC n).IsNegInvariant := by rw [lebesgueC_eq_volume]; infer_instance
  letI : SigmaFinite (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  have hChart : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨V,hV,hχV,hVO,hcV⟩ := exists_open_between_and_isCompact_closure hcχ hChart hχO
  obtain ⟨O,hO,hVO',hOO,hcO⟩ := exists_open_between_and_isCompact_closure hcV hChart hVO
  obtain ⟨θ,hθ,hcθ,hθO,_,hθK⟩ := exists_model_chart_cutoff hChart hcO hOO
  have hθone (z : ComplexVector n) (hz : z ∈ O) : θ z = 1 := (hθK z (subset_closure hz)).1
  let q := fun i j z => θ z * hodgeRegularityQ g.form x i j z
  let E1 := fun r c i z => θ z * hodgeRegularityE1 g.form x b r c i z
  let E0 := fun r c z => θ z * hodgeRegularityE0 g.form x b r c z
  have hqp i j := scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityQ_contDiffOn g x i j)
  have hp1 r c i := scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityE1_contDiffOn g x b r c i)
  have hp0 r c := scalar_cutoff_contDiff_properties hChart θ hθ hcθ hθO _ (hodgeRegularityE0_contDiffOn g x b r c)
  obtain ⟨ell,hell,hcoercive⟩ := hodgeRegularityQ_uniform_coercive g x hcO hOO
  let U := fun j => hodgeRegularityChartInput x b θ (A j)
  have hUL (j : ℕ) (hj : j ≤ N) (c : α) : MemLp (fun z => U j z c) 2 ((lebesgueC n).restrict O) :=
    (chartFunctional_memLp g μ hμ x θ hθ hcθ hθO (b.coord c).toContinuousLinearMap (A j) (hA j hj)).restrict O
  have hEdge (j : ℕ) (hj : j < N) : regularityForwardWeak (lebesgueC n) O
      (realModelBasis n) q E1 E0 (U j) (U (j+1)) :=
    hodgeClosureGraph_cutoff_forwardWeak g μ hμ (A j) (A (j+1))
      (hA j (by omega)) (hA (j+1) (by omega)) (hgraph j hj) x b θ hθ hcθ hθO
      hO (subset_closure.trans hOO) hθone
  obtain ⟨J,hJ⟩ := regularityForwardChain_weakJet (lebesgueC n) N (realModelBasis n) q E1 E0
    (fun i j => (hqp i j).1) (fun i j => (hqp i j).2.1)
    (fun r c i => (hp1 r c i).1) (fun r c i => (hp1 r c i).2.1)
    (fun r c => (hp0 r c).1) (fun r c => (hp0 r c).2.1)
    hO hV hcV hVO' ell hell
    (fun z hz ξ => by
      simpa only [q,hθone z hz,one_mul] using hcoercive z (subset_closure hz) ξ)
    U hUL hEdge
  have hcut := regularityWeakJet_compact_cutoff (lebesgueC n) hV (realModelBasis n) N (U 0) J hJ χ hχ hcχ hχV
  have heq : (fun z c => χ z * U 0 z c) =
      fun z c => χ z * hodgeRegularityCoord b (A 0) x z c := by
    funext z c
    by_cases hz : z ∈ tsupport χ
    · have hzO := hVO' (subset_closure (hχV hz))
      simp only [U,hodgeRegularityChartInput,hθone z hzO,one_mul]
    · simp only [image_eq_zero_of_notMem_tsupport hz,zero_mul]
  rw [heq] at hcut
  exact ⟨_,hcut⟩

end Yau.NodeProofs.P06Aux

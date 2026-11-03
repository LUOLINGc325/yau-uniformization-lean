import Yau.Proofs.V03BoundaryTensorTransport
import Yau.Proofs.V03FrameSmooth
import Yau.Proofs.V03LogTrace

/-! The original symbol has smooth circle entries in each actual disc
frame. The proof uses a valid fixed chart near each circle point and the
same ambient frame of the given immersion. -/

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem closedDisc_scalar_trace_contDiff {H : ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (Metric.closedBall (0 : ℂ) 1)) :
    ContDiff ℝ ∞ (fun θ => H (circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hh := (hH.restrict_scalars ℝ _ (circlePoint_mem_closedBall θ)).comp θ
    circlePoint_contDiff.contDiffAt.contDiffWithinAt
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall t)
  exact contDiffWithinAt_univ.mp hh

variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_discTime_trace_contDiff {d : VariationData X q} {j : ℕ}
    {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiff ℝ ∞ (fun θ => discTime F (circlePoint θ)) := by
  have hw := closedDisc_scalar_trace_contDiff hF.2.1
  exact contDiff_const.mul
    ((contDiff_const.mul (Complex.reCLM.contDiff.comp hw)).exp)

theorem boundarySymbol_trace_contDiff {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E)
    (i l : CotangentIndex n) :
    ContDiff ℝ ∞ (fun θ => boundarySymbol d j a F E (circlePoint θ) i l) := by
  have hA (b : Fin q) (k : CotangentIndex n) :
      ContDiff ℝ ∞ (fun θ => ambientFrame d.G F.f E (circlePoint θ) b k) :=
    closedDisc_scalar_trace_contDiff (ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 b k)
  have htime := admissible_discTime_trace_contDiff hF
  rw [contDiff_iff_contDiffAt]
  intro θ₀
  let x := (F.f (circlePoint θ₀)).1
  have hself : F.f (circlePoint θ₀) ∈ cotangentSource x := mem_extChartAt_source x
  have hz : cotangentChart x (F.f (circlePoint θ₀)) ∈ cotangentTarget x :=
    cotangentChart_mapsTo x hself
  have hcoord : ContDiffAt ℝ ∞ (fun θ => cotangentChart x (F.f (circlePoint θ))) θ₀ := by
    have hc := ((cotangentDisc_coords_contDiffWithinAt hF.1
      (circlePoint_mem_closedBall θ₀) x hself).restrict_scalars ℝ).comp θ₀
      circlePoint_contDiff.contDiffAt.contDiffWithinAt
      (fun θ (_ : θ ∈ (Set.univ : Set ℝ)) => circlePoint_mem_closedBall θ)
    exact contDiffWithinAt_univ.mp hc
  let p : ℝ → (CotangentCoord n × ℝ) × ℝ :=
    fun θ => ((cotangentChart x (F.f (circlePoint θ)), discTime F (circlePoint θ)), F.s)
  have hmap : ContDiffAt ℝ ∞ p θ₀ := (hcoord.prodMk htime.contDiffAt).prodMk contDiffAt_const
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ₀)
  have htext : discTime F (circlePoint θ₀) < d.extendedT := ht.2.trans hd.2.1
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hdom : ((cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) ×ˢ Set.univ) ∈ 𝓝 (p θ₀) :=
    prod_mem_nhds (prod_mem_nhds (hopen.mem_nhds hz) (Icc_mem_nhds ht.1 htext)) Filter.univ_mem
  have hB (b c : Fin q) : ContDiffAt ℝ ∞
      (fun θ => fixedAmbientBoundaryTensor d j a x (p θ) b c) θ₀ :=
    ((fixedAmbientBoundaryTensor_entry_contDiffOn hd j a x b c).contDiffAt hdom).comp θ₀ hmap
  have hmodel : ContDiffAt ℝ ∞ (fun θ =>
      ((ambientFrame d.G F.f E (circlePoint θ))ᴴ *
        fixedAmbientBoundaryTensor d j a x (p θ) * ambientFrame d.G F.f E (circlePoint θ)) i l) θ₀ := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply ContDiffAt.sum
    intro c _
    apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro b _
      exact ((Complex.conjCLE.contDiff.contDiffAt.comp θ₀ (hA b i).contDiffAt).mul (hB b c))
    · exact (hA c l).contDiffAt
  have hbase : Continuous (fun θ => (F.f (circlePoint θ)).1) :=
    hF.1.1.continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hsource : ∀ᶠ θ in 𝓝 θ₀, F.f (circlePoint θ) ∈ cotangentSource x :=
    hbase.continuousAt.eventually ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds hself)
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [hsource] with θ hθ
  exact congrFun (congrFun (boundarySymbol_eq_fixedAmbientBoundaryTensor hd j a ha F hF E θ x hθ) i) l

end Yau.Blueprint.V04Proof

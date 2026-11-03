import Yau.Proofs.F05PositiveOpenCharts
import Yau.Proofs.F05ChartRegularity

/-! Joint smoothness in an actual flattened chart gives the literal
centered-chart SmoothNear predicate used by viscosity comparison. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_flat_smoothNear_to_manifold {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) (w : M.Carrier → ℝ → ℝ)
    {z : Space n} {t : ℝ} (hz : z ∈ Metric.ball 0 3)
    (hSmooth : ContDiffAt ℝ ∞ (pull A i w) (z,t)) : SmoothNear w (lift A i z) t := by
  let x := lift A i z
  let c := A.center i
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) c).symm
  let q : Space n → Space n := fun y => chartPt c (chartInv x y)
  have hRawTarget : A.inverse i z ∈ chartTarget c :=
    (hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩)
  have hxE : x ∈ e.target := by
    simpa [x,lift,e,c,chartInv,ComplexModel,extChartAt] using
      (extChartAt (ComplexModel n) c).map_target hRawTarget
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt (I := ComplexModel n) (x := c))
  have hCenter : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hMem : chartPt x x ∈ inverseChartDomain e x := by
    refine ⟨mem_extChartAt_target x,?_⟩
    change chartInv x (chartPt x x) ∈ e.target
    rwa [hCenter]
  have hDomain := (inverseChartDomain_isOpen e x).mem_nhds hMem
  have hQ : ContDiffAt ℝ ∞ q (chartPt x x) := by
    simpa [q,e,chartPt,ComplexModel] using
      (inverseChart_real_contDiffOn e he x).contDiffAt hDomain
  have hQValue : q (chartPt x x) = A.inverse i z := by
    dsimp only [q]
    rw [hCenter]
    exact (extChartAt (ComplexModel n) c).right_inv hRawTarget
  have hSource : A.inverse i z ∈ A.source i := (hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩
  have hF : ContDiffAt ℝ ∞ (A.forward i) (q (chartPt x x)) := by
    rw [hQValue]
    exact ((hA.1 i).2.2.1).contDiffAt ((hA.1 i).1.mem_nhds hSource)
  let ψ : Point n → Point n := fun p => (A.forward i (q p.1),p.2)
  have hForwardQ : ContDiffAt ℝ ∞ (fun y => A.forward i (q y)) (chartPt x x) := hF.comp _ hQ
  have hψ : ContDiffAt ℝ ∞ ψ (chartPt x x,t) :=
    (hForwardQ.comp (chartPt x x,t) contDiffAt_fst).prodMk contDiffAt_snd
  have hψValue : ψ (chartPt x x,t) = (z,t) := by
    change (A.forward i (q (chartPt x x)),t) = (z,t)
    rw [hQValue,(hA.1 i).2.2.2.2.2.1 z hz]
  have hComp : ContDiffAt ℝ ∞ ((pull A i w) ∘ ψ) (chartPt x x,t) := by
    apply ContDiffAt.comp _ _ hψ
    rwa [hψValue]
  change ContDiffAt ℝ ∞ (fun p : Point n => w (chartInv x p.1) p.2) (chartPt x x,t)
  apply hComp.congr_of_eventuallyEq
  have hQNear : ∀ᶠ y in 𝓝 (chartPt x x), q y ∈ A.source i :=
    hQ.continuousAt.eventually (by rw [hQValue]; exact (hA.1 i).1.mem_nhds hSource)
  have hQNearProd : ∀ᶠ p : Point n in 𝓝 (chartPt x x,t), q p.1 ∈ A.source i :=
    (continuous_fst.continuousAt : ContinuousAt (fun p : Point n => p.1) (chartPt x x,t)).eventually hQNear
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hDomain,hQNearProd] with p hpDomain hpQ
  change w (chartInv x p.1) p.2 =
    w (chartInv c (A.inverse i (A.forward i (q p.1)))) p.2
  rw [(hA.1 i).2.2.2.2.2.2.1 (q p.1) hpQ]
  apply congrArg (fun y => w y p.2)
  symm
  exact (extChartAt (ComplexModel n) c).left_inv (by
    simpa [e,ComplexModel,extChartAt] using hpDomain.2)

theorem F05_open_charts_smoothNear {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (w : M.Carrier → ℝ → ℝ) {T : ℝ}
    (hSmooth : ∀ i, ContDiffOn ℝ ∞ (pull A i w)
      ((F05ModelOpen A i ∩ Metric.ball 0 3) ×ˢ Ioc 0 T)) :
    ∀ x ∈ O, ∀ t ∈ Ioo 0 T, SmoothNear w x t := by
  intro x hx t ht
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA (subset_closure hx)
  have hz3 := F05D_mem_ball hz
  have hPhysical := ((hA.1 i).2.2.2.2.2.2.2 z hz3).1
  have hzOpen : z ∈ F05ModelOpen A i := by
    have hh := hPhysical.mp (by rwa [hzx])
    cases hν : A.normal i with
    | none => simp [F05ModelOpen,hν]
    | some j => simpa only [F05ModelOpen,hν,mem_ofPred_eq] using hh
  have hSpace : IsOpen (F05ModelOpen A i ∩ Metric.ball 0 3) := by
    rw [F05ModelOpen_eq]
    exact (F05FlatOpen_isOpen _).inter Metric.isOpen_ball
  have hAt : ContDiffAt ℝ ∞ (pull A i w) (z,t) :=
    (hSmooth i).contDiffAt (prod_mem_nhds (hSpace.mem_nhds ⟨hzOpen,hz3⟩) (Ioc_mem_nhds ht.1 ht.2))
  rw [← hzx]
  exact F05_flat_smoothNear_to_manifold hA i w hz3 hAt

end Yau.Proofs.F05Aux

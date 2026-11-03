import Yau.Proofs.F05BufferedChart
import Yau.Proofs.F05AtlasModel

/-! Interior points have smooth physical charts with the same fixed target buffer. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic
variable {n : ℕ} {M : ComplexManifold n}

theorem open_buffered_interior_chart {O : Set M.Carrier} (hO : IsOpen O)
    {p : M.Carrier} (hp : p ∈ O) :
    ∃ c : OpenPartialHomeomorph (Space n) (Space n),
      chartPt p p ∈ c.source ∧ c (chartPt p p) = 0 ∧ c.source ⊆ chartTarget p ∧
      Metric.closedBall 0 4 ⊆ c.target ∧ ContDiffOn ℝ ∞ c c.source ∧
      ContDiffOn ℝ ∞ c.symm c.target ∧ ∀ z ∈ c.source, chartInv p z ∈ O := by
  let a : OpenPartialHomeomorph M.Carrier (Space n) := chartAt (Space n) p
  have haPt : (a : M.Carrier → Space n) = chartPt p := by
    funext y
    simp [a,chartPt,ComplexModel]
  have haInv : (a.symm : Space n → M.Carrier) = chartInv p := by
    funext z
    simp [a,chartInv,ComplexModel]
  let V := a.target ∩ a.symm ⁻¹' O
  have hV : IsOpen V := a.symm.isOpen_inter_preimage hO
  let z₀ := a p
  have hz₀ : z₀ ∈ V :=
    ⟨a.map_source (mem_chart_source (Space n) p),by
      change a.symm (a p) ∈ O
      rwa [a.left_inv (mem_chart_source (Space n) p)]⟩
  let c₀ := (OpenPartialHomeomorph.ofSet V hV).trans
    (Homeomorph.addRight (-z₀)).toOpenPartialHomeomorph
  have hc₀source : c₀.source = V := by
    change V ∩ (fun z : Space n => z) ⁻¹' univ = V
    simp only [preimage_univ,inter_univ]
  have hc₀point : z₀ ∈ c₀.source := by rwa [hc₀source]
  have hc₀zero : c₀ z₀ = 0 := by
    change z₀ + (-z₀) = 0
    exact add_neg_cancel _
  have hc₀ : ContDiffOn ℝ ∞ c₀ c₀.source := by
    change ContDiffOn ℝ ∞ (fun z : Space n => z + (-z₀)) c₀.source
    fun_prop
  have hci₀ : ContDiffOn ℝ ∞ c₀.symm c₀.target := by
    change ContDiffOn ℝ ∞ (fun z : Space n => z - (-z₀)) c₀.target
    fun_prop
  obtain ⟨q,c,hq,hsource,hbuffer,hcenter,hforward,hinverse,hc,hci⟩ :=
    buffered_smooth_chart c₀ hc₀point hc₀zero hc₀ hci₀
  have hcoords : chartPt p p = z₀ := (congrFun haPt p).symm
  have hcV : c.source = V := hsource.trans hc₀source
  refine ⟨c,?_,?_,?_,hbuffer,hc,hci,?_⟩
  · rw [hcoords]
    rwa [hsource]
  · rwa [hcoords]
  · intro z hz
    have hzV : z ∈ V := by rwa [← hcV]
    have hzTarget := hzV.1
    simpa [a,chartTarget,ComplexModel] using hzTarget
  · intro z hz
    have hzV : z ∈ V := by rwa [← hcV]
    have hzO := hzV.2
    rwa [haInv] at hzO

end Yau.Proofs.F05Aux

import Yau.Proofs.E02ProductDomain
import Yau.Proofs.E02JensenExtension

open Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The actual physical C² comparison cost is extended after real
packing, without changing its values near the whole evaluation compactum. -/
theorem exists_packed_product_cost_extension {n m : ℕ}
    (f : ComplexVector n × ℝ → ℝ) (α : Fin m → ℝ) (P₀ : Herm m) (θ : ℝ)
    (V : Set (ComplexVector n × ℝ)) (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V)
    (O : Set (ProductPoint n m)) (hOC : IsCompact (closure O))
    (hOU : closure O ⊆ productOpenDomain α V) :
    ∃ (g : EuclideanSpace ℝ (Fin (2*n+1+2*n*m)) → ℝ) (C : ℝ)
      (W : Set (EuclideanSpace ℝ (Fin (2*n+1+2*n*m)))),
      IsOpen W ∧ closure ((productRealCoordinates n m) '' O) ⊆ W ∧
      EqOn g (productCostPacked f α P₀ θ) W ∧ ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      0 < C ∧ ConvexOn ℝ univ (fun Q => g Q+C*(‖Q‖^2/2)) := by
  let e := productRealCoordinates n m
  let U := productOpenDomain α V
  have hU : IsOpen U := isOpen_productOpenDomain α V hV
  have hImage : closure (e '' O) = e '' closure O := (e.toHomeomorph.image_closure O).symm
  have hK : IsCompact (closure (e '' O)) := by
    rw [hImage]
    exact hOC.image e.continuous
  have hKU : closure (e '' O) ⊆ e '' U := by
    rw [hImage]
    exact image_mono hOU
  have hCost : ContDiffOn ℝ 2 (productCostPacked f α P₀ θ) (e '' U) :=
    (productCostPhysical_contDiffOn_domain f V hV hf α P₀ θ).comp e.symm.contDiff.contDiffOn
      (by rintro Q ⟨p,hp,rfl⟩; simpa only [e,U,ContinuousLinearEquiv.symm_apply_apply] using hp)
  obtain ⟨W,g,C,hW,hKW,_hWU,hg,hgC,hEq,hC,hConv,_hDerivs⟩ :=
    exists_jensen_C2_extension (closure (e '' O)) (e '' U) hK (e.isOpenMap U hU) hKU
      (productCostPacked f α P₀ θ) hCost
  exact ⟨g,C,W,hW,hKW,hEq,hg,hgC,hC,hConv⟩

/-- Local minima are transported back from the extension to the actual
cost on the open agreement region; no derivative of uκ is asserted. -/
theorem localMin_sub_cost_of_eqOn {E : Type*} [TopologicalSpace E]
    (F g g' slope : E → ℝ) (W : Set E) (hW : IsOpen W) (q : E) (hq : q ∈ W)
    (hEq : EqOn g g' W)
    (hMin : IsLocalMin (fun R => F R-g R-slope R) q) :
    IsLocalMin (fun R => F R-g' R-slope R) q := by
  filter_upwards [hMin,hW.mem_nhds hq] with R hR hRW
  rw [←hEq hq,←hEq hRW]
  exact hR

end Yau.NodeProofs.E02Aux

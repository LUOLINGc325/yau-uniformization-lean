import Yau.Proofs.V02FlowFields

/-! Smooth actual native charts and transport of actual curve equations. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem nativeCotangentChart_contMDiffOn (x : M.Carrier) :
    ContMDiffOn 𝓘(ℂ, CotangentCoord n) 𝓘(ℂ, CotangentCoord n) ∞
      (fun y : NativeCotangentPoint M => cotangentChart x y.val)
      {y | y.val ∈ cotangentSource x} := by
  exact contMDiffOn_extChartAt (I := 𝓘(ℂ, CotangentCoord n))
    (x := NativeCotangentPoint.mk (x, 0))

theorem nativeCotangentChartInv_contMDiffOn (x : M.Carrier) :
    ContMDiffOn 𝓘(ℂ, CotangentCoord n) 𝓘(ℂ, CotangentCoord n) ∞
      (fun z => NativeCotangentPoint.mk (cotangentChartInv x z)) (cotangentTarget x) := by
  have h := contMDiffOn_extChartAt_symm (I := 𝓘(ℂ, CotangentCoord n)) (n := ∞)
    (NativeCotangentPoint.mk (x, 0))
  simp only [extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.preimage_id, Set.range_id, Set.inter_univ] at h
  change ContMDiffOn 𝓘(ℂ, CotangentCoord n) 𝓘(ℂ, CotangentCoord n) ∞
    (fun z => NativeCotangentPoint.mk (cotangentChartInv x z)) (cotangentTarget x) at h
  exact h

def nativeCotangentChartBall (x : M.Carrier) (a : CotangentCoord n) (r : ℝ) :
    Set (NativeCotangentPoint M) :=
  (nativeCotangentChartHomeomorph x).symm '' ball a r

theorem nativeCotangentChartBall_isOpen {x : M.Carrier} {a : CotangentCoord n} {r : ℝ}
    (hball : ball a r ⊆ cotangentTarget x) : IsOpen (nativeCotangentChartBall x a r) :=
  (nativeCotangentChartHomeomorph x).isOpen_image_symm_of_subset_target isOpen_ball hball

theorem nativeCotangentChartBall_mem_iff {x : M.Carrier} {a : CotangentCoord n} {r : ℝ}
    (hball : ball a r ⊆ cotangentTarget x) {y : NativeCotangentPoint M} :
    y ∈ nativeCotangentChartBall x a r ↔
      y.val ∈ cotangentSource x ∧ cotangentChart x y.val ∈ ball a r := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨cotangentChartInv_mapsTo x (hball hz), by
      change cotangentChart x (cotangentChartInv x z) ∈ ball a r
      rwa [cotangentChart_right_inv x (hball hz)]⟩
  · rintro ⟨hs, hb⟩
    exact ⟨cotangentChart x y.val, hb, NativeCotangentPoint.ext (cotangentChart_left_inv x hs)⟩

theorem nativeCurve_coordinate_hasDerivAt_transport
    {Z : CotangentPoint M → CotangentIndex n → ℂ}
    {γ : ℂ → NativeCotangentPoint M} {t : ℂ} (hγ : ContinuousAt γ t)
    (x x' : M.Carrier) (hx : (γ t).val ∈ cotangentSource x)
    (hx' : (γ t).val ∈ cotangentSource x')
    (hd : HasDerivAt (fun z => cotangentChart x (γ z).val)
      (cotangentChartField Z x (cotangentChart x (γ t).val)) t) :
    HasDerivAt (fun z => cotangentChart x' (γ z).val)
      (cotangentChartField Z x' (cotangentChart x' (γ t).val)) t := by
  have hb : chartInv x (cotangentChart x (γ t).val).1 = (γ t).val.1 :=
    (extChartAt (ComplexModel n) x).left_inv hx
  have hT := cotangentChartTransition_contDiffAt x x'
    (cotangentChart_mapsTo x hx) (by rw [hb]; exact hx')
  have hcomp := (hT.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hd
  rw [cotangentChartField_transport Z x x' (γ t).val hx hx'] at hcomp
  apply hcomp.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 t, (γ z).val ∈ cotangentSource x :=
    hγ.preimage_mem_nhds
      ((nativeCotangentChartHomeomorph x).open_source.mem_nhds hx)
  filter_upwards [hnear] with z hz
  exact (congrArg (cotangentChart x') (cotangentChart_left_inv x hz)).symm

def NativeFieldIntegralCurve (Z : CotangentPoint M → CotangentIndex n → ℂ)
    (γ : ℂ → NativeCotangentPoint M) (D : Set ℂ) : Prop :=
  ContinuousOn γ D ∧ ∀ t ∈ D, ∀ x, (γ t).val ∈ cotangentSource x →
    HasDerivAt (fun z => cotangentChart x (γ z).val)
      (cotangentChartField Z x (cotangentChart x (γ t).val)) t

end Yau.Blueprint.V02FlowProof

import Yau.Proofs.E02CompactExtension
import Yau.Proofs.E02HessianConvex

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.NodeProofs.E02Aux

/-- The actual finite C² extension needed in Jensen's argument, with a
global quadratic bound and exactly the original derivatives near K. -/
theorem exists_jensen_C2_extension {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (K U : Set E) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → ℝ) (hf : ContDiffOn ℝ 2 f U) :
    ∃ (V : Set E) (F : E → ℝ) (C : ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContDiff ℝ 2 F ∧ HasCompactSupport F ∧ EqOn F f V ∧ 0 < C ∧
      ConvexOn ℝ univ (fun x => F x+C*(‖x‖^2/2)) ∧
      ∀ x ∈ V, fderiv ℝ F x = fderiv ℝ f x ∧
        fderiv ℝ (fderiv ℝ F) x = fderiv ℝ (fderiv ℝ f) x := by
  obtain ⟨V,F,hV,hKV,hVU,hF,hFC,hEq⟩ := exists_compact_C2_extension K U hK hU hKU f hf
  obtain ⟨C,hC,hBound⟩ := compact_C2_second_fderiv_bounded F hF hFC
  refine ⟨V,F,C,hV,hKV,hVU,hF,hFC,hEq,hC,
    convexOn_add_quadratic_of_second_fderiv_bound F hF C hBound,?_⟩
  intro x hx
  have hNear : F =ᶠ[𝓝 x] f := Filter.eventuallyEq_iff_exists_mem.mpr ⟨V,hV.mem_nhds hx,hEq⟩
  exact ⟨hNear.fderiv_eq,hNear.fderiv.fderiv_eq⟩

end Yau.NodeProofs.E02Aux

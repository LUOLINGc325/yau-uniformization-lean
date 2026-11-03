import Yau.Proofs.V03JointGaussTwoFormSmooth
import Yau.Proofs.V03ScalarLeviClosed

/-! The genuine intrinsic Gauss two-form is closed at every interior
parameter point: locally it is exactly the native scalar Levi two-form. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

theorem jointGaussTwoForm_closed {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) (hS : UniqueDiffOn ℂ S)
    {p : P} (hp : p ∈ interior S) :
    extDeriv (jointGaussTwoForm G f S) p = 0 := by
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p (interior_subset hp)
  let W : Set P := interior S ∩ V
  have hW : IsOpen W := isOpen_interior.inter hV
  have hpW : p ∈ W := ⟨hp, hpV⟩
  have hsub : W ⊆ S ∩ V := fun r hr => ⟨interior_subset hr.1, hr.2⟩
  let c : P → CotangentCoord n := fun r => cotangentChart (f p).1 (f r)
  have hc : ContDiffOn ℂ ∞ c W := hcoord.mono hsub
  have hopen : IsOpen (cotangentTarget (f p).1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) (f p).1).prod isOpen_univ
  have hpot : ContDiffOn ℝ ∞ (gaussPotential G (f p).1) (cotangentTarget (f p).1) :=
    fun z hz => (gaussPotential_contDiffAt hG (f p).1 hz).contDiffWithinAt
  have hmap : Set.MapsTo c W (cotangentTarget (f p).1) :=
    fun r hr => cotangentChart_mapsTo (f p).1 (hsource r (hsub hr))
  have hcomp : ContDiffOn ℝ ∞ (fun r => gaussPotential G (f p).1 (c r)) W :=
    hpot.comp (hc.restrict_scalars ℝ) hmap
  have heq : jointGaussTwoForm G f S =ᶠ[𝓝 p]
      scalarLeviTwoForm (fun r => gaussPotential G (f p).1 (c r)) := by
    filter_upwards [hW.mem_nhds hpW] with r hr
    rw [jointGaussTwoForm_eq_fixed_chart hG hf (hsub hr).1 (hS r (hsub hr).1)
      (f p).1 (hsource r (hsub hr))]
    have hSn : S ∈ 𝓝 r := mem_of_superset (isOpen_interior.mem_nhds hr.1) interior_subset
    rw [fderivWithin_of_mem_nhds hSn]
    exact (scalarLeviTwoForm_holomorphic_comp
      ((hc.contDiffAt (hW.mem_nhds hr)).of_le (by simp))
      ((hpot.contDiffAt (hopen.mem_nhds (hmap hr))).of_le (by simp))).symm
  rw [heq.extDeriv_eq]
  exact scalarLeviTwoForm_closed hW hcomp hpW

end Yau.Blueprint.V03Proof

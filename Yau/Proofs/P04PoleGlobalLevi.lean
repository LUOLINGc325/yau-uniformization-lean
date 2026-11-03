import Yau.Proofs.P04LeviSemipositive
import Yau.Proofs.P04PoleChartValues

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine smooth zero extension transports a model Levi lower bound to
the whole manifold, including points outside the original chart source. -/
theorem pole_extension_global_semipositive (p : M.Carrier)
    {ψ P : M.Carrier → ℝ} (hψ : IsSmoothStrictPsh ψ) (hP : SmoothFn P)
    (hs : tsupport P ⊆ (extChartAt (ComplexModel n) p).source)
    {k : ℝ} (hk : 1 ≤ k)
    (hlocal : ∀ z ∈ chartTarget p,
      (leviC (inChart p (fun x => (k-1)*ψ x+P x)) z).PosSemidef) :
    ∀ x, (levi (fun y => (k-1)*ψ y+P y) x).PosSemidef := by
  let F : M.Carrier → ℝ := fun y => (k-1)*ψ y+P y
  have hF : SmoothFn F := fun a => (contDiffOn_const.mul (hψ.1 a)).add (hP a)
  intro x
  by_cases hx : x ∈ (extChartAt (ComplexModel n) p).source
  · have hi : chartInv x (chartPt x x)=x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    apply levi_inChart_posSemidef_of_overlap hF x p (z := chartPt x x)
      ((extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x))
      (by rwa [hi])
    simpa only [hi] using hlocal (chartPt p x)
      ((extChartAt (ComplexModel n) p).map_source hx)
  · have hzero : P =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hs h))
    have heq : F =ᶠ[𝓝 x] (fun y => (k-1)*ψ y) := by
      filter_upwards [hzero] with y hy
      simp only [F,hy,add_zero]
    have hψx : ContDiffAt ℝ 2 (inChart x ψ) (chartPt x x) :=
      ((hψ.1 x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds
        ((extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)))).of_le (by simp)
    change (levi F x).PosSemidef
    rw [L22Aux.levi_congr_of_eventuallyEq heq]
    change (leviC (fun z => (k-1)*inChart x ψ z) (chartPt x x)).PosSemidef
    rw [L17Aux.leviC_const_mul hψx (k-1)]
    exact (hψ.2 x).posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hk))

/-- Adding back the original strictly positive Levi form gives actual strict
plurisubharmonicity; no chart positivity is added as an independent premise. -/
theorem strictPsh_of_positive_background {ψ P : M.Carrier → ℝ}
    (hψ : IsSmoothStrictPsh ψ) (hP : SmoothFn P) (k : ℝ)
    (hpos : ∀ x, (levi (fun y => (k-1)*ψ y+P y) x).PosSemidef) :
    IsSmoothStrictPsh (fun y => k*ψ y+P y) := by
  have hF : SmoothFn (fun y => (k-1)*ψ y+P y) :=
    fun a => (contDiffOn_const.mul (hψ.1 a)).add (hP a)
  refine ⟨fun a => (contDiffOn_const.mul (hψ.1 a)).add (hP a),fun x => ?_⟩
  have htarget := (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have hFx : ContDiffAt ℝ 2 (inChart x (fun y => (k-1)*ψ y+P y)) (chartPt x x) :=
    ((hF x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds htarget)).of_le (by simp)
  have hψx : ContDiffAt ℝ 2 (inChart x ψ) (chartPt x x) :=
    ((hψ.1 x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds htarget)).of_le (by simp)
  have heq : (fun y => k*ψ y+P y)=(fun y => ((k-1)*ψ y+P y)+ψ y) := by
    funext y
    ring
  rw [heq]
  change (leviC (fun z => inChart x (fun y => (k-1)*ψ y+P y) z+inChart x ψ z)
    (chartPt x x)).PosDef
  rw [L17Aux.leviC_add hFx hψx]
  exact Matrix.PosDef.posSemidef_add (hpos x) (hψ.2 x)

end Yau.Proofs.P04Aux

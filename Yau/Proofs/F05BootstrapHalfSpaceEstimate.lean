import Yau.Proofs.F05BootstrapHalfSpaceUniqueness
import Yau.Proofs.F05BootstrapRelativeCongruence
import Yau.Proofs.F05BootstrapRestrictions
import Yau.LeafProofs.L16HalfSpaceHolderInverse

/-! The native Hölder-only inverse and proved bounded relative uniqueness
give an estimate for every actual bounded relative classical solution. No
coefficient Lipschitz bound or prior finite Schauder norm is assumed. -/

open Set Filter
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_halfSpace_uniqueDiffOn {e : Space n} (he : ‖e‖ = 1) :
    UniqueDiffOn ℝ {x | 0 ≤ inner ℝ e x} := by
  have hOpen : IsOpen {x : Space n | 0 < inner ℝ e x} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hePos : 0 < inner ℝ e e := by rw [real_inner_self_eq_norm_sq,he]; norm_num
  apply uniqueDiffOn_convex (convex_halfSpace_ge (innerSL ℝ e).toLinearMap.isLinear 0)
  refine ⟨e,mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset (hOpen.mem_nhds hePos)
    (fun x hx => (show 0 < inner ℝ e x from hx).le)

theorem F05_relative_halfSpace_classical_estimate {α M lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (e : Space n) (he : ‖e‖ = 1)
    {K : Set (Space n)} (hK : IsCompact K) (hKH : K ⊆ {x | 0 ≤ inner ℝ e x}) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a M →
      (∀ j, HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun z => b z j) M) →
      Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper →
      (∀ z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, z.1 ∉ K → a z = 1) →
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) →
      F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) u →
      (∀ z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |u z| ≤ B) →
      (∀ x, 0 ≤ inner ℝ e x → u (x,0) = 0) →
      (∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) →
      (∀ z ∈ {x | 0 < inner ℝ e x} ×ˢ Ioc 0 T,
        F05RelOp {x | 0 ≤ inner ℝ e x} (Icc 0 T) a b u z = f z) →
      F05RelSchauder α {x | 0 ≤ inner ℝ e x} (Icc 0 T) u (C*F) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hInverse⟩ :=
    halfSpaceHolderInverse_exists_uniform_short (M := M) (lam := lam) (upper := upper)
      hα hα1 e he hK hKH
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro T a b f u F B hT hTδ ha hb hEll hExterior hf hCorner hu hUBound hInit hFace hPDE
  obtain ⟨v,hv,hvLow,hvInit,hvFace,hvPDE⟩ :=
    hInverse T a b hT hTδ ha hb hEll hExterior f F hf hCorner
  have hUnique := F05_halfSpace_uniqueDiffOn he
  have hNative : SchauderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v (C*F) :=
    Yau.LeafProofs.L16BoundaryTimeAux.schauderBound_mono_space (subset_univ _) hv
  have hHigh := F05_native_schauder_relative_high hUnique hNative
  have hLow : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T)
      (fun z => (v z,F05RelD {x | 0 ≤ inner ℝ e x} v z)) (C*F) := by
    apply holderBound_congr_on (holderBound_mono hvLow
      (show cylinder {x | 0 ≤ inner ℝ e x} 0 T ⊆ cylinder univ 0 T from
        fun z hz => ⟨mem_univ _,hz.2⟩))
    intro z hz
    change (v z,spatialD v z) = (v z,F05RelD {x | 0 ≤ inner ℝ e x} v z)
    rw [F05RelD_eq_spatialD (hUnique z.1 hz.1)
      ((hNative.1.2.2.2.2.1 z hz).differentiableAt (by norm_num))]
  have hvRel : F05RelSchauder α {x | 0 ≤ inner ℝ e x} (Icc 0 T) v (C*F) :=
    ⟨hHigh.1,hLow,hHigh.2.2.1,hHigh.2.2.2⟩
  have hEq : EqOn v u (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
    apply F05_relative_bounded_halfSpace_unique he hT hvRel.1 hu hEll ha.1
      (fun z hz j => by simpa only [Real.norm_eq_abs] using (hb j).2.1 z hz)
      (B := C*F) (C := B)
      (fun z hz => (hNative.2.2.1 z hz).1) hUBound
      (fun x hx => by rw [hvInit x,hInit x hx])
      (fun x hx t ht => by rw [hvFace x hx t ht,hFace x hx t ht])
    intro z hz
    have hzQ : z ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
      ⟨(show 0 < inner ℝ e z.1 from hz.1).le,hz.2.1.le,hz.2.2⟩
    rw [F05RelOp_eq_linearOp hUnique hNative.1 a b hzQ,hvPDE z hzQ,hPDE z hz]
  exact F05_relative_schauder_congr hvRel hEq

end Yau.Proofs.F05Aux

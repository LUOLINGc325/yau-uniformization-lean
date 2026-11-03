import Yau.Proofs.F05BootstrapHalfSpaceComparison
import Yau.Proofs.F05BootstrapRelativeExtension

/-! Both native and genuinely relative bounded solutions are unique on the
same physical half-space. Only the original physical-side equation is used. -/

open Set
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_bounded_halfSpace_unique {e : Space n} (he : ‖e‖ = 1)
    {T lam upper M B C : ℝ} {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u v : Point n → ℝ} (hT : 0 < T)
    (hu : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) u)
    (hv : C2 (cylinder {x | 0 ≤ inner ℝ e x} 0 T) v)
    (hEll : Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ∀ i, |b p i| ≤ M)
    (hUBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |u p| ≤ B)
    (hVBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |v p| ≤ C)
    (hInit : ∀ x, 0 ≤ inner ℝ e x → u (x,0) = v (x,0))
    (hFace : ∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = v (x,t))
    (hOp : ∀ p ∈ {x | 0 < inner ℝ e x} ×ˢ Ioc 0 T,
      linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b u p =
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a b v p) :
    EqOn u v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  have hForward := F05_bounded_halfSpace_subsolution_bound he hT (c2_sub hu hv) hEll hM hb
    (B := B+C) (F := 0)
    (fun p hp => (le_abs_self _).trans ((abs_sub _ _).trans
      (add_le_add (hUBound p hp) (hVBound p hp))))
    (fun x hx => by rw [hInit x hx,sub_self])
    (fun x hx t ht => by rw [hFace x hx t ht,sub_self]) (by norm_num) (by
      intro p hp
      have hpQ : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
        ⟨(show 0 < inner ℝ e p.1 from hp.1).le,hp.2.1.le,hp.2.2⟩
      rw [linearOp_sub (a := a) (b := b) hu hv hpQ,hOp p hp,sub_self])
  have hBackward := F05_bounded_halfSpace_subsolution_bound he hT (c2_sub hv hu) hEll hM hb
    (B := C+B) (F := 0)
    (fun p hp => (le_abs_self _).trans ((abs_sub _ _).trans
      (add_le_add (hVBound p hp) (hUBound p hp))))
    (fun x hx => by rw [hInit x hx,sub_self])
    (fun x hx t ht => by rw [hFace x hx t ht,sub_self]) (by norm_num) (by
      intro p hp
      have hpQ : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
        ⟨(show 0 < inner ℝ e p.1 from hp.1).le,hp.2.1.le,hp.2.2⟩
      rw [linearOp_sub (a := a) (b := b) hv hu hpQ,hOp p hp,sub_self])
  intro p hp
  have hF := hForward p hp
  have hB := hBackward p hp
  simp only [mul_zero] at hF hB
  linarith

theorem F05_relative_bounded_halfSpace_unique {e : Space n} (he : ‖e‖ = 1)
    {T lam upper M B C : ℝ} {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {u v : Point n → ℝ} (hT : 0 < T)
    (hu : F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) u)
    (hv : F05RelC2 {x | 0 ≤ inner ℝ e x} (Icc 0 T) v)
    (hEll : Elliptic (cylinder {x | 0 ≤ inner ℝ e x} 0 T) a lam upper) (hM : 0 ≤ M)
    (hb : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, ∀ i, |b p i| ≤ M)
    (hUBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |u p| ≤ B)
    (hVBound : ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T, |v p| ≤ C)
    (hInit : ∀ x, 0 ≤ inner ℝ e x → u (x,0) = v (x,0))
    (hFace : ∀ x, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = v (x,t))
    (hOp : ∀ p ∈ {x | 0 < inner ℝ e x} ×ˢ Ioc 0 T,
      F05RelOp {x | 0 ≤ inner ℝ e x} (Icc 0 T) a b u p =
        F05RelOp {x | 0 ≤ inner ℝ e x} (Icc 0 T) a b v p) :
    EqOn u v (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  obtain ⟨hU,hUValue,hUD,hUDD,hUT⟩ := F05_relative_halfSpace_extension he hT hu
  obtain ⟨hV,hVValue,hVD,hVDD,hVT⟩ := F05_relative_halfSpace_extension he hT hv
  have hEq := F05_bounded_halfSpace_unique he hT
    (c2_cylinder_restrict_space hU) (c2_cylinder_restrict_space hV) hEll hM hb
    (fun p hp => by rw [hUValue hp]; exact hUBound p hp)
    (fun p hp => by rw [hVValue hp]; exact hVBound p hp)
    (fun x hx => by
      have hxQ : ((x,0) : Point n) ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
        ⟨hx,le_rfl,hT.le⟩
      rw [hUValue hxQ,hVValue hxQ,hInit x hx])
    (fun x hx t ht => by
      have hxH : 0 ≤ inner ℝ e x := hx.ge
      have hxQ : ((x,t) : Point n) ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T := ⟨hxH,ht⟩
      rw [hUValue hxQ,hVValue hxQ,hFace x hx t ht]) (by
      intro p hp
      have hpQ : p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T :=
        ⟨(show 0 < inner ℝ e p.1 from hp.1).le,hp.2.1.le,hp.2.2⟩
      rw [F05_relative_extension_operator he hT hu a b hpQ,
        F05_relative_extension_operator he hT hv a b hpQ,hOp p hp])
  intro p hp
  exact (hUValue hp).symm.trans ((hEq hp).trans (hVValue hp))

end Yau.Proofs.F05Aux

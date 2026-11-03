import Yau.Blueprint.Nodes
import Yau.Proofs.U02AnalyticManifold

/-! Construction of the exact open-image record from the coordinate map.
All data below use the map and inverse extension occurring in the original
`GlobalCoordinates` conclusion. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

/-- The zero-dimensional case is excluded by the original connected,
noncompact manifold assumptions. -/
theorem dimension_pos {n : ℕ} (M : ComplexManifold n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  letI : DiscreteTopology (ComplexVector 0) := inferInstance
  letI : DiscreteTopology M.Carrier :=
    ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := subsingleton_of_preconnected_totallyDisconnected
  exact noncompact_univ M.Carrier isCompact_univ

theorem inverse_contMDiff_omega {n : ℕ} {M : ComplexManifold n}
    {s : Set (ComplexVector n)} (hs : IsOpen s) {g : ComplexVector n → M.Carrier}
    (hg : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ g s) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ω g s := by
  letI : IsManifold (ComplexModel n) ω (ComplexVector n) := instIsManifoldModelSpace
  exact U02AnalyticAux.contMDiffOn_omega_of_complex_infty
    (E := ComplexVector n) (F := ComplexVector n) (M := ComplexVector n) (N := M.Carrier) hs hg

/-- The inverse on the range is precisely the original inverse extension. -/
def coordinatesToOpen {n : ℕ} {X : KahlerManifold n} {o : Pt X} {ρ : STF X}
    {f : ℝ → Pt X → ComplexVector n} {tk : ℕ → ℝ}
    {H G Ginv : ℕ → PolyMap n} {sigma gamma : ℝ}
    {psi : Pt X → ComplexVector n} {inverse : ComplexVector n → Pt X}
    (hc : GlobalCoordinates X o ρ f tk H G Ginv sigma gamma psi inverse) :
    Uniformization.OpenCoordinateData n X.manifold where
  dimension_pos := dimension_pos X.manifold
  map := psi
  injective := hc.2.2.1
  inverse := fun z => inverse z.1
  left_inverse := hc.2.2.2.2.2.2.1
  right_inverse := by
    rintro ⟨z, x, rfl⟩
    change psi (inverse (psi x)) = psi x
    rw [hc.2.2.2.2.2.2.1 x]
  image_open := hc.2.2.2.2.1
  map_holomorphic := by
    refine ⟨U02AnalyticAux.contMDiff_omega_of_complex_infty hc.2.1, ?_⟩
    intro x a v
    change mfderiv (ComplexModel n) (ComplexModel n) psi x (a • v) =
      a • mfderiv (ComplexModel n) (ComplexModel n) psi x v
    exact map_smul _ a v
  inverse_extension := inverse
  inverse_contMDiffOn := inverse_contMDiff_omega hc.2.2.2.2.1 hc.2.2.2.2.2.1
  inverse_complex_linear_on := fun _ _ a v => map_smul _ a v
  inverse_extension_on_image := fun _ => rfl

@[simp] theorem coordinatesToOpen_map {n : ℕ} {X : KahlerManifold n}
    {o : Pt X} {ρ : STF X} {f : ℝ → Pt X → ComplexVector n} {tk : ℕ → ℝ}
    {H G Ginv : ℕ → PolyMap n} {sigma gamma : ℝ}
    {psi : Pt X → ComplexVector n} {inverse : ComplexVector n → Pt X}
    (hc : GlobalCoordinates X o ρ f tk H G Ginv sigma gamma psi inverse) :
    (coordinatesToOpen hc).map = psi := rfl

@[simp] theorem coordinatesToOpen_inverse_extension {n : ℕ} {X : KahlerManifold n}
    {o : Pt X} {ρ : STF X} {f : ℝ → Pt X → ComplexVector n} {tk : ℕ → ℝ}
    {H G Ginv : ℕ → PolyMap n} {sigma gamma : ℝ}
    {psi : Pt X → ComplexVector n} {inverse : ComplexVector n → Pt X}
    (hc : GlobalCoordinates X o ρ f tk H G Ginv sigma gamma psi inverse) :
    (coordinatesToOpen hc).inverse_extension = inverse := rfl

/-- Image estimates are transported to the range of the very same map,
without an independent image, clock, or polynomial sequence. -/
theorem imageDynamics_of_coordinates {n : ℕ} {X : KahlerManifold n}
    {o : Pt X} {ρ : STF X} {f : ℝ → Pt X → ComplexVector n} {tk : ℕ → ℝ}
    {H G Ginv : ℕ → PolyMap n} {sigma gamma : ℝ}
    {psi : Pt X → ComplexVector n} {inverse : ComplexVector n → Pt X}
    (hc : GlobalCoordinates X o ρ f tk H G Ginv sigma gamma psi inverse)
    (hs : Tendsto (fun k => ρ o (tk k)) atTop atTop)
    (hgamma : 0 < gamma) (hgap : gamma < sigma / 2)
    (hauto : ∀ k, IsPolyAutomorphism (forwardComp G k) (backwardComp Ginv k)) :
    ImageDynamics (coordinatesToOpen hc) G Ginv (fun k => ρ o (tk k)) sigma gamma := by
  refine ⟨?_, hs, hgamma, hgap, hauto, hc.2.2.2.2.2.2.2.1,
    hc.2.2.2.2.2.2.2.2⟩
  exact ⟨o, hc.2.2.2.1⟩

end Yau.NodeProofs.U02Proof

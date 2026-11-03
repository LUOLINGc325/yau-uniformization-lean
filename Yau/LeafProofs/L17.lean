import Yau.LeafProofs.L17BootstrapOriginalData
import Yau.LeafProofs.L17BootstrapLocalBranches
import Yau.LeafProofs.L17BootstrapProfilesFromBranches
import Yau.LeafProofs.L17BootstrapOriginalFlowBinding

noncomputable section
open Set Metric
open scoped Classical Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs
open L17Aux L17HolderAux L17SchauderAux L17ParabolicOperatorAux
open L17BootstrapOriginalDataAux L17BootstrapLocalBranchesAux
open L17BootstrapProfilesFromBranchesAux L17BootstrapOriginalFlowBindingAux

/-- The original complete Hermitian short-time potential flow, on the original
closed time interval with comparison constant two. -/
theorem L17 : LeafObligations.L17 := by
  intro n M g hg _hComplete hBG
  obtain ⟨P,N,Ccut,hCcut,hN,hCut,hr,h2rho,T,hT,hTime,hBase⟩ :=
    exists_original_bootstrap_data g hg hBG
  obtain ⟨Ja,Jb,hJa,hJb,ua,ub,huaEq,hubEq,hFun,huaZ,hubZ,huaSmall,hubSmall,B0,hB0⟩ := hBase
  have hBranches := exists_actual_local_shift_branches hg N Ccut hCcut hN h2rho hCut hTime hr
    Jb hJb ua ub hFun hubZ hubSmall hubEq B0 hB0
  have hSmooth := potentialFlow_smooth_of_actual_shift_branches P T hT hg hTime hr
    Jb hJb ub hubZ hubSmall hubEq hBranches
  have hConditions := potential_flow_original_conditions P T (1/4) hT hTime
    (by norm_num) (by norm_num) hr hg Jb hJb ub hubZ hubSmall hubEq hSmooth.1 hSmooth.2
  exact ⟨T,2,hT,by norm_num,potentialFlowField hg ub hubSmall,potentialFunction ub,hConditions⟩

end Yau.LeafProofs

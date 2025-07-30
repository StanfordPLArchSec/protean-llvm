#pragma once

#include <unordered_map>
#include <unordered_set>
#include <set>

#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/LivePhysRegs.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "PTeX/PublicPhysRegs.h"
#include "PTeX/PTeXInfo.h"

namespace llvm::X86 {

// TODO: Remove.
inline bool regAlwaysPublic(Register Reg, const TargetRegisterInfo &TRI) {
  return PublicPhysRegs::regAlwaysPublic(Reg, TRI);
}


class PTeXAnalysis : public PTeXInfo {
public:
  MachineFunctionPass &Pass;
  
  PTeXAnalysis(MachineFunction &MF, MachineFunctionPass &Pass): PTeXInfo(MF), Pass(Pass) {}

  void run();
  void dump() const { print(errs()); }

  MachineBasicBlock *splitCriticalEdge(MachineBasicBlock *Src, MachineBasicBlock *Dest);

protected:
  // Initialization functions.
  void init();
  void initTransmittedUses(MachineInstr &MI);
  void initPointerLoadsOrStores(MachineInstr &MI);
  void initAlwaysPublicRegs(MachineInstr &MI);
  void initFrameSetupAndDestroy(MachineInstr &MI);
  void initPointerCallArgs(MachineInstr &MI);
  void initPointerTypes(MachineInstr &MI);
  void initPointerReturnValue(MachineInstr &MI);
  void initPublicInstr(MachineInstr &MI);
  void initGOTLoads(MachineInstr &MI);
  void initMachineMemOperands(MachineInstr &MI);
  void initAnnotatedPublicAccesses(MachineInstr &MI);

  bool forward();
  bool backward();
  bool fixup();
  bool branch();

  void markOpPublic(MachineOperand &MO);
  void markAllOpsPublic(MachineInstr &MI);

  template <class BackwardAnalysis>
  bool runBackward();
};

}
